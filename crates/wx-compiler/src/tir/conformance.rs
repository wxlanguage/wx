//! Trait-impl conformance: whether `impl Tr for X` keeps the contract `Tr`
//! states for `X`. It is one check per impl, run after the impl's other
//! declaration checks once every signature exists (`check_declarations`), so everything an impl owes its trait is decided and
//! reported in one place:
//! - every member the impl writes is one the trait declares, of the same
//!   kind, and every declaration without a default is provided;
//! - a function's signature is the declaration's read with `Self` as the
//!   target: the same number of own type parameters and parameters, the same
//!   parameter names, the same types; a constant has the declaration's type;
//! - the target implements the trait's supertraits, with their bindings
//!   (`Self`'s clauses in the trait's frame, proved for the target);
//! - every associated type's value (the impl's own, or the default it
//!   inherits) satisfies the bounds the trait declares for it.
//!
//! Types are compared the way every equality in the checker is: the
//! declaration's type is substituted into the impl's terms (`Self` is the
//! target, the declaration's own parameters are the function's), both are
//! normalized with every fact, and the interned results are compared. Only a
//! mismatch is walked, to point at where the two differ.
//!
//! An impl function's own type parameters may assume no more than the
//! declaration's do (rustc's E0276): a caller through the trait proves only
//! the trait's bounds. The function is read in the env such a caller sees
//! (`contract_env`, rustc's hybrid `ParamEnv` in `compare_impl_method`): the
//! impl's env around it, and the declaration's clauses about its own
//! parameters. Its own clauses are proved there, and its signature is
//! compared there.

use super::bounds::{
	AssumptionEnvIdx, BoundClauses, BoundId, Clause, EqualityClause,
	RepresentableClause, TraitClause,
};
use super::decls::{
	AstNodeRef, BindingKey, ConstIdx, DeclId, DeclKind, FunctionIdx, MemberIdx,
	MemberKind, Tier, TraitIdx, TraitImplIdx,
};
use super::members::TraitMemberSelection;
use super::obligations::BoundRequirements;
use super::resolutions::{Reference, Site};
use super::signatures::{Semantics, SemanticsBuilder};
use super::solver::{
	ImplMember, NormalizationDepth, RewriteFlags, SolverError, Subjects,
	UnsatisfiedClause,
};
use super::types::{
	GenericEnvIdx, GenericEnvOwner, Substitution, Type, TypeIndex,
};
use crate::ast::{self, Spanned, StringInterner};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::vfs::FileId;
use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

impl Semantics {
	/// Whether the impl provides `declaration`: selection finds a member of
	/// its kind under its name. One of another kind is reported as such, and
	/// provides nothing.
	fn provides(
		&self,
		impl_index: TraitImplIdx,
		declaration: MemberKind,
	) -> bool {
		matches!(
			self.decls.select_trait_member(impl_index, declaration),
			TraitMemberSelection::Impl(_)
		)
	}

	/// The env a caller through the trait sees `function` in: the impl's
	/// env around it, and what the clauses the declaration itself states
	/// mean with `Self` as `target` and the declaration's parameters as the
	/// function's, by position (`normalize_clauses`, as the function's own
	/// `Self` entry is read). It exists for the check alone; its index is
	/// new, so its cache entries alias no declaration's. A function whose
	/// declaration states nothing is read in its impl's.
	fn contract_env(
		&mut self,
		strings: &StringInterner,
		declaration: FunctionIdx,
		function: FunctionIdx,
		target: TypeIndex,
	) -> Result<AssumptionEnvIdx, SolverError> {
		let env = self.functions[usize::from(function)].type_params;
		let impl_env = self.impl_env(function);
		let declaration_env =
			self.functions[usize::from(declaration)].type_params;
		let requirements = self.own_requirements(declaration_env);
		if requirements.is_empty() {
			return Ok(impl_env);
		}
		let arguments: Box<[TypeIndex]> = std::iter::once(target)
			.chain(self.own_params(env).iter().copied())
			.collect();
		let clauses =
			self.instantiate_clauses(requirements, declaration_env, &arguments);
		let (assumed, _) =
			self.normalize_clauses(strings, impl_env, clauses)?;
		let contract = self.assumption_envs.push(impl_env, None);
		*self.assumption_envs.clauses_mut(contract) = assumed;
		Ok(contract)
	}

	/// `clauses`, written in `env`'s chain, with that chain's parameters
	/// replaced by `arguments`: a new run, the written bounds they come from
	/// kept.
	fn instantiate_clauses(
		&mut self,
		clauses: BoundClauses,
		env: GenericEnvIdx,
		arguments: &[TypeIndex],
	) -> BoundClauses {
		let Some(range) = clauses.final_range() else {
			unreachable!("every signature exists when declarations are checked")
		};
		let substitution = Substitution {
			envs: &self.generic_envs,
			env,
			args: arguments,
		};
		let instantiated: Vec<Clause> = self
			.clauses
			.get(range)
			.iter()
			.map(|clause| match *clause {
				Clause::Trait(clause) => Clause::Trait(TraitClause {
					subject: self
						.types
						.substitute(clause.subject, substitution),
					..clause
				}),
				Clause::Equality(clause) => Clause::Equality(EqualityClause {
					projection: self
						.types
						.substitute(clause.projection, substitution),
					value: self.types.substitute(clause.value, substitution),
					..clause
				}),
				Clause::Representable(clause) => {
					Clause::Representable(RepresentableClause {
						subject: self
							.types
							.substitute(clause.subject, substitution),
						ty: self.types.substitute(clause.ty, substitution),
						..clause
					})
				}
			})
			.collect();
		BoundClauses::Final(self.clauses.push(&instantiated))
	}

	/// Proves the clauses `function`'s own env states in `contract`, where
	/// they assume only the declaration's: an impl may require less than its
	/// trait, never more. Each written bound that does not follow is reported
	/// once, by the first of its clauses that fails (`T: Ord` over a trait's
	/// `T: PartialEq` is one report, not one per supertrait). Answers whether
	/// every bound follows.
	fn check_own_bounds(
		&mut self,
		strings: &StringInterner,
		trait_index: TraitIdx,
		(declaration, function): (FunctionIdx, FunctionIdx),
		contract: AssumptionEnvIdx,
	) -> Result<bool, SolverError> {
		let env = self.functions[usize::from(function)].type_params;
		let requirements = self.own_requirements(env);
		if requirements.is_empty() {
			return Ok(true);
		}
		// Only what the function assumes is compared: a clause about a type
		// that is not abstract holds or not of its own, and is checked where
		// it is written (`normalize_self_entry`). Each is read where the
		// function is written, not under the contract's assumptions.
		let impl_env = self.impl_env(function);
		let (clauses, _) =
			self.normalize_clauses(strings, impl_env, requirements)?;
		let arguments: Box<[TypeIndex]> =
			self.generic_envs.identity_args(env).into();
		let mut failures = Vec::new();
		let holds = self.satisfies_clauses(
			strings,
			contract,
			clauses,
			Subjects::All,
			(env, &arguments),
			Some(&mut failures),
			None,
		)?;
		if !holds {
			// The written bound each failure came from.
			let mut reported = Vec::new();
			for failure in failures {
				let origin = match failure {
					UnsatisfiedClause::Trait {
						trait_index,
						source,
						..
					} => self
						.clauses
						.traits(clauses.range())
						.find(|clause| {
							clause.trait_index == trait_index
								&& clause.source == source
						})
						.map(|clause| clause.origin),
					UnsatisfiedClause::Equality { source, .. } => self
						.clauses
						.equalities(clauses.range())
						.find(|clause| clause.source == source)
						.map(|clause| clause.origin),
					UnsatisfiedClause::Representable { source, .. } => self
						.clauses
						.representable(clauses.range())
						.find(|clause| clause.source == source)
						.map(|clause| clause.origin),
				}
				.expect("a failure is one of the proved clauses");
				if reported.contains(&origin) {
					continue;
				}
				reported.push(origin);
				self.report_stricter_bound(
					strings,
					trait_index,
					(declaration, function),
					origin,
					&failure,
				);
			}
		}
		Ok(holds)
	}

	/// A function's own type parameters, given its frame: none when that is
	/// the trait's or impl's around it, which a function without its own
	/// parameters is read in.
	/// The env of the impl `function` is written in.
	fn impl_env(&self, function: FunctionIdx) -> AssumptionEnvIdx {
		let env = self.functions[usize::from(function)].type_params;
		let impl_frame = match self.generic_envs.owner(env) {
			GenericEnvOwner::Function(_) => self
				.generic_envs
				.parent(env)
				.expect("a function's own frame has its impl's around it"),
			_ => env,
		};
		self.assumption_envs.of_frame(impl_frame)
	}

	/// What `frame`'s function itself states: nothing when it has no frame
	/// of its own and `frame` is its impl's or its trait's.
	fn own_requirements(&self, frame: GenericEnvIdx) -> BoundClauses {
		match self.generic_envs.owner(frame) {
			GenericEnvOwner::Function(_) => {
				self.assumption_envs.requirements(frame)
			}
			_ => BoundClauses::NONE,
		}
	}

	fn own_params(&self, frame: GenericEnvIdx) -> &[TypeIndex] {
		match self.generic_envs.owner(frame) {
			GenericEnvOwner::Function(_) => {
				self.generic_envs.param_types(frame)
			}
			_ => &[],
		}
	}

	fn trait_name<'s>(
		&self,
		strings: &'s StringInterner,
		trait_index: TraitIdx,
	) -> &'s str {
		let name = self.decls.traits[usize::from(trait_index)].name.inner;
		strings.resolve(name).unwrap()
	}

	fn expected_found(
		&self,
		strings: &StringInterner,
		expected: TypeIndex,
		found: TypeIndex,
	) -> String {
		let formatter = self.type_formatter(strings);
		format!(
			"expected `{}`, found `{}`",
			formatter.display_type(expected),
			formatter.display_type(found),
		)
	}

	/// The head of every function signature mismatch: E2080, naming the
	/// function and its trait.
	fn signature_mismatch(
		&self,
		strings: &StringInterner,
		trait_index: TraitIdx,
		member: MemberKind,
		function: FunctionIdx,
	) -> Diagnostic<FileId> {
		let name = self.decls.functions[usize::from(function)].name.inner;
		Diagnostic::error()
			.with_code(DiagnosticCode::TraitImplSignatureMismatch.code())
			.with_message(format!(
				"{} `{}` has an incompatible signature for trait `{}`",
				member_noun(member),
				strings.resolve(name).unwrap(),
				self.trait_name(strings, trait_index),
			))
	}

	fn report_count_mismatch(
		&mut self,
		strings: &StringInterner,
		trait_index: TraitIdx,
		member: MemberKind,
		(declaration, function): (FunctionIdx, FunctionIdx),
		what: &str,
		(expected, found): (usize, usize),
	) {
		let plural = |count: usize| if count == 1 { "" } else { "s" };
		let (expected_decl, decl) = (
			&self.decls.functions[usize::from(declaration)],
			&self.decls.functions[usize::from(function)],
		);
		let diagnostic = self
			.signature_mismatch(strings, trait_index, member, function)
			.with_label(
				SourceSpan::new(decl.file_id, decl.name.span)
					.primary_label()
					.with_message(format!(
						"expected {expected} {what}{}, found {found}",
						plural(expected),
					)),
			)
			.with_label(
				SourceSpan::new(expected_decl.file_id, expected_decl.name.span)
					.secondary_label()
					.with_message(format!(
						"the trait declares {expected} {what}{}",
						plural(expected),
					)),
			);
		self.diagnostics.push(diagnostic);
	}

	/// rustc's E0276: a bound the impl writes on its function's own type
	/// parameter that the trait's declaration does not imply. It is pointed
	/// at as written; the clause that fails is what the label names.
	fn report_stricter_bound(
		&mut self,
		strings: &StringInterner,
		trait_index: TraitIdx,
		(declaration, function): (FunctionIdx, FunctionIdx),
		origin: BoundId,
		failure: &UnsatisfiedClause,
	) {
		let read = match *failure {
			UnsatisfiedClause::Representable {
				subject, constant, ..
			} => Some(self.types.intern_const(constant, &[subject])),
			_ => None,
		};
		let formatter = self.type_formatter(strings);
		let requirement = match *failure {
			UnsatisfiedClause::Trait {
				subject,
				trait_index,
				..
			} => {
				let name =
					self.decls.traits[usize::from(trait_index)].name.inner;
				format!(
					"{}: {}",
					formatter.display_type(subject),
					strings.resolve(name).unwrap(),
				)
			}
			UnsatisfiedClause::Equality {
				projection,
				required,
				..
			} => format!(
				"{} == {}",
				formatter.display_type(projection),
				formatter.display_type(required),
			),
			UnsatisfiedClause::Representable { ty, .. } => format!(
				"{} is representable as {}",
				formatter.display_type(
					read.expect("a representability clause reads its constant")
				),
				formatter.display_type(ty),
			),
		};
		let expected_decl = &self.decls.functions[usize::from(declaration)];
		let name = self.decls.functions[usize::from(function)].name.inner;
		let diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::ImplStricterThanTrait.code())
			.with_message(format!(
				"impl has stricter requirements than trait `{}`",
				self.trait_name(strings, trait_index),
			))
			.with_label(self.bounds.span(origin).primary_label().with_message(
				format!("impl has extra requirement `{requirement}`"),
			))
			.with_label(
				SourceSpan::new(expected_decl.file_id, expected_decl.name.span)
					.secondary_label()
					.with_message(format!(
						"definition of `{}` from trait",
						strings.resolve(name).unwrap(),
					)),
			)
			.with_note(
				"a caller through the trait proves only the trait's bounds, so \
				 an impl may require less than its trait, never more",
			);
		self.diagnostics.push(diagnostic);
	}

	fn report_not_a_member(
		&mut self,
		strings: &StringInterner,
		trait_index: TraitIdx,
		member: MemberKind,
		name: Spanned<SymbolU32>,
		at_member: SourceSpan,
	) {
		let trait_name = self.trait_name(strings, trait_index);
		let diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::NotATraitMember.code())
			.with_message(format!(
				"{} `{}` is not a member of trait `{trait_name}`",
				member_noun(member),
				strings.resolve(name.inner).unwrap(),
			))
			.with_label(
				at_member
					.primary_label()
					.with_message(format!("not a member of `{trait_name}`")),
			);
		self.diagnostics.push(diagnostic);
	}

	fn report_kind_mismatch(
		&mut self,
		strings: &StringInterner,
		trait_index: TraitIdx,
		declaration: MemberKind,
		member: MemberKind,
		at_member: SourceSpan,
	) {
		let name = self.decls.name(declaration.decl_id());
		let trait_decl = &self.decls.traits[usize::from(trait_index)];
		let diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::TraitImplItemKindMismatch.code())
			.with_message(format!(
				"`{}` is {} {}, but trait `{}` declares {} {}",
				strings.resolve(name.inner).unwrap(),
				article(member),
				member_noun(member),
				self.trait_name(strings, trait_index),
				article(declaration),
				member_noun(declaration),
			))
			.with_label(
				at_member
					.primary_label()
					.with_message("does not match the trait"),
			)
			.with_label(
				SourceSpan::new(trait_decl.file_id, name.span)
					.secondary_label()
					.with_message(format!(
						"declared as {} {} here",
						article(declaration),
						member_noun(declaration),
					)),
			);
		self.diagnostics.push(diagnostic);
	}

	fn report_missing(
		&mut self,
		strings: &StringInterner,
		trait_index: TraitIdx,
		missing: &[Spanned<SymbolU32>],
		at_target: SourceSpan,
	) {
		let names = missing
			.iter()
			.map(|name| format!("`{}`", strings.resolve(name.inner).unwrap()))
			.collect::<Vec<_>>()
			.join(", ");
		let trait_file = self.decls.traits[usize::from(trait_index)].file_id;
		let mut diagnostic =
			Diagnostic::error()
				.with_code(DiagnosticCode::IncompleteTraitImpl.code())
				.with_message(format!(
					"not all members of trait `{}` are implemented",
					self.trait_name(strings, trait_index),
				))
				.with_label(at_target.primary_label().with_message(format!(
					"missing {names} in implementation"
				)));
		for name in missing {
			diagnostic = diagnostic.with_label(
				SourceSpan::new(trait_file, name.span)
					.secondary_label()
					.with_message(format!(
						"`{}` from trait",
						strings.resolve(name.inner).unwrap(),
					)),
			);
		}
		self.diagnostics.push(diagnostic);
	}

	/// Reports two unequal types, each pointed at where it is written: the
	/// walk finds the innermost part they differ in, and each side's syntax is
	/// followed along that path as far as it spells the type out. The impl's
	/// side is labelled with the parts that differ at the depth its syntax
	/// reaches; a note names the parts further in, when its syntax stops short
	/// (an alias, a projection, `Self`).
	fn report_type_mismatch<'ast>(
		&mut self,
		strings: &StringInterner,
		head: Diagnostic<FileId>,
		(expected_file, expected_written): (FileId, WrittenType<'ast>),
		(found_file, found_written): (FileId, WrittenType<'ast>),
		(expected, found): (TypeIndex, TypeIndex),
	) {
		let mut path = Vec::new();
		self.innermost_difference(expected, found, &mut path);
		let (at_expected, _) =
			self.written_part(expected_file, expected_written, &path);
		let (at_found, depth) =
			self.written_part(found_file, found_written, &path);
		let (label_expected, label_found) = match depth {
			0 => (expected, found),
			depth => (path[depth - 1].1, path[depth - 1].2),
		};
		let mut diagnostic = head
			.with_label(
				SourceSpan::new(found_file, at_found)
					.primary_label()
					.with_message(self.expected_found(
						strings,
						label_expected,
						label_found,
					)),
			)
			.with_label(
				SourceSpan::new(expected_file, at_expected)
					.secondary_label()
					.with_message("type in trait"),
			);
		if let Some(&(_, inner_expected, inner_found)) = path.last()
			&& depth < path.len()
		{
			let place = path[depth..]
				.iter()
				.map(|&(step, ..)| step.describe())
				.collect::<Vec<_>>()
				.join(" → ");
			diagnostic = diagnostic.with_note(format!(
				"they differ in {place}: {}",
				self.expected_found(strings, inner_expected, inner_found),
			));
		}
		self.diagnostics.push(diagnostic);
	}

	/// How far `written` spells out `path`: the span of the deepest part it
	/// reaches, and the number of steps taken to get there. Syntax spells a
	/// type's parts in a tuple, a pointer, slice or array, a function type,
	/// and a path to a struct or a function with its arguments. It stops at
	/// anything whose meaning is not spelled where it is written: an alias,
	/// a parameter, `Self`, a projection.
	fn written_part<'ast>(
		&self,
		file_id: FileId,
		written: WrittenType<'ast>,
		path: &[(TypePathStep, TypeIndex, TypeIndex)],
	) -> (TextSpan, usize) {
		let mut current = match written {
			WrittenType::Written(written) => written,
			WrittenType::Implied(span) => return (span, 0),
		};
		let mut taken = 0;
		loop {
			// A tuple of one is its element.
			while let ast::TypeExpression::Tuple { elements } = &current.inner
				&& let [element] = &elements[..]
			{
				current = &element.inner;
			}
			let Some(&(step, ..)) = path.get(taken) else {
				return (current.span, taken);
			};
			let next = match (&current.inner, step) {
				(
					ast::TypeExpression::Tuple { elements },
					TypePathStep::TupleElement(index),
				) => elements.get(index).map(|element| &element.inner),
				(
					ast::TypeExpression::Pointer { inner, .. },
					TypePathStep::Pointee,
				)
				| (
					ast::TypeExpression::Slice { inner }
					| ast::TypeExpression::Array { inner, .. },
					TypePathStep::Element,
				) => Some(&**inner),
				(
					ast::TypeExpression::Array { length, .. },
					TypePathStep::Length,
				) => return (length.span, taken + 1),
				(
					ast::TypeExpression::Pointer { memory, .. },
					TypePathStep::Memory,
				) => {
					if let Some([first, .., last] | [first @ last]) =
						memory.as_deref()
					{
						return (
							TextSpan::new(
								first.ident.span.start,
								last.ident.span.end,
							),
							taken + 1,
						);
					}
					None
				}
				(
					ast::TypeExpression::Function { result, .. },
					TypePathStep::Result,
				) => result.as_deref(),
				// The parameter list is sugar for one parameter: a list of
				// several is that tuple, whose elements are its entries.
				(
					ast::TypeExpression::Function { params, .. },
					TypePathStep::Parameter,
				) => match &params[..] {
					[param] => Some(&*param.inner.inner.ty),
					params => match path.get(taken + 1) {
						Some(&(TypePathStep::TupleElement(index), ..))
							if index < params.len() =>
						{
							taken += 1;
							Some(&*params[index].inner.inner.ty)
						}
						_ => None,
					},
				},
				(
					ast::TypeExpression::Path(segments),
					TypePathStep::TypeArgument(index),
				) => {
					let last = segments.last().expect("a path is never empty");
					let site =
						Site::Type(SourceSpan::new(file_id, last.ident.span));
					let spells_its_arguments = self
						.resolutions
						.get(site)
						.and_then(|reference| match reference {
							Reference::Item { item, .. } => Some(item),
							_ => None,
						})
						.is_some_and(|key| {
							matches!(
								key.symbol_kind(&self.decls),
								DeclKind::Struct(_) | DeclKind::Function(_)
							)
						});
					match last.type_args.get(index) {
						Some(ast::TypeArgument::Type(argument))
							if spells_its_arguments =>
						{
							Some(argument)
						}
						_ => None,
					}
				}
				_ => None,
			};
			let Some(next) = next else {
				return (current.span, taken);
			};
			current = next;
			taken += 1;
		}
	}

	/// The path from two unequal types to the innermost part they differ in,
	/// each step with the parts it reaches. It descends while exactly one part
	/// differs; parts that differ in several places, or in a way that is not a
	/// part (two structs, two ownerships), are the difference themselves.
	fn innermost_difference(
		&self,
		expected: TypeIndex,
		found: TypeIndex,
		path: &mut Vec<(TypePathStep, TypeIndex, TypeIndex)>,
	) {
		let types = &self.types;
		let lists = |a, b, step: fn(usize) -> TypePathStep| {
			let (a, b) = (types.list(a), types.list(b));
			if a.len() != b.len() {
				return Vec::new();
			}
			a.iter()
				.zip(b)
				.enumerate()
				.map(|(index, (&a, &b))| (step(index), a, b))
				.collect()
		};
		let parts: Vec<(TypePathStep, TypeIndex, TypeIndex)> =
			match (types.resolve(expected), types.resolve(found)) {
				(
					&Type::Tuple { elements: a },
					&Type::Tuple { elements: b },
				) => lists(a, b, TypePathStep::TupleElement),
				(
					&Type::Struct {
						struct_index: a,
						type_args: a_args,
					},
					&Type::Struct {
						struct_index: b,
						type_args: b_args,
					},
				) if a == b => lists(a_args, b_args, TypePathStep::TypeArgument),
				(
					&Type::Function {
						func_index: a,
						type_args: a_args,
					},
					&Type::Function {
						func_index: b,
						type_args: b_args,
					},
				) if a == b => lists(a_args, b_args, TypePathStep::TypeArgument),
				(
					&Type::Const {
						constant: a,
						type_args: a_args,
					},
					&Type::Const {
						constant: b,
						type_args: b_args,
					},
				) if a == b => lists(a_args, b_args, TypePathStep::TypeArgument),
				(
					&Type::TypedFuncref {
						param: a_param,
						result: a_result,
					},
					&Type::TypedFuncref {
						param: b_param,
						result: b_result,
					},
				) => vec![
					(TypePathStep::Parameter, a_param, b_param),
					(TypePathStep::Result, a_result, b_result),
				],
				(
					&Type::Pointer {
						to: a_to,
						memory: a_memory,
						ownership: a,
					},
					&Type::Pointer {
						to: b_to,
						memory: b_memory,
						ownership: b,
					},
				) if a == b => vec![
					(TypePathStep::Pointee, a_to, b_to),
					(TypePathStep::Memory, a_memory, b_memory),
				],
				(
					&Type::Array {
						of: a_of,
						length: a_length,
					},
					&Type::Array {
						of: b_of,
						length: b_length,
					},
				) => vec![
					(TypePathStep::Element, a_of, b_of),
					(TypePathStep::Length, a_length, b_length),
				],
				(&Type::Slice { of: a_of }, &Type::Slice { of: b_of }) => {
					vec![(TypePathStep::Element, a_of, b_of)]
				}
				(
					&Type::TypeProjection {
						trait_index: a_trait,
						assoc_type_index: a,
						base: a_base,
					},
					&Type::TypeProjection {
						trait_index: b_trait,
						assoc_type_index: b,
						base: b_base,
					},
				) if a_trait == b_trait && a == b => {
					vec![(TypePathStep::ProjectionBase, a_base, b_base)]
				}
				_ => Vec::new(),
			};
		let mut differing = parts.into_iter().filter(|(_, a, b)| a != b);
		if let (Some(part @ (_, expected, found)), None) =
			(differing.next(), differing.next())
		{
			path.push(part);
			self.innermost_difference(expected, found, path);
		}
	}

	/// Reports a check that could not finish (a cycle, an exhausted budget)
	/// at `reference`. A poisoned one was reported where it failed; only
	/// "not decided yet" is passed on.
	fn report_unfinished(
		&mut self,
		strings: &StringInterner,
		result: Result<(), SolverError>,
		reference: SourceSpan,
	) -> Result<(), SolverError> {
		match result {
			Ok(()) | Err(SolverError::Poisoned) => Ok(()),
			Err(SolverError::Cycle(cycle)) => {
				let diagnostic =
					self.cycle_diagnostic(strings, &cycle, reference);
				self.diagnostics.push(diagnostic);
				Ok(())
			}
			Err(SolverError::Overflow) => {
				self.diagnostics.push(self.overflow_diagnostic(reference));
				Ok(())
			}
			Err(SolverError::Pending) => Err(SolverError::Pending),
		}
	}
}

/// Where a compared type is written: its syntax, or, for a type left out
/// (a function's `()` result), the span that stands for it.
#[derive(Clone, Copy)]
enum WrittenType<'ast> {
	Written(&'ast Spanned<ast::TypeExpression>),
	Implied(TextSpan),
}

/// One step from a type into one of its parts, for saying where two types
/// differ.
#[derive(Clone, Copy)]
enum TypePathStep {
	TupleElement(usize),
	TypeArgument(usize),
	Parameter,
	Result,
	Pointee,
	Element,
	Length,
	Memory,
	ProjectionBase,
}

impl TypePathStep {
	fn describe(self) -> String {
		match self {
			Self::TupleElement(index) => format!("tuple element {}", index + 1),
			Self::TypeArgument(index) => format!("type argument {}", index + 1),
			Self::Parameter => "the parameter".to_owned(),
			Self::Result => "the result".to_owned(),
			Self::Pointee => "the pointee".to_owned(),
			Self::Element => "the element".to_owned(),
			Self::Length => "the length".to_owned(),
			Self::Memory => "the memory".to_owned(),
			Self::ProjectionBase => "the projection's base".to_owned(),
		}
	}
}

fn member_noun(member: MemberKind) -> &'static str {
	match member {
		MemberKind::Function(_) => "function",
		MemberKind::Method(_) => "method",
		MemberKind::Constant(_) => "constant",
		MemberKind::AssociatedType(_) => "associated type",
	}
}

fn article(member: MemberKind) -> &'static str {
	match member {
		MemberKind::AssociatedType(_) => "an",
		_ => "a",
	}
}

impl<'ast> SemanticsBuilder<'ast> {
	/// Checks what `impl_index` owes its trait. Each part is reported on its
	/// own, so one failure does not hide the next; only "not decided yet"
	/// is returned.
	pub(super) fn check_conformance(
		&mut self,
		sema: &mut Semantics,
		impl_index: TraitImplIdx,
	) -> Result<(), SolverError> {
		// An impl of an unresolved trait reported that already.
		let Some(trait_decl) =
			sema.impl_dispatch.trait_header(impl_index).trait_decl
		else {
			return Ok(());
		};
		let trait_index = trait_decl.inner;
		let header = sema.trait_impls[usize::from(impl_index)]
			.as_ref()
			.expect("every signature exists when declarations are checked");
		let (scope, target) = (header.type_params, header.target);
		let file_id = sema.decls.trait_impls[usize::from(impl_index)].file_id;
		let at_target = SourceSpan::new(file_id, target.span);
		let owner = GenericEnvOwner::Trait(trait_index);

		self.check_members(
			sema,
			impl_index,
			trait_index,
			target.inner,
			at_target,
		)?;

		// The supertraits are the clauses on the trait's `Self`; the target
		// must satisfy them where the impl is written, with its parameters'
		// bounds assumed.
		let trait_env = sema.traits[usize::from(trait_index)].env;
		let args = sema.generic_args.push([(target.inner, target.span)]);
		let result = sema.check_bound_requirements(
			&self.strings,
			sema.assumption_envs.of_frame(scope),
			BoundRequirements::Frame {
				env: trait_env,
				args,
			},
			at_target,
			owner,
		);
		sema.report_unfinished(&self.strings, result, at_target)?;

		for member_index in
			0..sema.decls.traits[usize::from(trait_index)].members.len()
		{
			let declaration @ MemberKind::AssociatedType(declaration_index) =
				sema.decls.traits[usize::from(trait_index)].members
					[member_index]
					.kind
			else {
				continue;
			};
			// The value's own judgement (`CheckAssocValue`) reports a value
			// that has no meaning; one the impl omits with no default is
			// reported missing above.
			let value = match sema.assoc_value(
				&self.strings,
				ImplMember {
					impl_index,
					declaration: declaration_index,
				},
				None,
			) {
				Ok(value) => value,
				Err(SolverError::Pending) => return Err(SolverError::Pending),
				Err(_) => continue,
			};
			// A written value is pointed at; an inherited default is written
			// in the trait, so the impl's target stands for it.
			let reference =
				match sema.decls.select_trait_member(impl_index, declaration) {
					TraitMemberSelection::Impl(MemberKind::AssociatedType(
						provider,
					)) => {
						let AstNodeRef::TraitImplAssocType {
							item: ast::ImplItem::AssocType { ty, .. },
							..
						} = *self.ast_node(DeclId::AssocType(provider))
						else {
							unreachable!("a trait impl's associated type")
						};
						SourceSpan::new(
							sema.decls.assoc_types[usize::from(provider)]
								.file_id,
							ty.span,
						)
					}
					_ => at_target,
				};
			let result = sema.check_bound_requirements(
				&self.strings,
				sema.assumption_envs.of_frame(scope),
				BoundRequirements::AssociatedType {
					declaration: declaration_index,
					trait_index,
					receiver: target.inner,
					value,
				},
				reference,
				owner,
			);
			sema.report_unfinished(&self.strings, result, reference)?;
		}
		Ok(())
	}

	/// The impl's members against the trait's declarations, in the order the
	/// impl writes them, then the declarations it leaves out. Each side is a
	/// lookup in the other's bindings. A member is matched to the declaration
	/// of its name, of its own tier first: one of the other tier is the
	/// declaration it was meant to provide, of another kind. A declaration is
	/// missing when the impl does not provide it (`provides`) and it has no
	/// default.
	fn check_members(
		&mut self,
		sema: &mut Semantics,
		impl_index: TraitImplIdx,
		trait_index: TraitIdx,
		target: TypeIndex,
		at_target: SourceSpan,
	) -> Result<(), SolverError> {
		let impl_decl = &sema.decls.trait_impls[usize::from(impl_index)];
		let impl_file = impl_decl.file_id;
		for index in 0..impl_decl.members.len() {
			let impl_decl = &sema.decls.trait_impls[usize::from(impl_index)];
			let member = impl_decl.members[index].kind;
			let name = sema.decls.name(member.decl_id());
			// A second member of one name was reported as a duplicate.
			if impl_decl
				.bindings
				.get(&BindingKey::new(member.tier(), name.inner))
				!= Some(&MemberIdx::new(index as u32))
			{
				continue;
			}
			let at_member = SourceSpan::new(impl_file, name.span);
			let other_tier = match member.tier() {
				Tier::Type => Tier::Value,
				Tier::Value => Tier::Type,
			};
			let trait_decl = &sema.decls.traits[usize::from(trait_index)];
			let Some(declaration_index) =
				[member.tier(), other_tier].into_iter().find_map(|tier| {
					trait_decl
						.bindings
						.get(&BindingKey::new(tier, name.inner))
						.copied()
				})
			else {
				sema.report_not_a_member(
					&self.strings,
					trait_index,
					member,
					name,
					at_member,
				);
				continue;
			};
			let declaration =
				trait_decl.members[usize::from(declaration_index)].kind;
			match (declaration, member) {
				(
					MemberKind::Function(expected)
					| MemberKind::Method(expected),
					MemberKind::Function(found) | MemberKind::Method(found),
				) => {
					let result = self.compare_function(
						sema,
						trait_index,
						declaration,
						expected,
						found,
						target,
					);
					sema.report_unfinished(&self.strings, result, at_member)?;
				}
				(
					MemberKind::Constant(expected),
					MemberKind::Constant(found),
				) => {
					let result = self.compare_constant(
						sema,
						trait_index,
						expected,
						found,
						target,
					);
					sema.report_unfinished(&self.strings, result, at_member)?;
				}
				(
					MemberKind::AssociatedType(_),
					MemberKind::AssociatedType(_),
				) => {}
				_ => sema.report_kind_mismatch(
					&self.strings,
					trait_index,
					declaration,
					member,
					at_member,
				),
			}
		}

		let trait_decl = &sema.decls.traits[usize::from(trait_index)];
		let missing: Vec<Spanned<SymbolU32>> = trait_decl
			.members
			.iter()
			.filter(|member| {
				!sema.provides(impl_index, member.kind)
					&& !self.has_default(sema, member.kind)
			})
			.map(|member| sema.decls.name(member.kind.decl_id()))
			.collect();
		if !missing.is_empty() {
			sema.report_missing(
				&self.strings,
				trait_index,
				&missing,
				at_target,
			);
		}
		Ok(())
	}

	/// Whether the trait's declaration supplies what an impl omits.
	fn has_default(&self, sema: &Semantics, declaration: MemberKind) -> bool {
		match declaration {
			MemberKind::AssociatedType(index) => sema.assoc_types
				[usize::from(index)]
			.as_ref()
			.is_some_and(|signature| signature.value.is_some()),
			MemberKind::Function(index) | MemberKind::Method(index) => {
				matches!(
					*self.ast_node(DeclId::Function(index)),
					AstNodeRef::TraitFunction {
						item: ast::TraitItem::Function { body: Some(_), .. },
						..
					}
				)
			}
			MemberKind::Constant(index) => matches!(
				*self.ast_node(DeclId::Const(index)),
				AstNodeRef::TraitConst {
					item: ast::TraitItem::Const { value: Some(_), .. },
					..
				}
			),
		}
	}

	/// The impl's `function` against the trait's `declaration`, read in the
	/// env a caller through the trait sees (`contract_env`): `Self` is
	/// `target`, and the declaration's own type parameters are the
	/// function's, by position, assuming what the declaration's do. Reports
	/// the first difference: the number of own type parameters, a bound the
	/// declaration does not imply, the number of parameters, then each
	/// parameter's name and type in order, then the result.
	fn compare_function(
		&mut self,
		sema: &mut Semantics,
		trait_index: TraitIdx,
		member: MemberKind,
		declaration: FunctionIdx,
		function: FunctionIdx,
		target: TypeIndex,
	) -> Result<(), SolverError> {
		let declaration_env =
			sema.functions[usize::from(declaration)].type_params;
		let env = sema.functions[usize::from(function)].type_params;
		let (expected_own, own) = (
			sema.own_params(declaration_env).len(),
			sema.own_params(env).len(),
		);
		if expected_own != own {
			sema.report_count_mismatch(
				&self.strings,
				trait_index,
				member,
				(declaration, function),
				"type parameter",
				(expected_own, own),
			);
			return Ok(());
		}
		let contract =
			sema.contract_env(&self.strings, declaration, function, target)?;
		if !sema.check_own_bounds(
			&self.strings,
			trait_index,
			(declaration, function),
			contract,
		)? {
			return Ok(());
		}
		let (expected_signature, signature) = (
			&sema.functions[usize::from(declaration)],
			&sema.functions[usize::from(function)],
		);
		let (expected_params, expected_result) = (
			expected_signature.param_types,
			expected_signature.return_type,
		);
		let (found_params, found_result) =
			(signature.param_types, signature.return_type);
		let params = sema.types.list(found_params).len();
		let expected_count = sema.types.list(expected_params).len();
		if expected_count != params {
			sema.report_count_mismatch(
				&self.strings,
				trait_index,
				member,
				(declaration, function),
				"parameter",
				(expected_count, params),
			);
			return Ok(());
		}
		let arguments: Box<[TypeIndex]> = std::iter::once(target)
			.chain(sema.own_params(env).iter().copied())
			.collect();
		// The result is compared as one more position, after the parameters.
		for position in 0..=params {
			let (expected, found) = if position < params {
				(
					sema.types.list(expected_params)[position],
					sema.types.list(found_params)[position],
				)
			} else {
				(expected_result, found_result)
			};
			// A type that failed to lower was reported where it is written,
			// and the parameter is not understood well enough to compare,
			// its name included.
			if sema.types.has_error(expected) || sema.types.has_error(found) {
				continue;
			}
			if position < params {
				let expected_name = sema.decls.functions
					[usize::from(declaration)]
				.params[position];
				let name = sema.decls.functions[usize::from(function)].params
					[position];
				// Leaving the parameter unnamed only binds no local: the contract
				// is still the trait's, and so are the names calls use.
				if name.is_some()
					&& expected_name.map(|name| name.inner)
						!= name.map(|name| name.inner)
				{
					self.report_name_mismatch(
						sema,
						trait_index,
						member,
						(declaration, function),
						position,
						(expected_name, name),
					);
					return Ok(());
				}
			}
			let expected = sema.types.substitute(
				expected,
				Substitution {
					envs: &sema.generic_envs,
					env: declaration_env,
					args: &arguments,
				},
			);
			let expected = sema.normalize(
				&self.strings,
				contract,
				expected,
				NormalizationDepth::Deep,
				RewriteFlags::ALL,
			)?;
			let found = sema.normalize(
				&self.strings,
				contract,
				found,
				NormalizationDepth::Deep,
				RewriteFlags::ALL,
			)?;
			// Normalizing may still meet an error (a projection with no value),
			// which was reported where it belongs.
			if expected == found
				|| sema.types.has_error(expected)
				|| sema.types.has_error(found)
			{
				continue;
			}
			let (expected_syntax, syntax) = (
				self.function_syntax(declaration),
				self.function_syntax(function),
			);
			// A left-out result is `()`; its function's name stands for it.
			let written = |syntax: &'ast ast::FunctionSignature| {
				if position < params {
					WrittenType::Written(
						&syntax.params[position].inner.inner.ty,
					)
				} else {
					syntax.result.as_deref().map_or(
						WrittenType::Implied(syntax.name.span),
						WrittenType::Written,
					)
				}
			};
			let head = sema.signature_mismatch(
				&self.strings,
				trait_index,
				member,
				function,
			);
			sema.report_type_mismatch(
				&self.strings,
				head,
				(
					sema.decls.functions[usize::from(declaration)].file_id,
					written(expected_syntax),
				),
				(
					sema.decls.functions[usize::from(function)].file_id,
					written(syntax),
				),
				(expected, found),
			);
			return Ok(());
		}
		Ok(())
	}

	/// The impl's constant against the trait's `declaration`, with `Self` as
	/// `target`.
	fn compare_constant(
		&mut self,
		sema: &mut Semantics,
		trait_index: TraitIdx,
		declaration: ConstIdx,
		constant: ConstIdx,
		target: TypeIndex,
	) -> Result<(), SolverError> {
		let expected_signature = &sema.constants[usize::from(declaration)];
		let (expected, declaration_env) =
			(expected_signature.ty, expected_signature.env);
		let signature = &sema.constants[usize::from(constant)];
		let (found, env) = (signature.ty, signature.env);
		let expected = sema.types.substitute(
			expected,
			Substitution {
				envs: &sema.generic_envs,
				env: declaration_env,
				args: &[target],
			},
		);
		let expected = sema.normalize(
			&self.strings,
			sema.assumption_envs.of_frame(env),
			expected,
			NormalizationDepth::Deep,
			RewriteFlags::ALL,
		)?;
		let found = sema.normalize(
			&self.strings,
			sema.assumption_envs.of_frame(env),
			found,
			NormalizationDepth::Deep,
			RewriteFlags::ALL,
		)?;
		if expected == found
			|| sema.types.has_error(expected)
			|| sema.types.has_error(found)
		{
			return Ok(());
		}
		// A constant whose type is left out is reported and typed `ERROR`, so
		// both are written here.
		let AstNodeRef::TraitConst {
			item: ast::TraitItem::Const {
				ty: expected_ty, ..
			},
			..
		} = *self.ast_node(DeclId::Const(declaration))
		else {
			unreachable!("a trait's constant")
		};
		let AstNodeRef::TraitImplConstant {
			item: ast::ImplItem::Constant { ty: Some(ty), .. },
			..
		} = *self.ast_node(DeclId::Const(constant))
		else {
			unreachable!("a trait impl's constant with a written type")
		};
		let name = sema.decls.constants[usize::from(constant)].name.inner;
		let head = Diagnostic::error()
			.with_code(DiagnosticCode::TraitImplConstTypeMismatch.code())
			.with_message(format!(
				"constant `{}` has an incompatible type for trait `{}`",
				self.strings.resolve(name).unwrap(),
				sema.trait_name(&self.strings, trait_index),
			));
		sema.report_type_mismatch(
			&self.strings,
			head,
			(
				sema.decls.constants[usize::from(declaration)].file_id,
				WrittenType::Written(expected_ty),
			),
			(
				sema.decls.constants[usize::from(constant)].file_id,
				WrittenType::Written(ty),
			),
			(expected, found),
		);
		Ok(())
	}

	/// The written signature of a trait's or a trait impl's function, for
	/// its spans.
	fn function_syntax(
		&self,
		function: FunctionIdx,
	) -> &'ast ast::FunctionSignature {
		match *self.ast_node(DeclId::Function(function)) {
			AstNodeRef::TraitFunction {
				item: ast::TraitItem::Function { signature, .. },
				..
			}
			| AstNodeRef::TraitImplFunction {
				item: ast::ImplItem::Function { signature, .. },
				..
			} => signature,
			_ => unreachable!("a trait's or a trait impl's function"),
		}
	}

	/// A parameter's name is part of the trait's contract: a call by name
	/// uses the declaration's names, whichever impl it reaches. So an impl
	/// names a parameter as the trait does, or leaves it unnamed, which binds
	/// no local and changes nothing for callers; it never renames one, nor
	/// names one the trait leaves unnamed. Only the name is compared; whether
	/// its local is `mut` is the body's own.
	fn report_name_mismatch(
		&mut self,
		sema: &mut Semantics,
		trait_index: TraitIdx,
		member: MemberKind,
		(declaration, function): (FunctionIdx, FunctionIdx),
		position: usize,
		(expected, found): (
			Option<Spanned<SymbolU32>>,
			Option<Spanned<SymbolU32>>,
		),
	) {
		let describe = |name: Option<Spanned<SymbolU32>>| match name {
			Some(name) => {
				format!("`{}`", self.strings.resolve(name.inner).unwrap())
			}
			None => "an unnamed parameter".to_owned(),
		};
		// An unnamed parameter is pointed at by its type.
		let at = |function: FunctionIdx, name: Option<Spanned<SymbolU32>>| {
			name.map_or_else(
				|| {
					self.function_syntax(function).params[position]
						.inner
						.inner
						.ty
						.span
				},
				|name| name.span,
			)
		};
		let diagnostic = sema
			.signature_mismatch(&self.strings, trait_index, member, function)
			.with_label(
				SourceSpan::new(
					sema.decls.functions[usize::from(function)].file_id,
					at(function, found),
				)
				.primary_label()
				.with_message(format!(
					"expected {}, found {}",
					describe(expected),
					describe(found),
				)),
			)
			.with_label(
				SourceSpan::new(
					sema.decls.functions[usize::from(declaration)].file_id,
					at(declaration, expected),
				)
				.secondary_label()
				.with_message("parameter in trait"),
			)
			.with_note(
				"a parameter's name is part of the trait's contract: a call \
				 by name uses the trait's names, so an impl names it the same \
				 or leaves it unnamed",
			);
		sema.diagnostics.push(diagnostic);
	}
}

#[cfg(test)]
mod tests {
	use codespan_reporting::diagnostic::Diagnostic;
	use indoc::indoc;

	use super::*;
	use crate::diagnostics::DiagnosticCode;
	use crate::testing::DiagnosticView;
	use crate::tir::signatures::tests::source_graph;
	use crate::vfs::Files;

	/// A checked `Semantics`, with the files it was checked from.
	struct TestCase {
		files: Files,
		sema: Semantics,
	}

	impl TestCase {
		fn new(source: &str) -> Self {
			let mut strings = crate::symbols::Keyword::create_interner();
			let graph = source_graph(source, &mut strings);
			let sema = crate::tir::check(&graph, &mut strings);
			Self {
				files: graph.files,
				sema,
			}
		}

		fn diagnostics(&self) -> DiagnosticView<'_> {
			DiagnosticView::new(
				"conformance",
				&self.sema.diagnostics,
				&self.files,
			)
		}
	}

	#[test]
	fn an_associated_type_value_satisfies_its_declared_bound() {
		let case = TestCase::new(indoc! {"
			trait Size {}
			impl Size for u32 {}
			trait Container { type Item: Size; }
			struct Bag();
			impl Container for Bag { type Item = u32; }
		"});
		case.diagnostics().assert_none();
	}

	#[test]
	fn an_associated_type_value_violating_its_declared_bound_is_reported() {
		let case = TestCase::new(indoc! {"
			trait Size {}
			trait Container { type Item: Size; }
			struct Bag();
			impl Container for Bag { type Item = u8; }
		"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics()
			.assert_error_saying("the trait bound `u8: Size` is not satisfied");
	}

	#[test]
	fn an_inherited_default_is_checked_against_the_bound_per_impl() {
		let case = TestCase::new(indoc! {"
			trait Size {}
			trait Container { type Item: Size = u8; }
			struct Bag();
			impl Container for Bag {}
		"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
	}

	/// A target that does not resolve leaves nothing to prove supertraits
	/// for, but a value's bound does not depend on it.
	#[test]
	fn an_impl_of_an_unresolved_target_still_checks_its_values() {
		let case = TestCase::new(indoc! {"
			trait Size {}
			trait Container: Size + StackValue { type Item: Size; func f(self: Self); }
			impl Container for Missing { type Item = u8; func f(self: Self) {} }
		"});
		case.diagnostics().assert_codes(&[
			DiagnosticCode::UndeclaredIdentifier,
			DiagnosticCode::TraitBoundViolation,
		]);
		case.diagnostics()
			.assert_error_saying("the trait bound `u8: Size` is not satisfied");
	}

	#[test]
	fn a_value_naming_an_impl_parameter_needs_the_parameter_bounded() {
		let case = TestCase::new(indoc! {"
			trait Size {}
			trait Container { type Item: Size; }
			struct Bounded<T>();
			struct Unbounded<T>();
			impl<T: Size> Container for Bounded<T> { type Item = T; }
			impl<T> Container for Unbounded<T> { type Item = T; }
		"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics()
			.assert_error_saying("the trait bound `T: Size` is not satisfied");
	}

	#[test]
	fn a_nested_equality_on_an_associated_type_is_proved_for_the_value() {
		let case = TestCase::new(indoc! {"
			trait Inner { type Value; }
			struct Good();
			struct Bad();
			impl Inner for Good { type Value = u32; }
			impl Inner for Bad { type Value = u8; }
			trait Outer { type Item: Inner where { Value = u32 }; }
			struct A();
			struct B();
			impl Outer for A { type Item = Good; }
			impl Outer for B { type Item = Bad; }
		"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::AssocTypeEqualityMismatch]);
	}

	#[test]
	fn an_impl_requires_its_traits_supertraits() {
		let case = TestCase::new(indoc! {"
			trait Base {}
			trait Derived: Base {}
			struct Both();
			struct Only();
			impl Base for Both {}
			impl Derived for Both {}
			impl Derived for Only {}
		"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics().assert_error_saying(
			"the trait bound `Only: Base` is not satisfied",
		);
	}

	#[test]
	fn a_generic_impl_proves_its_supertraits_with_its_own_bounds() {
		let case = TestCase::new(indoc! {"
			trait Marker {}
			trait Base {}
			trait Derived: Base {}
			struct W<T>();
			struct V<T>();
			impl<T: Marker> Base for W<T> {}
			impl<T: Marker> Derived for W<T> {}
			impl<T: Marker> Base for V<T> {}
			impl<T> Derived for V<T> {}
		"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics().assert_error_saying(
			"the trait bound `V<T>: Base` is not satisfied",
		);
	}

	#[test]
	fn a_supertraits_binding_is_proved_for_the_target() {
		let case = TestCase::new(indoc! {"
			trait Base { type Out; }
			trait Derived: Base where { Out = u32 } {}
			struct Good();
			struct Bad();
			impl Base for Good { type Out = u32; }
			impl Derived for Good {}
			impl Base for Bad { type Out = u8; }
			impl Derived for Bad {}
		"});
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::AssocTypeEqualityMismatch]);
	}

	/// The source text a diagnostic's label covers.
	fn labelled<'s>(
		source: &'s str,
		diagnostic: &Diagnostic<FileId>,
		index: usize,
	) -> &'s str {
		&source[diagnostic.labels[index].range.clone()]
	}

	const PRELUDE: &str = "
		struct Box<T>();
	";

	#[test]
	fn an_impl_that_keeps_the_contract_reports_nothing() {
		let source = format!(
			"{PRELUDE}{}",
			indoc! {"
			trait Store: StackValue {
				type Item: StackValue;
				func get(self: Self) -> Box<Self::Item>;
				func put(self: Self, item: Self::Item, at: u32);
				func swap<A: StackValue, B: StackValue>(a: A, b: B) -> (B, A);
				func kept(self: Self) -> u32 { 0 }
				const ZERO: Self;
			}
			struct Bag<T>();
			impl<T: StackValue> Store for Bag<T> {
				type Item = T;
				func get(self: Self) -> Box<T> { Box() }
				func put(self: Self, mut item: T, at: u32) {}
				func swap<X: StackValue, Y: StackValue>(a: X, b: Y) -> (Y, X) { (b, a) }
				const ZERO: Bag<T> = Bag();
			}
		"}
		);
		let case = TestCase::new(&source);
		case.diagnostics().assert_none();
	}

	#[test]
	fn a_declaration_without_a_default_must_be_provided() {
		let case = TestCase::new(&format!(
			"{PRELUDE}{}",
			indoc! {"
				trait Store: StackValue {
					type Item;
					type Kept = u8;
					func get(self: Self) -> u32;
					func kept(self: Self) {}
					const N: u32;
					const K: u32 = 0;
				}
				struct Bag();
				impl Store for Bag {}
			"}
		));
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::IncompleteTraitImpl]);
		assert_eq!(
			case.sema.diagnostics[0].labels[0].message,
			"missing `Item`, `get`, `N` in implementation"
		);
	}

	#[test]
	fn a_member_of_another_kind_does_not_provide_its_declaration() {
		let case = TestCase::new(&format!(
			"{PRELUDE}{}",
			indoc! {"
				trait Store { func size() -> u32; type Item; }
				struct Bag();
				impl Store for Bag { const size: u32 = 0; func Item() {} }
			"}
		));
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TraitImplItemKindMismatch,
			DiagnosticCode::TraitImplItemKindMismatch,
			DiagnosticCode::IncompleteTraitImpl,
		]);
		case.diagnostics().assert_error_saying(
			"`size` is a constant, but trait `Store` declares a function",
		);
		case.diagnostics().assert_error_saying(
			"`Item` is a function, but trait `Store` declares an associated \
			 type",
		);
	}

	/// A default supplies the declaration, so a member of another kind is
	/// reported only as such, not also as missing.
	#[test]
	fn a_member_of_another_kind_is_reported_once_where_the_trait_has_a_default()
	{
		let case = TestCase::new(&format!(
			"{PRELUDE}{}",
			indoc! {"
				trait Store { func size() -> u32 { 0 } }
				struct Bag();
				impl Store for Bag { type size = u32; }
			"}
		));
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitImplItemKindMismatch]);
	}

	#[test]
	fn a_member_the_trait_does_not_declare_is_reported() {
		let case = TestCase::new(&format!(
			"{PRELUDE}{}",
			indoc! {"
				trait Store {}
				struct Bag();
				impl Store for Bag { func extra() {} type Extra = u8; }
			"}
		));
		case.diagnostics().assert_codes(&[
			DiagnosticCode::NotATraitMember,
			DiagnosticCode::NotATraitMember,
		]);
		case.diagnostics().assert_error_saying(
			"function `extra` is not a member of trait `Store`",
		);
	}

	#[test]
	fn parameter_names_are_part_of_the_contract() {
		let source = format!(
			"{PRELUDE}{}",
			indoc! {"
			trait Store: StackValue {
				func renamed(self: Self, rhs: u32);
				func unnamed(self: Self, u32);
				func named(self: Self, at: u32);
				func bare(self: Self, at: u32);
				func receiver(self: Self);
			}
			struct Bag();
			impl Store for Bag {
				func renamed(self: Self, other: u32) {}
				func unnamed(self: Self, at: u32) {}
				func named(self: Self, _: u32) {}
				func bare(self: Self, u32) {}
				func receiver(this: Self) {}
			}
		"}
		);
		let case = TestCase::new(&source);
		// `named` and `bare` leave the trait's name unbound, which keeps the
		// contract.
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TraitImplSignatureMismatch,
			DiagnosticCode::TraitImplSignatureMismatch,
			DiagnosticCode::TraitImplSignatureMismatch,
		]);
		let [renamed, unnamed, receiver] = &case.sema.diagnostics[..] else {
			unreachable!()
		};
		assert_eq!(labelled(&source, renamed, 0), "other");
		assert_eq!(renamed.labels[0].message, "expected `rhs`, found `other`");
		assert_eq!(labelled(&source, renamed, 1), "rhs");
		assert_eq!(
			unnamed.labels[0].message,
			"expected an unnamed parameter, found `at`"
		);
		// An unnamed parameter is pointed at by its type.
		assert_eq!(labelled(&source, unnamed, 1), "u32");
		assert_eq!(receiver.labels[0].message, "expected `self`, found `this`");
	}

	#[test]
	fn the_counts_of_type_parameters_and_parameters_must_match() {
		let case = TestCase::new(&format!(
			"{PRELUDE}{}",
			indoc! {"
				trait Store: StackValue {
					func generic<T: StackValue>(x: T);
					func arity(self: Self, a: u32);
				}
				struct Bag();
				impl Store for Bag {
					func generic<T: StackValue, U>(x: T) {}
					func arity(self: Self) {}
				}
			"}
		));
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TraitImplSignatureMismatch,
			DiagnosticCode::TraitImplSignatureMismatch,
		]);
		assert_eq!(
			case.sema.diagnostics[0].labels[0].message,
			"expected 1 type parameter, found 2"
		);
		assert_eq!(
			case.sema.diagnostics[1].labels[0].message,
			"expected 2 parameters, found 1"
		);
	}

	#[test]
	fn own_type_parameters_correspond_by_position() {
		let case = TestCase::new(&format!(
			"{PRELUDE}{}",
			indoc! {"
				trait Store { func pair<A: StackValue, B: StackValue>(a: A, b: B); }
				struct Bag();
				impl Store for Bag { func pair<A: StackValue, B: StackValue>(a: B, b: A) {} }
			"}
		));
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitImplSignatureMismatch]);
		assert_eq!(
			case.sema.diagnostics[0].labels[0].message,
			"expected `A`, found `B`"
		);
	}

	#[test]
	fn a_difference_is_pointed_at_where_each_side_writes_it() {
		let source = format!(
			"{PRELUDE}{}",
			indoc! {"
			trait Store: StackValue { func put(self: Self, slot: Box<(u8, u32)>); }
			struct Bag();
			impl Store for Bag { func put(self: Self, slot: Box<(u8, u64)>) {} }
		"}
		);
		let case = TestCase::new(&source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitImplSignatureMismatch]);
		let diagnostic = &case.sema.diagnostics[0];
		let impl_side = source.rfind("u64").unwrap();
		assert_eq!(diagnostic.labels[0].range.start, impl_side);
		assert_eq!(diagnostic.labels[0].message, "expected `u32`, found `u64`");
		assert_eq!(labelled(&source, diagnostic, 1), "u32");
		assert!(diagnostic.notes.is_empty());
	}

	#[test]
	fn a_difference_behind_a_projection_points_at_the_projection() {
		let source = format!(
			"{PRELUDE}{}",
			indoc! {"
			trait Store: StackValue { type Item; func get(self: Self) -> Box<Self::Item>; }
			struct Bag();
			impl Store for Bag { type Item = u8; func get(self: Self) -> Box<u16> { Box() } }
		"}
		);
		let case = TestCase::new(&source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitImplSignatureMismatch]);
		let diagnostic = &case.sema.diagnostics[0];
		assert_eq!(labelled(&source, diagnostic, 0), "u16");
		assert_eq!(diagnostic.labels[0].message, "expected `u8`, found `u16`");
		assert_eq!(labelled(&source, diagnostic, 1), "Self::Item");
	}

	#[test]
	fn a_difference_behind_an_alias_is_named_in_a_note() {
		let source = format!(
			"{PRELUDE}{}",
			indoc! {"
			type Alias = Box<(u8, u64)>;
			trait Store: StackValue { func put(self: Self, slot: Box<(u8, u32)>); }
			struct Bag();
			impl Store for Bag { func put(self: Self, slot: Alias) {} }
		"}
		);
		let case = TestCase::new(&source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitImplSignatureMismatch]);
		let diagnostic = &case.sema.diagnostics[0];
		assert_eq!(labelled(&source, diagnostic, 0), "Alias");
		assert_eq!(
			diagnostic.notes,
			[
				"they differ in type argument 1 → tuple element 2: expected \
			  `u32`, found `u64`"
			]
		);
	}

	#[test]
	fn a_left_out_result_is_unit_pointed_at_by_the_name() {
		let source = format!(
			"{PRELUDE}{}",
			indoc! {"
			trait Store: StackValue { func count(self: Self) -> u32; }
			struct Bag();
			impl Store for Bag { func count(self: Self) {} }
		"}
		);
		let case = TestCase::new(&source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitImplSignatureMismatch]);
		let diagnostic = &case.sema.diagnostics[0];
		assert_eq!(labelled(&source, diagnostic, 0), "count");
		assert_eq!(diagnostic.labels[0].message, "expected `u32`, found `()`");
	}

	#[test]
	fn a_constant_has_its_declarations_type_with_self_as_the_target() {
		let source = format!(
			"{PRELUDE}{}",
			indoc! {"
			trait Store { const SELF: Self; const N: u32; }
			struct Bag();
			impl Store for Bag { const SELF: Bag = Bag(); const N: u64 = 0; }
		"}
		);
		let case = TestCase::new(&source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitImplConstTypeMismatch]);
		case.diagnostics().assert_error_saying(
			"constant `N` has an incompatible type for trait `Store`",
		);
		assert_eq!(labelled(&source, &case.sema.diagnostics[0], 0), "u64");
	}

	const ORDERING: &str = "
		trait PartialEq {}
		trait PartialOrd: PartialEq {}
		trait Eq: PartialEq {}
		trait Ord: PartialOrd + Eq {}
		trait Container { type Item: StackValue; }
		struct Bag();
	";

	#[test]
	fn an_impl_function_may_require_less_than_or_as_much_as_its_trait() {
		let case = TestCase::new(&format!(
			"{PRELUDE}{ORDERING}{}",
			indoc! {"
				trait Sorter {
					func fewer<T: StackValue + PartialEq>(x: T);
					func same<T: StackValue + PartialOrd>(x: T);
					func implied<T: StackValue + Ord>(x: T);
				}
				impl Sorter for Bag {
					func fewer<T: StackValue>(x: T) {}
					func same<T: StackValue + PartialOrd>(x: T) {}
					func implied<T: StackValue + PartialEq>(x: T) {}
				}
			"}
		));
		case.diagnostics().assert_none();
	}

	#[test]
	fn a_stricter_bound_is_reported_once_where_it_is_written() {
		let source = format!(
			"{PRELUDE}{ORDERING}{}",
			indoc! {"
			trait Sorter { func sort<T: StackValue + PartialEq>(x: T); }
			impl Sorter for Bag { func sort<T: StackValue + Ord>(x: T) {} }
		"}
		);
		let case = TestCase::new(&source);
		// `Ord` brings `PartialOrd` and `Eq`, which do not follow either; the
		// written bound is the one report.
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::ImplStricterThanTrait]);
		case.diagnostics().assert_error_saying(
			"impl has stricter requirements than trait `Sorter`",
		);
		let diagnostic = &case.sema.diagnostics[0];
		assert_eq!(labelled(&source, diagnostic, 0), "Ord");
		assert_eq!(
			diagnostic.labels[0].message,
			"impl has extra requirement `T: Ord`"
		);
		assert_eq!(labelled(&source, diagnostic, 1), "sort");
	}

	#[test]
	fn an_extra_equality_is_a_stricter_requirement() {
		let case = TestCase::new(&format!(
			"{PRELUDE}{ORDERING}{}",
			indoc! {"
				trait Store { func take<U: StackValue + Container>(x: U); }
				impl Store for Bag {
					func take<U: StackValue + Container where { Item = u32 }>(x: U) {}
				}
			"}
		));
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::ImplStricterThanTrait]);
		assert_eq!(
			case.sema.diagnostics[0].labels[0].message,
			"impl has extra requirement `<U as Container>::Item == u32`"
		);
	}

	#[test]
	fn a_conflicting_equality_is_a_stricter_requirement() {
		let case = TestCase::new(&format!(
			"{PRELUDE}{ORDERING}{}",
			indoc! {"
				trait Store { func take<U: StackValue + Container where { Item = u8 }>(x: U); }
				impl Store for Bag {
					func take<U: StackValue + Container where { Item = u16 }>(x: U) {}
				}
			"}
		));
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::ImplStricterThanTrait]);
		assert_eq!(
			case.sema.diagnostics[0].labels[0].message,
			"impl has extra requirement `<U as Container>::Item == u16`"
		);
	}

	/// A bound nested on a projection is proved like one on the parameter:
	/// `Item: PartialEq` follows from the trait's `Item: Ord`, `Item: Ord`
	/// follows from nothing.
	#[test]
	fn a_nested_bound_is_proved_from_the_traits() {
		let case = TestCase::new(&format!(
			"{PRELUDE}{ORDERING}{}",
			indoc! {"
				trait Store {
					func strict<U: StackValue + Container>(x: U);
					func loose<U: StackValue + Container where { Item: Ord }>(x: U);
				}
				impl Store for Bag {
					func strict<U: StackValue + Container where { Item: Ord }>(x: U) {}
					func loose<U: StackValue + Container where { Item: PartialEq }>(x: U) {}
				}
			"}
		));
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::ImplStricterThanTrait]);
		assert_eq!(
			case.sema.diagnostics[0].labels[0].message,
			"impl has extra requirement `<U as Container>::Item: Ord`"
		);
	}

	#[test]
	fn self_in_a_declarations_bound_is_the_impls_target() {
		let case = TestCase::new(&format!(
			"{PRELUDE}{ORDERING}{}",
			indoc! {"
				trait Into { type Out; }
				trait Convert { func from<T: StackValue + Into where { Out = Self }>(x: T); }
				impl Convert for Bag {
					func from<T: StackValue + Into where { Out = Bag }>(x: T) {}
				}
			"}
		));
		case.diagnostics().assert_none();
	}

	#[test]
	fn a_signature_is_compared_under_the_traits_assumptions() {
		let case = TestCase::new(&format!(
			"{PRELUDE}{ORDERING}{}",
			indoc! {"
				trait Store {
					func read<U: Container where { Item = u32 }>(x: U::Item);
					func write<U: Container where { Item = u32 }>(x: u32);
				}
				impl Store for Bag {
					func read<U: Container>(x: u32) {}
					func write<U: Container>(x: U::Item) {}
				}
			"}
		));
		// Both read `U::Item` as `u32`, the trait's equality, though the impl
		// does not repeat it.
		case.diagnostics().assert_none();
	}
}
