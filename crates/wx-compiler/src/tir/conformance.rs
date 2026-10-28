//! Trait-impl conformance: whether `impl Tr for X` keeps the contract `Tr`
//! states for `X`. It is one check per impl (`TypeObligation::
//! CheckConformance`), run with the other declaration checks once every
//! signature exists, so everything an impl owes its trait is decided and
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
//! the trait's bounds. The function is read in the frame such a caller sees
//! (`contract_frame`): the impl's own frame around it, and its own parameters
//! assuming the declaration's clauses. Its own clauses are proved there, and
//! its signature is compared there.

use super::bounds::{
	BoundClauses, BoundId, Equalities, EqualityClause, TraitClause,
};
use super::defs::{
	AstNodeRef, BindingKey, ConstIdx, DefId, DefKind, FunctionIdx, MemberIdx,
	MemberKind, Tier, TraitIdx, TraitImplIdx,
};
use super::members::TraitMemberSelection;
use super::obligations::BoundRequirements;
use super::resolutions::Referent;
use super::signatures::{ParamBounds, TypeContext};
use super::solver::{
	ImplMember, NormalizationDepth, RewriteFlags, SolverError,
	UnsatisfiedClause,
};
use super::types::{Substitution, Type, TypeEnvIdx, TypeEnvOwner, TypeIndex};
use crate::ast::{self, Spanned};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::vfs::FileId;
use codespan_reporting::diagnostic::Diagnostic;
use string_interner::symbol::SymbolU32;

impl<'ast> TypeContext<'ast, '_, '_> {
	/// Checks what `impl_index` owes its trait. Each part is reported on its
	/// own, so one failure does not hide the next; only "not decided yet"
	/// is returned.
	pub(super) fn check_conformance(
		&mut self,
		impl_index: TraitImplIdx,
	) -> Result<(), SolverError> {
		// An impl of an unresolved trait reported that already.
		let Some(trait_def) =
			self.impl_dispatch.trait_header(impl_index).trait_def
		else {
			return Ok(());
		};
		let trait_index = trait_def.inner;
		let header = self.trait_impls[usize::from(impl_index)]
			.as_ref()
			.expect("every signature exists when declarations are checked");
		let (scope, target) = (header.type_params, header.target);
		let file_id = self.defs.trait_impls[usize::from(impl_index)].file_id;
		let at_target = SourceSpan::new(file_id, target.span);
		let owner = TypeEnvOwner::Trait(trait_index);

		self.check_members(impl_index, trait_index, target.inner, at_target)?;

		// The supertraits are the clauses on the trait's `Self`; the target
		// must satisfy them where the impl is written, with its parameters'
		// bounds assumed.
		let trait_env = self.traits[usize::from(trait_index)].env;
		let arguments = self.types.push_list(&[target.inner]);
		let result = self.check_bound_requirements(
			scope,
			BoundRequirements::Parameter {
				env: trait_env,
				index: 0,
				arguments,
			},
			target,
			at_target,
			owner,
		);
		self.report_unfinished(result, at_target)?;

		for member_index in
			0..self.defs.traits[usize::from(trait_index)].members.len()
		{
			let declaration @ MemberKind::AssociatedType(declaration_index) =
				self.defs.traits[usize::from(trait_index)].members
					[member_index]
					.kind
			else {
				continue;
			};
			// The value's own judgement (`CheckAssocValue`) reports a value
			// that has no meaning; one the impl omits with no default is
			// reported missing above.
			let value = match self.assoc_value(
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
				match self.defs.select_trait_member(impl_index, declaration) {
					TraitMemberSelection::Impl(MemberKind::AssociatedType(
						provider,
					)) => {
						let AstNodeRef::TraitImplAssocType {
							item: ast::ImplItem::AssocType { ty, .. },
							..
						} = *self.ast_node(DefId::AssocType(provider))
						else {
							unreachable!("a trait impl's associated type")
						};
						SourceSpan::new(
							self.defs.assoc_types[usize::from(provider)]
								.file_id,
							ty.span,
						)
					}
					_ => at_target,
				};
			let result = self.check_bound_requirements(
				scope,
				BoundRequirements::AssociatedType {
					declaration: declaration_index,
					trait_index,
					receiver: target.inner,
				},
				Spanned {
					inner: value,
					span: reference.span,
				},
				reference,
				owner,
			);
			self.report_unfinished(result, reference)?;
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
		impl_index: TraitImplIdx,
		trait_index: TraitIdx,
		target: TypeIndex,
		at_target: SourceSpan,
	) -> Result<(), SolverError> {
		let impl_def = &self.defs.trait_impls[usize::from(impl_index)];
		let impl_file = impl_def.file_id;
		for index in 0..impl_def.members.len() {
			let impl_def = &self.defs.trait_impls[usize::from(impl_index)];
			let member = impl_def.members[index].kind;
			let name = self.defs.name(member.def_id());
			// A second member of one name was reported as a duplicate.
			if impl_def
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
			let trait_def = &self.defs.traits[usize::from(trait_index)];
			let Some(declaration_index) =
				[member.tier(), other_tier].into_iter().find_map(|tier| {
					trait_def
						.bindings
						.get(&BindingKey::new(tier, name.inner))
						.copied()
				})
			else {
				self.report_not_a_member(trait_index, member, name, at_member);
				continue;
			};
			let declaration =
				trait_def.members[usize::from(declaration_index)].kind;
			match (declaration, member) {
				(
					MemberKind::Function(expected)
					| MemberKind::Method(expected),
					MemberKind::Function(found) | MemberKind::Method(found),
				) => {
					let result = self.compare_function(
						trait_index,
						declaration,
						expected,
						found,
						target,
					);
					self.report_unfinished(result, at_member)?;
				}
				(
					MemberKind::Constant(expected),
					MemberKind::Constant(found),
				) => {
					let result = self.compare_constant(
						trait_index,
						expected,
						found,
						target,
					);
					self.report_unfinished(result, at_member)?;
				}
				(
					MemberKind::AssociatedType(_),
					MemberKind::AssociatedType(_),
				) => {}
				_ => self.report_kind_mismatch(
					trait_index,
					declaration,
					member,
					at_member,
				),
			}
		}

		let trait_def = &self.defs.traits[usize::from(trait_index)];
		let missing: Vec<Spanned<SymbolU32>> = trait_def
			.members
			.iter()
			.filter(|member| {
				!self.provides(impl_index, member.kind)
					&& !self.has_default(member.kind)
			})
			.map(|member| self.defs.name(member.kind.def_id()))
			.collect();
		if !missing.is_empty() {
			self.report_missing(trait_index, &missing, at_target);
		}
		Ok(())
	}

	/// Whether the impl provides `declaration`: selection finds a member of
	/// its kind under its name. One of another kind is reported as such, and
	/// provides nothing.
	fn provides(
		&self,
		impl_index: TraitImplIdx,
		declaration: MemberKind,
	) -> bool {
		matches!(
			self.defs.select_trait_member(impl_index, declaration),
			TraitMemberSelection::Impl(_)
		)
	}

	/// Whether the trait's declaration supplies what an impl omits.
	fn has_default(&self, declaration: MemberKind) -> bool {
		match declaration {
			MemberKind::AssociatedType(index) => self.assoc_types
				[usize::from(index)]
			.as_ref()
			.is_some_and(|signature| signature.value.is_some()),
			MemberKind::Function(index) | MemberKind::Method(index) => {
				matches!(
					*self.ast_node(DefId::Function(index)),
					AstNodeRef::TraitFunction {
						item: ast::TraitItem::Function { body: Some(_), .. },
						..
					}
				)
			}
			MemberKind::Constant(index) => matches!(
				*self.ast_node(DefId::Const(index)),
				AstNodeRef::TraitConst {
					item: ast::TraitItem::Const { value: Some(_), .. },
					..
				}
			),
		}
	}

	/// The impl's `function` against the trait's `declaration`, read in the
	/// frame a caller through the trait sees (`contract_frame`): `Self` is
	/// `target`, and the declaration's own type parameters are the
	/// function's, by position, assuming what the declaration's do. Reports
	/// the first difference: the number of own type parameters, a bound the
	/// declaration does not imply, the number of parameters, then each
	/// parameter's name and type in order, then the result.
	fn compare_function(
		&mut self,
		trait_index: TraitIdx,
		member: MemberKind,
		declaration: FunctionIdx,
		function: FunctionIdx,
		target: TypeIndex,
	) -> Result<(), SolverError> {
		let declaration_env =
			self.functions[usize::from(declaration)].type_params;
		let env = self.functions[usize::from(function)].type_params;
		let (expected_own, own) = (
			self.own_params(declaration_env).len(),
			self.own_params(env).len(),
		);
		if expected_own != own {
			self.report_count_mismatch(
				trait_index,
				member,
				(declaration, function),
				"type parameter",
				(expected_own, own),
			);
			return Ok(());
		}
		let frame = self.contract_frame(declaration, function, target);
		if !self.check_own_bounds(
			trait_index,
			(declaration, function),
			frame,
		)? {
			return Ok(());
		}
		let (expected_signature, signature) = (
			&self.functions[usize::from(declaration)],
			&self.functions[usize::from(function)],
		);
		let (expected_params, expected_result) = (
			expected_signature.param_types,
			expected_signature.return_type,
		);
		let (found_params, found_result) =
			(signature.param_types, signature.return_type);
		let params = self.types.list(found_params).len();
		let expected_count = self.types.list(expected_params).len();
		if expected_count != params {
			self.report_count_mismatch(
				trait_index,
				member,
				(declaration, function),
				"parameter",
				(expected_count, params),
			);
			return Ok(());
		}
		let arguments: Box<[TypeIndex]> = std::iter::once(target)
			.chain(self.own_params(frame).iter().copied())
			.collect();
		// The result is compared as one more position, after the parameters.
		for position in 0..=params {
			let (expected, found) = if position < params {
				(
					self.types.list(expected_params)[position],
					self.types.list(found_params)[position],
				)
			} else {
				(expected_result, found_result)
			};
			// A type that failed to lower was reported where it is written,
			// and the parameter is not understood well enough to compare,
			// its name included.
			if self.types.has_error(expected) || self.types.has_error(found) {
				continue;
			}
			if position < params {
				let expected_name = self.defs.functions
					[usize::from(declaration)]
				.params[position];
				let name =
					self.defs.functions[usize::from(function)].params[position];
				// Leaving the parameter unnamed only binds no local: the contract
				// is still the trait's, and so are the names calls use.
				if name.is_some()
					&& expected_name.map(|name| name.inner)
						!= name.map(|name| name.inner)
				{
					self.report_name_mismatch(
						trait_index,
						member,
						(declaration, function),
						position,
						(expected_name, name),
					);
					return Ok(());
				}
			}
			let expected = self.types.substitute(
				expected,
				Substitution {
					envs: &self.type_envs,
					env: declaration_env,
					args: &arguments,
				},
			);
			let found = self.types.substitute(
				found,
				Substitution {
					envs: &self.type_envs,
					env,
					args: self.type_envs.identity_args(frame),
				},
			);
			let expected = self.normalize(
				frame,
				expected,
				NormalizationDepth::Deep,
				RewriteFlags::ALL,
			)?;
			let found = self.normalize(
				frame,
				found,
				NormalizationDepth::Deep,
				RewriteFlags::ALL,
			)?;
			// Normalizing may still meet an error (a projection with no value),
			// which was reported where it belongs.
			if expected == found
				|| self.types.has_error(expected)
				|| self.types.has_error(found)
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
			let head = self.signature_mismatch(trait_index, member, function);
			self.report_type_mismatch(
				head,
				(
					self.defs.functions[usize::from(declaration)].file_id,
					written(expected_syntax),
				),
				(
					self.defs.functions[usize::from(function)].file_id,
					written(syntax),
				),
				(expected, found),
			);
			return Ok(());
		}
		Ok(())
	}

	/// The frame a caller through the trait sees `function` in: the impl's
	/// own frame around it, and the function's own type parameters (their
	/// names, for display) assuming the clauses the declaration's state, with
	/// `Self` as `target` and the declaration's parameters as these, by
	/// position. It exists for the check alone. A function without its own
	/// parameters has nothing to read differently, and is read in its own
	/// frame.
	///
	/// A second frame is needed only because assumptions are keyed by
	/// parameter identity; `notes/tir-param-env-plan.md` proposes making the
	/// assumption context a value, which would reduce this to building one.
	fn contract_frame(
		&mut self,
		declaration: FunctionIdx,
		function: FunctionIdx,
		target: TypeIndex,
	) -> TypeEnvIdx {
		let env = self.functions[usize::from(function)].type_params;
		if self.own_params(env).is_empty() {
			return env;
		}
		let parent = self
			.type_envs
			.parent(env)
			.expect("a function's own frame has its impl's around it");
		let names = self.type_envs.param_names(env).to_vec();
		let frame = self.type_envs.push_param_frame(
			&mut self.types,
			TypeEnvOwner::Function(function),
			parent,
			names,
		);
		let declaration_env =
			self.functions[usize::from(declaration)].type_params;
		let own = self.type_envs.param_types(frame);
		let count = own.len();
		let arguments: Box<[TypeIndex]> =
			std::iter::once(target).chain(own.iter().copied()).collect();
		// Only the clauses are read; the bounds as written are the
		// declaration's, for display.
		let bounds = (0..count)
			.map(|index| ParamBounds {
				declared_bounds: Box::new([]),
				clauses: self.instantiate_clauses(
					self.param_bounds[usize::from(declaration_env)][index]
						.clauses,
					declaration_env,
					&arguments,
				),
			})
			.collect();
		// Indexed by frame; building the clauses pushed none.
		self.param_bounds.push(bounds);
		frame
	}

	/// `clauses`, written in `env`'s chain, with that chain's parameters
	/// replaced by `arguments`: a new run, the written bounds they come from
	/// kept.
	fn instantiate_clauses(
		&mut self,
		clauses: BoundClauses,
		env: TypeEnvIdx,
		arguments: &[TypeIndex],
	) -> BoundClauses {
		let Equalities::Final(equalities) = clauses.equalities else {
			unreachable!("every signature exists when declarations are checked")
		};
		let substitution = Substitution {
			envs: &self.type_envs,
			env,
			args: arguments,
		};
		let traits: Vec<TraitClause> = self
			.clauses
			.traits(clauses.traits)
			.iter()
			.map(|clause| TraitClause {
				subject: self.types.substitute(clause.subject, substitution),
				..*clause
			})
			.collect();
		let equalities: Vec<EqualityClause> = self
			.clauses
			.equalities(equalities)
			.iter()
			.map(|clause| EqualityClause {
				projection: self
					.types
					.substitute(clause.projection, substitution),
				value: self.types.substitute(clause.value, substitution),
				..*clause
			})
			.collect();
		BoundClauses {
			traits: self.clauses.push_traits(&traits),
			equalities: Equalities::Final(
				self.clauses.push_equalities(&equalities),
			),
		}
	}

	/// Proves the clauses of `function`'s own type parameters in `frame`, where
	/// they assume only the declaration's: an impl may require less than its
	/// trait, never more. Each written bound that does not follow is reported
	/// once, by the first of its clauses that fails (`T: Ord` over a trait's
	/// `T: PartialEq` is one report, not one per supertrait). Answers whether
	/// every bound follows.
	fn check_own_bounds(
		&mut self,
		trait_index: TraitIdx,
		(declaration, function): (FunctionIdx, FunctionIdx),
		frame: TypeEnvIdx,
	) -> Result<bool, SolverError> {
		let env = self.functions[usize::from(function)].type_params;
		if frame == env {
			return Ok(true);
		}
		let arguments: Box<[TypeIndex]> =
			self.type_envs.identity_args(frame).into();
		let mut holds = true;
		for index in 0..self.type_envs.param_types(env).len() {
			let clauses = self.param_bounds[usize::from(env)][index].clauses;
			let root = self.type_envs.param_types(env)[index];
			let subject = self.type_envs.param_types(frame)[index];
			let mut failures = Vec::new();
			if self.satisfies_clauses(
				frame,
				clauses,
				(root, subject),
				(env, &arguments),
				Some(&mut failures),
				None,
			)? {
				continue;
			}
			holds = false;
			let Equalities::Final(equalities) = clauses.equalities else {
				unreachable!("proved clauses are final")
			};
			// The bound written on this parameter each failure came from.
			let mut reported = Vec::new();
			for failure in failures {
				let origin = match failure {
					UnsatisfiedClause::Trait {
						trait_index,
						source,
						..
					} => self
						.clauses
						.traits(clauses.traits)
						.iter()
						.find(|clause| {
							clause.trait_index == trait_index
								&& clause.source == source
						})
						.map(|clause| clause.origin),
					UnsatisfiedClause::Equality { source, .. } => self
						.clauses
						.equalities(equalities)
						.iter()
						.find(|clause| clause.source == source)
						.map(|clause| clause.origin),
				}
				.expect("a failure is one of the proved clauses");
				if reported.contains(&origin) {
					continue;
				}
				reported.push(origin);
				self.report_stricter_bound(
					trait_index,
					(declaration, function),
					origin,
					&failure,
				);
			}
		}
		Ok(holds)
	}

	/// The impl's constant against the trait's `declaration`, with `Self` as
	/// `target`.
	fn compare_constant(
		&mut self,
		trait_index: TraitIdx,
		declaration: ConstIdx,
		constant: ConstIdx,
		target: TypeIndex,
	) -> Result<(), SolverError> {
		let expected_signature = &self.constants[usize::from(declaration)];
		let (expected, declaration_env) =
			(expected_signature.ty, expected_signature.env);
		let signature = &self.constants[usize::from(constant)];
		let (found, env) = (signature.ty, signature.env);
		let expected = self.types.substitute(
			expected,
			Substitution {
				envs: &self.type_envs,
				env: declaration_env,
				args: &[target],
			},
		);
		let expected = self.normalize(
			env,
			expected,
			NormalizationDepth::Deep,
			RewriteFlags::ALL,
		)?;
		let found = self.normalize(
			env,
			found,
			NormalizationDepth::Deep,
			RewriteFlags::ALL,
		)?;
		if expected == found
			|| self.types.has_error(expected)
			|| self.types.has_error(found)
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
		} = *self.ast_node(DefId::Const(declaration))
		else {
			unreachable!("a trait's constant")
		};
		let AstNodeRef::TraitImplConstant {
			item: ast::ImplItem::Constant { ty: Some(ty), .. },
			..
		} = *self.ast_node(DefId::Const(constant))
		else {
			unreachable!("a trait impl's constant with a written type")
		};
		let name = self.defs.constants[usize::from(constant)].name.inner;
		let head = Diagnostic::error()
			.with_code(DiagnosticCode::TraitImplConstTypeMismatch.code())
			.with_message(format!(
				"constant `{}` has an incompatible type for trait `{}`",
				self.strings.resolve(name).unwrap(),
				self.trait_name(trait_index),
			));
		self.report_type_mismatch(
			head,
			(
				self.defs.constants[usize::from(declaration)].file_id,
				WrittenType::Written(expected_ty),
			),
			(
				self.defs.constants[usize::from(constant)].file_id,
				WrittenType::Written(ty),
			),
			(expected, found),
		);
		Ok(())
	}

	/// A function's own type parameters, given the frame it is read in (its
	/// own, or the one its check builds): none when that frame is the
	/// trait's or impl's around it, which a function without its own
	/// parameters is read in.
	fn own_params(&self, frame: TypeEnvIdx) -> &[TypeIndex] {
		match self.type_envs.owner(frame) {
			TypeEnvOwner::Function(_) => self.type_envs.param_types(frame),
			_ => &[],
		}
	}

	/// The written signature of a trait's or a trait impl's function, for
	/// its spans.
	fn function_syntax(
		&self,
		function: FunctionIdx,
	) -> &'ast ast::FunctionSignature {
		match *self.ast_node(DefId::Function(function)) {
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

	fn trait_name(&self, trait_index: TraitIdx) -> &str {
		let name = self.defs.traits[usize::from(trait_index)].name.inner;
		self.strings.resolve(name).unwrap()
	}

	fn expected_found(&self, expected: TypeIndex, found: TypeIndex) -> String {
		let formatter = self.type_formatter();
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
		trait_index: TraitIdx,
		member: MemberKind,
		function: FunctionIdx,
	) -> Diagnostic<FileId> {
		let name = self.defs.functions[usize::from(function)].name.inner;
		Diagnostic::error()
			.with_code(DiagnosticCode::TraitImplSignatureMismatch.code())
			.with_message(format!(
				"{} `{}` has an incompatible signature for trait `{}`",
				member_noun(member),
				self.strings.resolve(name).unwrap(),
				self.trait_name(trait_index),
			))
	}

	fn report_count_mismatch(
		&mut self,
		trait_index: TraitIdx,
		member: MemberKind,
		(declaration, function): (FunctionIdx, FunctionIdx),
		what: &str,
		(expected, found): (usize, usize),
	) {
		let plural = |count: usize| if count == 1 { "" } else { "s" };
		let (expected_def, def) = (
			&self.defs.functions[usize::from(declaration)],
			&self.defs.functions[usize::from(function)],
		);
		let diagnostic = self
			.signature_mismatch(trait_index, member, function)
			.with_label(
				SourceSpan::new(def.file_id, def.name.span)
					.primary_label()
					.with_message(format!(
						"expected {expected} {what}{}, found {found}",
						plural(expected),
					)),
			)
			.with_label(
				SourceSpan::new(expected_def.file_id, expected_def.name.span)
					.secondary_label()
					.with_message(format!(
						"the trait declares {expected} {what}{}",
						plural(expected),
					)),
			);
		self.diagnostics.push(diagnostic);
	}

	/// A parameter's name is part of the trait's contract: a call by name
	/// uses the declaration's names, whichever impl it reaches. So an impl
	/// names a parameter as the trait does, or leaves it unnamed, which binds
	/// no local and changes nothing for callers; it never renames one, nor
	/// names one the trait leaves unnamed. Only the name is compared; whether
	/// its local is `mut` is the body's own.
	fn report_name_mismatch(
		&mut self,
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
		let diagnostic = self
			.signature_mismatch(trait_index, member, function)
			.with_label(
				SourceSpan::new(
					self.defs.functions[usize::from(function)].file_id,
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
					self.defs.functions[usize::from(declaration)].file_id,
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
		self.diagnostics.push(diagnostic);
	}

	/// rustc's E0276: a bound the impl writes on its function's own type
	/// parameter that the trait's declaration does not imply. It is pointed
	/// at as written; the clause that fails is what the label names.
	fn report_stricter_bound(
		&mut self,
		trait_index: TraitIdx,
		(declaration, function): (FunctionIdx, FunctionIdx),
		origin: BoundId,
		failure: &UnsatisfiedClause,
	) {
		let formatter = self.type_formatter();
		let requirement = match *failure {
			UnsatisfiedClause::Trait {
				subject,
				trait_index,
				..
			} => {
				let name =
					self.defs.traits[usize::from(trait_index)].name.inner;
				format!(
					"{}: {}",
					formatter.display_type(subject),
					self.strings.resolve(name).unwrap(),
				)
			}
			UnsatisfiedClause::Equality {
				projection,
				expected,
				..
			} => format!(
				"{} == {}",
				formatter.display_type(projection),
				formatter.display_type(expected),
			),
		};
		let expected_def = &self.defs.functions[usize::from(declaration)];
		let name = self.defs.functions[usize::from(function)].name.inner;
		let diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::ImplStricterThanTrait.code())
			.with_message(format!(
				"impl has stricter requirements than trait `{}`",
				self.trait_name(trait_index),
			))
			.with_label(self.bounds.span(origin).primary_label().with_message(
				format!("impl has extra requirement `{requirement}`"),
			))
			.with_label(
				SourceSpan::new(expected_def.file_id, expected_def.name.span)
					.secondary_label()
					.with_message(format!(
						"definition of `{}` from trait",
						self.strings.resolve(name).unwrap(),
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
		trait_index: TraitIdx,
		member: MemberKind,
		name: Spanned<SymbolU32>,
		at_member: SourceSpan,
	) {
		let trait_name = self.trait_name(trait_index);
		let diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::NotATraitMember.code())
			.with_message(format!(
				"{} `{}` is not a member of trait `{trait_name}`",
				member_noun(member),
				self.strings.resolve(name.inner).unwrap(),
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
		trait_index: TraitIdx,
		declaration: MemberKind,
		member: MemberKind,
		at_member: SourceSpan,
	) {
		let name = self.defs.name(declaration.def_id());
		let trait_def = &self.defs.traits[usize::from(trait_index)];
		let diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::TraitImplItemKindMismatch.code())
			.with_message(format!(
				"`{}` is {} {}, but trait `{}` declares {} {}",
				self.strings.resolve(name.inner).unwrap(),
				article(member),
				member_noun(member),
				self.trait_name(trait_index),
				article(declaration),
				member_noun(declaration),
			))
			.with_label(
				at_member
					.primary_label()
					.with_message("does not match the trait"),
			)
			.with_label(
				SourceSpan::new(trait_def.file_id, name.span)
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
		trait_index: TraitIdx,
		missing: &[Spanned<SymbolU32>],
		at_target: SourceSpan,
	) {
		let names = missing
			.iter()
			.map(|name| {
				format!("`{}`", self.strings.resolve(name.inner).unwrap())
			})
			.collect::<Vec<_>>()
			.join(", ");
		let trait_file = self.defs.traits[usize::from(trait_index)].file_id;
		let mut diagnostic =
			Diagnostic::error()
				.with_code(DiagnosticCode::IncompleteTraitImpl.code())
				.with_message(format!(
					"not all members of trait `{}` are implemented",
					self.trait_name(trait_index),
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
						self.strings.resolve(name.inner).unwrap(),
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
	fn report_type_mismatch(
		&mut self,
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
					.with_message(
						self.expected_found(label_expected, label_found),
					),
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
				self.expected_found(inner_expected, inner_found),
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
	fn written_part(
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
					ast::TypeExpression::Pointer { inner, .. }
					| ast::TypeExpression::Slice { inner, .. }
					| ast::TypeExpression::Array { inner, .. },
					TypePathStep::Pointee | TypePathStep::Element,
				) => Some(&**inner),
				(
					ast::TypeExpression::Array { length, .. },
					TypePathStep::Length,
				) => return (length.span, taken + 1),
				(
					ast::TypeExpression::Pointer { memory, .. }
					| ast::TypeExpression::Slice { memory, .. }
					| ast::TypeExpression::Array { memory, .. },
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
						(SourceSpan::new(file_id, last.ident.span), Tier::Type);
					let spells_its_arguments = self
						.resolutions
						.by_site
						.get(&site)
						.and_then(|referent| match *referent {
							Referent::Definition(key)
							| Referent::Import {
								definition: key, ..
							} => Some(key),
							_ => None,
						})
						.is_some_and(|key| {
							matches!(
								key.symbol_kind(self.defs),
								DefKind::Struct(_) | DefKind::Function(_)
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
					&Type::FunctionRef {
						param: a_param,
						result: a_result,
					},
					&Type::FunctionRef {
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
						memory: a_memory,
						ownership: a,
					},
					&Type::Array {
						of: b_of,
						length: b_length,
						memory: b_memory,
						ownership: b,
					},
				) if a == b => vec![
					(TypePathStep::Element, a_of, b_of),
					(TypePathStep::Length, a_length, b_length),
					(TypePathStep::Memory, a_memory, b_memory),
				],
				(
					&Type::Slice {
						of: a_of,
						memory: a_memory,
						ownership: a,
					},
					&Type::Slice {
						of: b_of,
						memory: b_memory,
						ownership: b,
					},
				) if a == b => vec![
					(TypePathStep::Element, a_of, b_of),
					(TypePathStep::Memory, a_memory, b_memory),
				],
				(
					&Type::AssocTypeProjection {
						trait_index: a_trait,
						assoc_type_index: a,
						base: a_base,
					},
					&Type::AssocTypeProjection {
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
		result: Result<(), SolverError>,
		reference: SourceSpan,
	) -> Result<(), SolverError> {
		match result {
			Ok(()) | Err(SolverError::Poisoned) => Ok(()),
			Err(SolverError::Cycle(cycle)) => {
				let diagnostic = self.cycle_diagnostic(&cycle, reference);
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

#[cfg(test)]
mod tests {
	use codespan_reporting::diagnostic::Diagnostic;
	use indoc::indoc;

	use super::*;
	use crate::ast::StringInterner;
	use crate::diagnostics::DiagnosticCode;
	use crate::testing::DiagnosticView;
	use crate::tir::defs::{AstEntry, DefinitionRegistry};
	use crate::tir::impls::ImplDispatch;
	use crate::tir::resolutions::NameResolutions;
	use crate::tir::solver::Solver;
	use crate::vfs::{self, FileId, Files};

	/// `test_case!(case = "source")` declares the graph, the inputs and the
	/// swept `TestCase` borrowing them as three locals of the calling test.
	/// The source plays the stdlib's role, so it declares the primitives and
	/// traits it uses.
	macro_rules! test_case {
		($case:ident = $source:expr $(,)?) => {
			let mut graph = source_graph($source);
			let mut inputs = TestInputs::new(&mut graph);
			let $case = TestCase::new(&mut inputs);
		};
	}

	fn source_graph(source: &str) -> vfs::CompilationUnit {
		let mut builder = vfs::CompilationUnitBuilder::new();
		let root_id = builder
			.load_binary(
				vfs::AbsolutePath::new("/main.wx"),
				&vfs::VirtualFileSource::from_relative(
					std::collections::HashMap::from([(
						"main.wx".to_string(),
						source.to_string(),
					)]),
				),
			)
			.unwrap();
		builder.set_stdlib(root_id);
		builder.build(root_id)
	}

	/// Everything a `TypeContext` borrows, kept on the test's stack.
	struct TestInputs<'g> {
		files: &'g Files,
		strings: &'g mut StringInterner,
		defs: DefinitionRegistry,
		ast_nodes: Vec<AstEntry<'g>>,
		impl_dispatch: ImplDispatch,
		diagnostics: Vec<Diagnostic<FileId>>,
		resolutions: NameResolutions,
		solver: Solver,
	}

	impl<'g> TestInputs<'g> {
		fn new(graph: &'g mut vfs::CompilationUnit) -> Self {
			let vfs::CompilationUnit {
				files,
				packages,
				strings,
				stdlib_package,
				root_package,
			} = graph;
			let mut diagnostics = Vec::new();
			let mut resolutions = NameResolutions::default();
			let (defs, ast_nodes) = DefinitionRegistry::build(
				packages,
				files,
				strings,
				&mut diagnostics,
				&mut resolutions,
				*stdlib_package,
				*root_package,
			);
			let impl_dispatch = ImplDispatch::build(
				&mut diagnostics,
				&mut resolutions,
				strings,
				&defs,
				&ast_nodes,
			);
			let solver = Solver::new(defs.constants.len());
			Self {
				files,
				strings,
				defs,
				ast_nodes,
				impl_dispatch,
				diagnostics,
				resolutions,
				solver,
			}
		}
	}

	/// A swept `TypeContext` over `TestInputs`.
	struct TestCase<'a> {
		context: TypeContext<'a, 'a, 'a>,
	}

	impl<'a> TestCase<'a> {
		fn new(inputs: &'a mut TestInputs<'_>) -> Self {
			let TestInputs {
				files,
				strings,
				defs,
				ast_nodes,
				impl_dispatch,
				diagnostics,
				resolutions,
				solver,
			} = inputs;
			let mut context = TypeContext::new(
				diagnostics,
				resolutions,
				strings,
				solver,
				files,
				defs,
				ast_nodes,
				impl_dispatch,
			);
			context.sweep();
			Self { context }
		}

		fn diagnostics(&self) -> DiagnosticView<'_> {
			DiagnosticView::new(
				"conformance",
				self.context.diagnostics,
				self.context.files,
			)
		}
	}

	#[test]
	fn an_associated_type_value_satisfies_its_declared_bound() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u32;
			trait Size {}
			impl Size for u32 {}
			trait Container { type Item: Size; }
			struct Bag();
			impl Container for Bag { type Item = u32; }
		"}
		);
		case.diagnostics().assert_none();
	}

	#[test]
	fn an_associated_type_value_violating_its_declared_bound_is_reported() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8;
			trait Size {}
			trait Container { type Item: Size; }
			struct Bag();
			impl Container for Bag { type Item = u8; }
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics()
			.assert_error_saying("the trait bound `u8: Size` is not satisfied");
	}

	#[test]
	fn an_inherited_default_is_checked_against_the_bound_per_impl() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8;
			trait Size {}
			trait Container { type Item: Size = u8; }
			struct Bag();
			impl Container for Bag {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
	}

	/// A target that does not resolve leaves nothing to prove supertraits
	/// for, but a value's bound does not depend on it.
	#[test]
	fn an_impl_of_an_unresolved_target_still_checks_its_values() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8;
			trait Size {}
			trait Container: Size { type Item: Size; func f(self: Self); }
			impl Container for Missing { type Item = u8; func f(self: Self) {} }
		"}
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::UndeclaredIdentifier,
			DiagnosticCode::TraitBoundViolation,
		]);
		case.diagnostics()
			.assert_error_saying("the trait bound `u8: Size` is not satisfied");
	}

	#[test]
	fn a_value_naming_an_impl_parameter_needs_the_parameter_bounded() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Size {}
			trait Container { type Item: Size; }
			struct Bounded<T>();
			struct Unbounded<T>();
			impl<T: Size> Container for Bounded<T> { type Item = T; }
			impl<T> Container for Unbounded<T> { type Item = T; }
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics()
			.assert_error_saying("the trait bound `T: Size` is not satisfied");
	}

	#[test]
	fn a_nested_equality_on_an_associated_type_is_proved_for_the_value() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8;
			type u32;
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
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::AssocTypeEqualityMismatch]);
	}

	#[test]
	fn an_impl_requires_its_traits_supertraits() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Base {}
			trait Derived: Base {}
			struct Both();
			struct Only();
			impl Base for Both {}
			impl Derived for Both {}
			impl Derived for Only {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics().assert_error_saying(
			"the trait bound `Only: Base` is not satisfied",
		);
	}

	#[test]
	fn a_generic_impl_proves_its_supertraits_with_its_own_bounds() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			trait Marker {}
			trait Base {}
			trait Derived: Base {}
			struct W<T>();
			struct V<T>();
			impl<T: Marker> Base for W<T> {}
			impl<T: Marker> Derived for W<T> {}
			impl<T: Marker> Base for V<T> {}
			impl<T> Derived for V<T> {}
		"}
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitBoundViolation]);
		case.diagnostics().assert_error_saying(
			"the trait bound `V<T>: Base` is not satisfied",
		);
	}

	#[test]
	fn a_supertraits_binding_is_proved_for_the_target() {
		test_case!(
			case = indoc! {"
			pub trait Call { type Args; type Result; } pub trait Function: Call {}
			type u8;
			type u32;
			trait Base { type Out; }
			trait Derived: Base where { Out = u32 } {}
			struct Good();
			struct Bad();
			impl Base for Good { type Out = u32; }
			impl Derived for Good {}
			impl Base for Bad { type Out = u8; }
			impl Derived for Bad {}
		"}
		);
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
		pub trait Call { type Args; type Result; } pub trait Function: Call {}
		type u8; type u16; type u32; type u64;
		struct Box<T>();
	";

	#[test]
	fn an_impl_that_keeps_the_contract_reports_nothing() {
		let source = format!(
			"{PRELUDE}{}",
			indoc! {"
			trait Store {
				type Item;
				func get(self: Self) -> Box<Self::Item>;
				func put(self: Self, item: Self::Item, at: u32);
				func swap<A, B>(a: A, b: B) -> (B, A);
				func kept(self: Self) -> u32 { 0 }
				const ZERO: Self;
			}
			struct Bag<T>();
			impl<T> Store for Bag<T> {
				type Item = T;
				func get(self: Self) -> Box<T> { Box() }
				func put(self: Self, mut item: T, at: u32) {}
				func swap<X, Y>(a: X, b: Y) -> (Y, X) { (b, a) }
				const ZERO: Bag<T> = Bag();
			}
		"}
		);
		test_case!(case = &source);
		case.diagnostics().assert_none();
	}

	#[test]
	fn a_declaration_without_a_default_must_be_provided() {
		test_case!(
			case = &format!(
				"{PRELUDE}{}",
				indoc! {"
				trait Store {
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
			)
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::IncompleteTraitImpl]);
		assert_eq!(
			case.context.diagnostics[0].labels[0].message,
			"missing `Item`, `get`, `N` in implementation"
		);
	}

	#[test]
	fn a_member_of_another_kind_does_not_provide_its_declaration() {
		test_case!(
			case = &format!(
				"{PRELUDE}{}",
				indoc! {"
				trait Store { func size() -> u32; type Item; }
				struct Bag();
				impl Store for Bag { const size: u32 = 0; func Item() {} }
			"}
			)
		);
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
		test_case!(
			case = &format!(
				"{PRELUDE}{}",
				indoc! {"
				trait Store { func size() -> u32 { 0 } }
				struct Bag();
				impl Store for Bag { type size = u32; }
			"}
			)
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitImplItemKindMismatch]);
	}

	#[test]
	fn a_member_the_trait_does_not_declare_is_reported() {
		test_case!(
			case = &format!(
				"{PRELUDE}{}",
				indoc! {"
				trait Store {}
				struct Bag();
				impl Store for Bag { func extra() {} type Extra = u8; }
			"}
			)
		);
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
			trait Store {
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
		test_case!(case = &source);
		// `named` and `bare` leave the trait's name unbound, which keeps the
		// contract.
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TraitImplSignatureMismatch,
			DiagnosticCode::TraitImplSignatureMismatch,
			DiagnosticCode::TraitImplSignatureMismatch,
		]);
		let [renamed, unnamed, receiver] = &case.context.diagnostics[..] else {
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
		test_case!(
			case = &format!(
				"{PRELUDE}{}",
				indoc! {"
				trait Store {
					func generic<T>(x: T);
					func arity(self: Self, a: u32);
				}
				struct Bag();
				impl Store for Bag {
					func generic<T, U>(x: T) {}
					func arity(self: Self) {}
				}
			"}
			)
		);
		case.diagnostics().assert_codes(&[
			DiagnosticCode::TraitImplSignatureMismatch,
			DiagnosticCode::TraitImplSignatureMismatch,
		]);
		assert_eq!(
			case.context.diagnostics[0].labels[0].message,
			"expected 1 type parameter, found 2"
		);
		assert_eq!(
			case.context.diagnostics[1].labels[0].message,
			"expected 2 parameters, found 1"
		);
	}

	#[test]
	fn own_type_parameters_correspond_by_position() {
		test_case!(
			case = &format!(
				"{PRELUDE}{}",
				indoc! {"
				trait Store { func pair<A, B>(a: A, b: B); }
				struct Bag();
				impl Store for Bag { func pair<A, B>(a: B, b: A) {} }
			"}
			)
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitImplSignatureMismatch]);
		assert_eq!(
			case.context.diagnostics[0].labels[0].message,
			"expected `A`, found `B`"
		);
	}

	#[test]
	fn a_difference_is_pointed_at_where_each_side_writes_it() {
		let source = format!(
			"{PRELUDE}{}",
			indoc! {"
			trait Store { func put(self: Self, slot: Box<(u8, u32)>); }
			struct Bag();
			impl Store for Bag { func put(self: Self, slot: Box<(u8, u64)>) {} }
		"}
		);
		test_case!(case = &source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitImplSignatureMismatch]);
		let diagnostic = &case.context.diagnostics[0];
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
			trait Store { type Item; func get(self: Self) -> Box<Self::Item>; }
			struct Bag();
			impl Store for Bag { type Item = u8; func get(self: Self) -> Box<u16> { Box() } }
		"}
		);
		test_case!(case = &source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitImplSignatureMismatch]);
		let diagnostic = &case.context.diagnostics[0];
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
			trait Store { func put(self: Self, slot: Box<(u8, u32)>); }
			struct Bag();
			impl Store for Bag { func put(self: Self, slot: Alias) {} }
		"}
		);
		test_case!(case = &source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitImplSignatureMismatch]);
		let diagnostic = &case.context.diagnostics[0];
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
			trait Store { func count(self: Self) -> u32; }
			struct Bag();
			impl Store for Bag { func count(self: Self) {} }
		"}
		);
		test_case!(case = &source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitImplSignatureMismatch]);
		let diagnostic = &case.context.diagnostics[0];
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
		test_case!(case = &source);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::TraitImplConstTypeMismatch]);
		case.diagnostics().assert_error_saying(
			"constant `N` has an incompatible type for trait `Store`",
		);
		assert_eq!(labelled(&source, &case.context.diagnostics[0], 0), "u64");
	}

	const ORDERING: &str = "
		trait PartialEq {}
		trait PartialOrd: PartialEq {}
		trait Eq: PartialEq {}
		trait Ord: PartialOrd + Eq {}
		trait Container { type Item; }
		struct Bag();
	";

	#[test]
	fn an_impl_function_may_require_less_than_or_as_much_as_its_trait() {
		test_case!(
			case = &format!(
				"{PRELUDE}{ORDERING}{}",
				indoc! {"
				trait Sorter {
					func fewer<T: PartialEq>(x: T);
					func same<T: PartialOrd>(x: T);
					func implied<T: Ord>(x: T);
				}
				impl Sorter for Bag {
					func fewer<T>(x: T) {}
					func same<T: PartialOrd>(x: T) {}
					func implied<T: PartialEq>(x: T) {}
				}
			"}
			)
		);
		case.diagnostics().assert_none();
	}

	#[test]
	fn a_stricter_bound_is_reported_once_where_it_is_written() {
		let source = format!(
			"{PRELUDE}{ORDERING}{}",
			indoc! {"
			trait Sorter { func sort<T: PartialEq>(x: T); }
			impl Sorter for Bag { func sort<T: Ord>(x: T) {} }
		"}
		);
		test_case!(case = &source);
		// `Ord` brings `PartialOrd` and `Eq`, which do not follow either; the
		// written bound is the one report.
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::ImplStricterThanTrait]);
		case.diagnostics().assert_error_saying(
			"impl has stricter requirements than trait `Sorter`",
		);
		let diagnostic = &case.context.diagnostics[0];
		assert_eq!(labelled(&source, diagnostic, 0), "Ord");
		assert_eq!(
			diagnostic.labels[0].message,
			"impl has extra requirement `T: Ord`"
		);
		assert_eq!(labelled(&source, diagnostic, 1), "sort");
	}

	#[test]
	fn an_extra_equality_is_a_stricter_requirement() {
		test_case!(
			case = &format!(
				"{PRELUDE}{ORDERING}{}",
				indoc! {"
				trait Store { func take<U: Container>(x: U); }
				impl Store for Bag {
					func take<U: Container where { Item = u32 }>(x: U) {}
				}
			"}
			)
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::ImplStricterThanTrait]);
		assert_eq!(
			case.context.diagnostics[0].labels[0].message,
			"impl has extra requirement `<U as Container>::Item == u32`"
		);
	}

	#[test]
	fn a_conflicting_equality_is_a_stricter_requirement() {
		test_case!(
			case = &format!(
				"{PRELUDE}{ORDERING}{}",
				indoc! {"
				trait Store { func take<U: Container where { Item = u8 }>(x: U); }
				impl Store for Bag {
					func take<U: Container where { Item = u16 }>(x: U) {}
				}
			"}
			)
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::ImplStricterThanTrait]);
		assert_eq!(
			case.context.diagnostics[0].labels[0].message,
			"impl has extra requirement `<U as Container>::Item == u16`"
		);
	}

	/// A bound nested on a projection is proved like one on the parameter:
	/// `Item: PartialEq` follows from the trait's `Item: Ord`, `Item: Ord`
	/// follows from nothing.
	#[test]
	fn a_nested_bound_is_proved_from_the_traits() {
		test_case!(
			case = &format!(
				"{PRELUDE}{ORDERING}{}",
				indoc! {"
				trait Store {
					func strict<U: Container>(x: U);
					func loose<U: Container where { Item: Ord }>(x: U);
				}
				impl Store for Bag {
					func strict<U: Container where { Item: Ord }>(x: U) {}
					func loose<U: Container where { Item: PartialEq }>(x: U) {}
				}
			"}
			)
		);
		case.diagnostics()
			.assert_codes(&[DiagnosticCode::ImplStricterThanTrait]);
		assert_eq!(
			case.context.diagnostics[0].labels[0].message,
			"impl has extra requirement `<U as Container>::Item: Ord`"
		);
	}

	#[test]
	fn self_in_a_declarations_bound_is_the_impls_target() {
		test_case!(
			case = &format!(
				"{PRELUDE}{ORDERING}{}",
				indoc! {"
				trait Into { type Out; }
				trait Convert { func from<T: Into where { Out = Self }>(x: T); }
				impl Convert for Bag {
					func from<T: Into where { Out = Bag }>(x: T) {}
				}
			"}
			)
		);
		case.diagnostics().assert_none();
	}

	#[test]
	fn a_signature_is_compared_under_the_traits_assumptions() {
		test_case!(
			case = &format!(
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
			)
		);
		// Both read `U::Item` as `u32`, the trait's equality, though the impl
		// does not repeat it.
		case.diagnostics().assert_none();
	}
}
