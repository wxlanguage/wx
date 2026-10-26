//! Members of a type: paths through one, `Ordering::of(a, b)`, `Self::f`,
//! `T::f`, `W::<u8>::new`, `<T>::f`, and `<T as Trait>::f`, which searches
//! only the trait it names.
//!
//! A member is looked up by name on its receiver type
//! (`resolve_applicable_member`): an inherent impl's first, then the traits the
//! receiver implements. A function the lookup selects is called directly when
//! it is known, an inherent function or the member a concrete trait impl
//! defines, with the impl's arguments leading its own. A trait's declaration,
//! for an abstract receiver or an impl that inherits the default, is called
//! with the receiver as `Self`, and its impl is selected at monomorphization.
//!
//! An inherent member is as visible as it is written; a trait's member is as
//! visible as the trait.

use codespan_reporting::diagnostic::{Diagnostic, Label};

use super::calls::{Callee, Dispatch};
use super::{Arguments, BodyContext};
use crate::ast::{self, Spanned};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::tir::body::{ExprIdx, ExprKind};
use crate::tir::defs::{
	BindingKey, ConstIdx, DefKind, MemberKind, Tier, TraitIdx, Visibility,
};
use crate::tir::impls::ImplTarget;
use crate::tir::members::{
	ApplicableMember, MemberLookup, TraitImplLookup, TraitMemberSelection,
	report_ambiguous_type_member,
};
use crate::tir::resolutions::Referent;
use crate::tir::satisfaction::{
	TypeArgsNotAllowedOn, report_type_args_not_allowed,
};
use crate::tir::signatures::InferPolicy;
use crate::tir::solver::SolverError;
use crate::tir::types::{Substitution, Type, TypeIndex};

/// A member of a type a path names.
pub(super) struct MemberPath<'s> {
	/// The type the segments before `member` name.
	receiver: TypeIndex,
	member: &'s ast::PathSegment,
	/// The trait a `<T as Trait>::member` root names, the only one searched.
	qualified: Option<TraitIdx>,
}

impl<'s> MemberPath<'s> {
	pub(super) fn new(
		receiver: TypeIndex,
		member: &'s ast::PathSegment,
	) -> Self {
		Self {
			receiver,
			member,
			qualified: None,
		}
	}
}

/// What a member path selects.
enum Member {
	/// A function without `self`.
	Function(Callee),
	/// A function taking `self`.
	Method(Callee),
	/// A constant, with its flat type arguments: the impl's, or `Self` for a
	/// trait's declaration (a constant has no parameters of its own).
	Constant {
		constant: ConstIdx,
		type_args: Box<[TypeIndex]>,
	},
}

impl BodyContext<'_, '_, '_, '_> {
	/// `<T as Trait>::member` or `<T>::member`: a member of the bracketed
	/// type. Only one segment may follow a trait-qualified root.
	pub(super) fn resolve_rooted_path<'s>(
		&mut self,
		expr: &'s Spanned<ast::Expression>,
	) -> Result<MemberPath<'s>, ExprIdx> {
		let path = match &expr.inner {
			ast::Expression::Grouped { inner, segments } => {
				let (member, prefix) = segments.split_last().unwrap();
				let root = self.cx.resolve_type(
					&mut self.obligations.types,
					self.scope,
					inner,
					InferPolicy::Allow,
				);
				let receiver = self.cx.resolve_type_member_path(
					&mut self.obligations.types,
					self.scope,
					root,
					prefix,
					InferPolicy::Allow,
				);
				MemberPath::new(receiver, member)
			}
			ast::Expression::QualifiedPath { root, segments } => {
				let [member] = &**segments else {
					return Err(self.unsupported(
						expr.span,
						"a path past a trait-qualified member",
					));
				};
				let receiver = self.cx.resolve_type(
					&mut self.obligations.types,
					self.scope,
					&root.self_type,
					InferPolicy::Allow,
				);
				let qualified = self.cx.resolve_trait_bound_path(
					self.scope.file_id,
					self.scope.namespace,
					&root.trait_path,
				);
				let Some(qualified) = qualified else {
					return Err(self.body.push(
						ExprKind::Error,
						TypeIndex::ERROR,
						expr.span,
					));
				};
				return Ok(MemberPath {
					receiver,
					member,
					qualified: Some(qualified),
				});
			}
			_ => unreachable!("only a bracketed root starts a rooted path"),
		};
		Ok(path)
	}

	/// `Type::member` without a call: a function as a value, which needs its
	/// own type arguments written.
	pub(super) fn build_member_value(
		&mut self,
		path: MemberPath<'_>,
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		match self.select_member(&path) {
			Some(Member::Function(callee) | Member::Method(callee)) => {
				self.build_function_value(callee, path.member, expected, span)
			}
			Some(Member::Constant {
				constant,
				type_args,
			}) => self.build_constant(constant, &type_args, path.member, span),
			None => self.body.push(ExprKind::Error, TypeIndex::ERROR, span),
		}
	}

	/// `Type::CONSTANT`: a known constant's value, or a trait's declaration
	/// of it for an abstract receiver or an impl inheriting its default.
	fn build_constant(
		&mut self,
		constant: ConstIdx,
		type_args: &[TypeIndex],
		member: &ast::PathSegment,
		span: TextSpan,
	) -> ExprIdx {
		let (kind, ty) = self.constant_value(constant, type_args, member);
		self.body.push(kind, ty, span)
	}

	/// `Type::CONSTANT` in a pattern: the constant the member selects, as
	/// `ExprKind::Const` or `ExprKind::AbstractConst`, with its type. `None`
	/// when it selects nothing or is not a constant (reported).
	pub(super) fn select_constant(
		&mut self,
		path: MemberPath<'_>,
	) -> Option<(ExprKind, TypeIndex)> {
		match self.select_member(&path)? {
			Member::Constant {
				constant,
				type_args,
			} => Some(self.constant_value(constant, &type_args, path.member)),
			Member::Function(_) | Member::Method(_) => {
				let name = self.cx.strings.resolve(path.member.ident.inner);
				self.cx.diagnostics.push(
					Diagnostic::error()
						.with_code(DiagnosticCode::InvalidMatchPattern.code())
						.with_message(format!(
							"expected a constant, found function `{}`",
							name.unwrap()
						))
						.with_label(Label::primary(
							self.scope.file_id,
							path.member.ident.span,
						))
						.with_note("a pattern compares with constants"),
				);
				None
			}
		}
	}

	/// A selected constant's node kind and type: the declared type, with the
	/// impl's arguments, or the receiver as `Self`.
	fn constant_value(
		&mut self,
		constant: ConstIdx,
		type_args: &[TypeIndex],
		member: &ast::PathSegment,
	) -> (ExprKind, TypeIndex) {
		if !member.type_args.is_empty() {
			self.cx.diagnostics.push(report_type_args_not_allowed(
				self.cx.strings,
				self.cx.defs,
				self.scope.file_id,
				member,
				TypeArgsNotAllowedOn::Declaration(DefKind::Const(constant)),
			));
		}
		let signature = &self.cx.constants[usize::from(constant)];
		debug_assert_eq!(
			self.cx.type_envs.generic_count(signature.env),
			type_args.len()
		);
		let ty = self.cx.types.substitute(
			signature.ty,
			Substitution {
				envs: &self.cx.type_envs,
				env: signature.env,
				args: type_args,
			},
		);
		let ty = self.normalized(ty, self.scope.env);
		let ty = self.cx.types.collapse_error(ty);
		let owner = self.cx.defs.constants[usize::from(constant)].owner;
		let type_args = self.cx.types.push_list(type_args);
		let kind = match Dispatch::of(owner) {
			Dispatch::Direct => ExprKind::Const {
				constant,
				type_args,
			},
			Dispatch::Abstract => ExprKind::AbstractConst {
				constant,
				type_args,
			},
		};
		(kind, ty)
	}

	/// `Type::member(a, b)` or `Type::member({ b, a })`: a call of the
	/// function the member selects. A method is called like any function
	/// here, its receiver the first argument, named `self` in a call by name.
	pub(super) fn build_member_call(
		&mut self,
		path: MemberPath<'_>,
		callee_span: TextSpan,
		arguments: Arguments<'_>,
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		match self.select_member(&path) {
			Some(Member::Function(callee) | Member::Method(callee)) => self
				.build_function_call(
					callee,
					path.member,
					None,
					arguments,
					expected,
					span,
				),
			Some(Member::Constant {
				constant,
				type_args,
			}) => {
				let callee = self.build_constant(
					constant,
					&type_args,
					path.member,
					callee_span,
				);
				self.build_value_call(callee, arguments, span)
			}
			None => self.body.push(ExprKind::Error, TypeIndex::ERROR, span),
		}
	}

	/// `receiver.method(a, b)` or `receiver.method({ b, a })`: a call of the
	/// method the receiver's type has, the receiver its first argument. A pointer is not dereferenced: a
	/// method of the pointee is found only when it takes `self` by pointer,
	/// as `self: Mem::*Self` does, and the pointer itself is then `self`.
	pub(super) fn build_method_call(
		&mut self,
		object: &Spanned<ast::Expression>,
		method: &ast::PathSegment,
		arguments: Arguments<'_>,
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let receiver = self.build(object, TypeIndex::INFER);
		let receiver_ty = self.body.ty(receiver);
		if self.cx.types.has_untyped(receiver_ty) {
			self.report_annotation_required(receiver);
			return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
		}
		let receiver_ty = self.normalized(receiver_ty, self.scope.env);
		let pointee = match *self.cx.types.resolve(receiver_ty) {
			Type::Pointer { to, .. } => Some(to),
			_ => None,
		};
		let path = MemberPath::new(pointee.unwrap_or(receiver_ty), method);
		let callee = match self.select_member(&path) {
			Some(Member::Method(callee)) => callee,
			Some(Member::Function(_) | Member::Constant { .. }) => {
				self.report_not_a_method(receiver_ty, method);
				return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
			}
			None => {
				return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
			}
		};
		if pointee.is_some() {
			let params =
				self.cx.functions[usize::from(callee.function)].param_types;
			let declared = self.cx.types.list(params)[0];
			if !matches!(self.cx.types.resolve(declared), Type::Pointer { .. })
			{
				self.report_by_value_through_pointer(receiver_ty, method);
				return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
			}
		}
		self.build_function_call(
			callee,
			method,
			Some(receiver),
			arguments,
			expected,
			span,
		)
	}

	/// The value member `member` names on `receiver`, recorded as what the
	/// name refers to. `None` when there is none (reported) or the receiver
	/// is already an error.
	fn select_member(&mut self, path: &MemberPath<'_>) -> Option<Member> {
		let MemberPath {
			receiver,
			member,
			qualified,
		} = *path;
		if receiver == TypeIndex::ERROR {
			return None;
		}
		let reference = SourceSpan::new(self.scope.file_id, member.ident.span);
		let key = BindingKey::value(member.ident.inner);
		// The impl's arguments, learned from a receiver with arguments still
		// unknown; the call proves its bounds once it knows them.
		let mut learned = None;
		let lookup = match qualified {
			// The named trait alone is searched; that the receiver implements
			// it is checked, and reported, here.
			Some(trait_index) => {
				let found = self.cx.resolve_trait_qualified_value(
					&mut self.obligations.types,
					self.scope.env,
					receiver,
					trait_index,
					member.ident,
					self.scope.file_id,
				);
				match found {
					Ok(found) => MemberLookup::Found(found),
					Err(()) => MemberLookup::Error,
				}
			}
			None if self.cx.types.has_infer(receiver) => {
				let (found, impl_args) =
					self.select_inherent_with_holes(receiver, key, member)?;
				learned = Some(impl_args);
				MemberLookup::Found(found)
			}
			None => self.cx.resolve_applicable_member(
				self.scope.env,
				receiver,
				key,
				reference,
			),
		};
		let found = match lookup {
			MemberLookup::Found(found) => found,
			MemberLookup::Error => return None,
			MemberLookup::Stuck(error) => {
				match error {
					SolverError::Overflow => {
						self.cx
							.diagnostics
							.push(self.cx.overflow_diagnostic(reference));
					}
					SolverError::Cycle(cycle) => {
						self.cx
							.diagnostics
							.push(self.cx.cycle_diagnostic(&cycle, reference));
					}
					_ => {}
				}
				return None;
			}
			MemberLookup::Pending => {
				unreachable!("every signature is final when bodies are checked")
			}
			MemberLookup::NotFound => {
				self.report_no_member(receiver, member);
				return None;
			}
			MemberLookup::Ambiguous(candidates) => {
				self.cx.diagnostics.push(report_ambiguous_type_member(
					self.scope.file_id,
					self.cx.strings,
					self.cx.defs,
					member.ident,
					&candidates,
				));
				return None;
			}
		};
		self.cx.resolutions.by_site.insert(
			(reference, Tier::Value),
			Referent::Member(found.selected_kind(self.cx.defs)),
		);
		self.check_member_access(found, key, member);
		let receiver = self.normalized(receiver, self.scope.env);
		// The impl's arguments, and whether the selection proved them; a
		// trait's declaration is selected over `[Self]` instead.
		let (kind, impl_args, proven) = match found {
			ApplicableMember::Inherent { kind, .. }
				if let Some(impl_args) = learned =>
			{
				(kind, Some(impl_args), false)
			}
			ApplicableMember::Inherent { impl_index, kind } => {
				let header = self.cx.inherent_impls[usize::from(impl_index)]
					.as_ref()
					.expect("a selected impl has a header");
				// The lookup matched this impl's target to the receiver.
				let leading = self
					.cx
					.types
					.match_impl_target(
						header.target.inner,
						receiver,
						&self.cx.type_envs,
						header.type_params,
					)
					.expect("the selected impl's target matches the receiver");
				(kind, Some(leading), true)
			}
			ApplicableMember::TraitImplMember {
				trait_index,
				impl_index,
				declaration,
			} => match self.cx.defs.select_trait_member(impl_index, declaration)
			{
				TraitMemberSelection::Impl(kind) => {
					let Ok(Some(TraitImplLookup::Concrete { args, .. })) =
						self.cx.find_trait_impl_query(
							self.scope.env,
							receiver,
							trait_index,
						)
					else {
						unreachable!("the lookup selected this impl")
					};
					(kind, Some(args), true)
				}
				TraitMemberSelection::TraitDeclaration(declaration) => {
					(declaration, None, true)
				}
			},
			ApplicableMember::AbstractTraitMember { declaration, .. } => {
				(declaration, None, true)
			}
		};
		let leading = impl_args
			.as_deref()
			.unwrap_or(std::slice::from_ref(&receiver));
		let proven = if proven { leading.len() } else { 0 };
		Some(match kind {
			MemberKind::Function(function) => Member::Function(Callee::new(
				self.cx, function, leading, proven,
			)),
			MemberKind::Method(function) => {
				Member::Method(Callee::new(self.cx, function, leading, proven))
			}
			MemberKind::Constant(constant) => Member::Constant {
				constant,
				type_args: impl_args.unwrap_or_else(|| Box::from([receiver])),
			},
			MemberKind::AssociatedType(_) => {
				unreachable!("a value lookup finds no associated type")
			}
		})
	}

	/// The inherent member `key` of `receiver`, a type whose arguments are
	/// partly unknown (`Layout<_>`), and the impl's arguments as far as the
	/// receiver gives them. An impl is a candidate when its target, with what
	/// the receiver teaches its parameters, still meets the receiver; its
	/// bounds wait for the call, which learns the rest. Trait members are not
	/// looked up on such a receiver yet.
	fn select_inherent_with_holes(
		&mut self,
		receiver: TypeIndex,
		key: BindingKey,
		member: &ast::PathSegment,
	) -> Option<(ApplicableMember, Box<[TypeIndex]>)> {
		let Some(target) =
			ImplTarget::from_type(self.cx.types.resolve(receiver))
		else {
			self.report_no_member(receiver, member);
			return None;
		};
		let impl_dispatch = self.cx.impl_dispatch;
		let mut candidates = Vec::new();
		for &impl_index in impl_dispatch.inherent_candidates(target) {
			let impl_def =
				&self.cx.defs.inherent_impls[usize::from(impl_index)];
			let Some(&member_index) = impl_def.bindings.get(&key) else {
				continue;
			};
			let kind = impl_def.members[usize::from(member_index)].kind;
			let Some(header) = &self.cx.inherent_impls[usize::from(impl_index)]
			else {
				continue;
			};
			let (env, pattern) = (header.type_params, header.target.inner);
			let count = self.cx.type_envs.generic_count(env);
			let mut impl_args =
				vec![TypeIndex::INFER; count].into_boxed_slice();
			self.cx.types.learn(
				&self.cx.type_envs,
				env,
				&mut impl_args,
				pattern,
				receiver,
			);
			let instantiated = self.cx.types.substitute(
				pattern,
				Substitution {
					envs: &self.cx.type_envs,
					env,
					args: &impl_args,
				},
			);
			if self.cx.types.meet(instantiated, receiver).is_some() {
				candidates.push((impl_index, kind, impl_args));
			}
		}
		// A type's inherent impls declare a name once between them, so a
		// second candidate is a duplicate already reported.
		if candidates.len() > 1 {
			return None;
		}
		let Some((impl_index, kind, impl_args)) = candidates.pop() else {
			let is_trait_member = impl_dispatch
				.trait_candidates(target)
				.iter()
				.any(|&(trait_index, _)| {
					self.cx
						.defs
						.declared_trait_member(trait_index, key)
						.is_some()
				});
			if is_trait_member {
				self.report_unsupported(
					member.ident.span,
					"a trait member of a type without its type arguments",
				);
			} else {
				self.report_no_member(receiver, member);
			}
			return None;
		};
		Some((ApplicableMember::Inherent { impl_index, kind }, impl_args))
	}

	/// Reports a member not visible here: an inherent member by its own
	/// visibility, a trait's by the trait's.
	fn check_member_access(
		&mut self,
		found: ApplicableMember,
		key: BindingKey,
		member: &ast::PathSegment,
	) {
		let defs = self.cx.defs;
		let (namespace, visibility) = match found {
			ApplicableMember::Inherent { impl_index, .. } => {
				let impl_def = &defs.inherent_impls[usize::from(impl_index)];
				let index = impl_def.bindings[&key];
				(
					impl_def.namespace,
					impl_def.members[usize::from(index)].visibility,
				)
			}
			ApplicableMember::TraitImplMember { trait_index, .. }
			| ApplicableMember::AbstractTraitMember { trait_index, .. } => {
				let trait_def = &defs.traits[usize::from(trait_index)];
				(trait_def.namespace, Visibility::from(trait_def.pub_span))
			}
		};
		if defs.namespaces.is_accessible_from(
			self.scope.namespace,
			namespace.into(),
			visibility,
		) {
			return;
		}
		let noun = member_noun(found.selected_kind(defs));
		let name = self.cx.strings.resolve(member.ident.inner).unwrap();
		self.cx.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::PrivateItem.code())
				.with_message(format!("{noun} `{name}` is private"))
				.with_label(
					Label::primary(self.scope.file_id, member.ident.span)
						.with_message(format!("private {noun}")),
				),
		);
	}

	fn report_no_member(
		&mut self,
		receiver: TypeIndex,
		member: &ast::PathSegment,
	) {
		let name = self.cx.strings.resolve(member.ident.inner).unwrap();
		let receiver = self.cx.type_formatter().display_type(receiver);
		self.cx.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::MethodNotFound.code())
				.with_message(format!(
					"no function or constant named `{name}` found for type \
					 `{receiver}`"
				))
				.with_label(Label::primary(
					self.scope.file_id,
					member.ident.span,
				)),
		);
	}
}

impl BodyContext<'_, '_, '_, '_> {
	fn report_not_a_method(
		&mut self,
		receiver: TypeIndex,
		method: &ast::PathSegment,
	) {
		let name = self.cx.strings.resolve(method.ident.inner).unwrap();
		let receiver = self.cx.type_formatter().display_type(receiver);
		self.cx.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::NotAMethod.code())
				.with_message(format!(
					"`{name}` of `{receiver}` does not take `self`, so it is \
					 not a method"
				))
				.with_label(Label::primary(
					self.scope.file_id,
					method.ident.span,
				))
				.with_note(format!(
					"call it through its type: `{receiver}::{name}(..)`"
				)),
		);
	}

	fn report_by_value_through_pointer(
		&mut self,
		receiver: TypeIndex,
		method: &ast::PathSegment,
	) {
		let name = self.cx.strings.resolve(method.ident.inner).unwrap();
		let receiver = self.cx.type_formatter().display_type(receiver);
		self.cx.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::MethodNotFound.code())
				.with_message(format!(
					"no method `{name}` takes a `{receiver}` receiver"
				))
				.with_label(Label::primary(
					self.scope.file_id,
					method.ident.span,
				))
				.with_note(
					"this method takes `self` by value, and a pointer is not \
					 dereferenced: read the value with `.*` first",
				),
		);
	}
}

fn member_noun(kind: MemberKind) -> &'static str {
	match kind {
		MemberKind::Function(_) => "associated function",
		MemberKind::Method(_) => "method",
		MemberKind::Constant(_) => "associated constant",
		MemberKind::AssociatedType(_) => "associated type",
	}
}
