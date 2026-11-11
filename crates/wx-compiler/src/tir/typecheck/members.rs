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
use super::{Arguments, BodyBuilder};
use crate::ast::{self, Ownership, Spanned};
use crate::diagnostics::{DiagnosticCode, SourceSpan, TextSpan};
use crate::tir::body::{ExprIdx, ExprKind, Place, PlaceKind};
use crate::tir::decls::{
	BindingKey, ConstIdx, DeclKind, InherentImplIdx, MemberKind, Tier,
	TraitIdx, Visibility,
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

/// What a call's context expects of it.
#[derive(Clone, Copy)]
pub(super) enum Expected {
	/// A type (`INFER` for none).
	Type(TypeIndex),
	/// The call is the receiver of a method call, `f(x).method(..)`, which
	/// expects of it what the method takes as `self`
	/// (`BodyBuilder::receiver_expectation`).
	Receiver(ReceiverOf),
}

impl Expected {
	/// The type expected, without reading a method's: `INFER` for a
	/// receiver.
	pub(super) fn ty(self) -> TypeIndex {
		match self {
			Self::Type(ty) => ty,
			Self::Receiver(_) => TypeIndex::INFER,
		}
	}
}

/// A method call's name and the type expected of the method call.
#[derive(Clone, Copy)]
pub(super) struct ReceiverOf {
	pub(super) method: BindingKey,
	pub(super) expected: TypeIndex,
}

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

/// A path written from a bracketed root, as an expression or a constant
/// argument writes one.
#[derive(Clone, Copy)]
pub(super) enum RootedPath<'s> {
	/// `<T as Trait>::member`.
	Qualified {
		root: &'s ast::QualifiedPathRoot,
		segments: &'s [ast::PathSegment],
	},
	/// `<T>::member`.
	Grouped {
		inner: &'s Spanned<ast::TypeExpression>,
		segments: &'s [ast::PathSegment],
	},
}

impl<'s> RootedPath<'s> {
	/// `expr`'s, when it is one.
	pub(super) fn of_expression(expr: &'s ast::Expression) -> Option<Self> {
		Some(match expr {
			ast::Expression::QualifiedPath { root, segments } => {
				Self::Qualified { root, segments }
			}
			ast::Expression::Grouped { inner, segments } => {
				Self::Grouped { inner, segments }
			}
			_ => return None,
		})
	}

	/// `argument`'s, when it is one.
	pub(super) fn of_constant(
		argument: &'s ast::ConstArgument,
	) -> Option<Self> {
		Some(match argument {
			ast::ConstArgument::QualifiedPath { root, segments } => {
				Self::Qualified { root, segments }
			}
			ast::ConstArgument::Grouped { inner, segments } => {
				Self::Grouped { inner, segments }
			}
			_ => return None,
		})
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

impl BodyBuilder<'_, '_> {
	/// `<T as Trait>::member` or `<T>::member`, written at `span`: a member
	/// of the bracketed type. Only one segment may follow a trait-qualified
	/// root.
	pub(super) fn resolve_rooted_path<'s>(
		&mut self,
		path: RootedPath<'s>,
		span: TextSpan,
	) -> Result<MemberPath<'s>, ExprIdx> {
		let path = match path {
			RootedPath::Grouped { inner, segments } => {
				let (member, prefix) = segments.split_last().unwrap();
				let root = self.builder.resolve_type(
					self.sema,
					&mut self.obligations.types,
					self.scope,
					inner,
					InferPolicy::Allow,
				);
				let receiver = self.builder.resolve_type_member_path(
					self.sema,
					&mut self.obligations.types,
					self.scope,
					root,
					prefix,
					InferPolicy::Allow,
				);
				MemberPath::new(receiver, member)
			}
			RootedPath::Qualified { root, segments } => {
				let [member] = segments else {
					return Err(self.unsupported(
						span,
						"a path past a trait-qualified member",
					));
				};
				let receiver = self.builder.resolve_type(
					self.sema,
					&mut self.obligations.types,
					self.scope,
					&root.self_type,
					InferPolicy::Allow,
				);
				let qualified = self.sema.resolve_trait_bound_path(
					self.builder.strings,
					self.scope.file_id,
					self.scope.namespace,
					&root.trait_path,
				);
				let Some(qualified) = qualified else {
					return Err(self.body.push(
						ExprKind::Error,
						TypeIndex::ERROR,
						span,
					));
				};
				return Ok(MemberPath {
					receiver,
					member,
					qualified: Some(qualified),
				});
			}
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
				let name =
					self.builder.strings.resolve(path.member.ident.inner);
				self.sema.diagnostics.push(
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
			self.sema.diagnostics.push(report_type_args_not_allowed(
				self.builder.strings,
				&self.sema.decls,
				self.scope.file_id,
				member,
				TypeArgsNotAllowedOn::Declaration(DeclKind::Const(constant)),
			));
		}
		let signature = &self.sema.constants[usize::from(constant)];
		debug_assert_eq!(
			self.sema.generic_envs.generic_count(signature.env),
			type_args.len()
		);
		let ty = self.sema.types.substitute(
			signature.ty,
			Substitution {
				envs: &self.sema.generic_envs,
				env: signature.env,
				args: type_args,
			},
		);
		let ty = self.context().normalized(ty);
		let ty = self.sema.types.collapse_error(ty);
		let owner = self.sema.decls.constants[usize::from(constant)].owner;
		let type_args = self
			.sema
			.generic_args
			.push(type_args.iter().map(|&arg| (arg, member.ident.span)));
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
		expected: Expected,
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
			None => {
				self.build_unchecked_arguments(arguments);
				self.body.push(ExprKind::Error, TypeIndex::ERROR, span)
			}
		}
	}

	/// A method call's receiver. A call there learns its type arguments from
	/// what the method expects of it (`receiver_expectation`), since nothing
	/// else gives the receiver an expected type; any other receiver expects
	/// nothing.
	fn build_receiver(
		&mut self,
		object: &Spanned<ast::Expression>,
		receiver_of: ReceiverOf,
	) -> ExprIdx {
		let span = object.span;
		match &object.inner {
			ast::Expression::Call { callee, arguments } => self.build_call(
				callee,
				Arguments::Positional(arguments),
				Expected::Receiver(receiver_of),
				span,
			),
			ast::Expression::NamedCall { callee, arguments } => self
				.build_call(
					callee,
					Arguments::Named(arguments),
					Expected::Receiver(receiver_of),
					span,
				),
			ast::Expression::MethodCall(call) => self.build_method_call(
				&call.object,
				&call.method,
				Arguments::Positional(&call.arguments),
				Expected::Receiver(receiver_of),
				span,
			),
			ast::Expression::NamedMethodCall(call) => self.build_method_call(
				&call.object,
				&call.method,
				Arguments::Named(&call.arguments),
				Expected::Receiver(receiver_of),
				span,
			),
			_ => self.build(object, TypeIndex::INFER),
		}
	}

	/// `receiver.method(a, b)` or `receiver.method({ b, a })`: a call of the
	/// method the receiver's type has, the receiver its first argument. A
	/// pointer is not dereferenced: a method of the pointee is found only when
	/// it takes `self` by pointer, as `self: Mem::*Self` does, and the pointer
	/// itself is then `self`. The one conversion is an exclusive pointer
	/// given to a method that takes a shared one, `self: Mem::&Self`, which
	/// is `receiver.*.&`.
	pub(super) fn build_method_call(
		&mut self,
		object: &Spanned<ast::Expression>,
		method: &ast::PathSegment,
		arguments: Arguments<'_>,
		expected: Expected,
		span: TextSpan,
	) -> ExprIdx {
		// A method call that is itself a receiver expects nothing it can
		// pass on: its method is selected only once its receiver is built.
		let receiver = self.build_receiver(
			object,
			ReceiverOf {
				method: BindingKey::value(method.ident.inner),
				expected: expected.ty(),
			},
		);
		let receiver_ty = self.body.ty(receiver);
		if self.sema.types.needs_context(receiver_ty) {
			self.report_annotation_required(receiver);
			self.build_unchecked_arguments(arguments);
			return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
		}
		let receiver_ty = self.context().normalized(receiver_ty);
		let pointee = match *self.sema.types.resolve(receiver_ty) {
			Type::Pointer { to, .. } => Some(to),
			_ => None,
		};
		let path = MemberPath::new(pointee.unwrap_or(receiver_ty), method);
		let callee = match self.select_member(&path) {
			Some(Member::Method(callee)) => callee,
			Some(Member::Function(_) | Member::Constant { .. }) => {
				self.report_not_a_method(receiver_ty, method);
				self.build_unchecked_arguments(arguments);
				return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
			}
			None => {
				self.build_unchecked_arguments(arguments);
				return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
			}
		};
		let mut receiver = receiver;
		if let Type::Pointer {
			to,
			memory,
			ownership,
		} = *self.sema.types.resolve(receiver_ty)
		{
			let params =
				self.sema.functions[usize::from(callee.function)].param_types;
			let declared = self.sema.types.list(params)[0];
			let Type::Pointer {
				ownership: declared,
				..
			} = *self.sema.types.resolve(declared)
			else {
				self.report_by_value_through_pointer(receiver_ty, method);
				self.build_unchecked_arguments(arguments);
				return self.body.push(ExprKind::Error, TypeIndex::ERROR, span);
			};
			match (ownership, declared) {
				(Ownership::Exclusive, Ownership::Shared) => {
					receiver = self.shared_receiver(receiver, to, memory);
				}
				(Ownership::Shared, Ownership::Exclusive) => {
					self.report_shared_receiver(receiver, method);
					self.build_unchecked_arguments(arguments);
					return self.body.push(
						ExprKind::Error,
						TypeIndex::ERROR,
						span,
					);
				}
				_ => {}
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
				let found = self.sema.resolve_trait_qualified_value(
					self.builder.strings,
					&mut self.obligations.types,
					self.scope.generic_env,
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
			None if self.sema.types.has_infer(receiver) => {
				let (found, impl_args) =
					self.select_inherent_with_holes(receiver, key, member)?;
				learned = Some(impl_args);
				MemberLookup::Found(found)
			}
			None => self.builder.resolve_applicable_member(
				self.sema,
				self.scope.assumption_env,
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
						self.sema
							.diagnostics
							.push(self.sema.overflow_diagnostic(reference));
					}
					SolverError::Cycle(cycle) => {
						self.sema.diagnostics.push(self.sema.cycle_diagnostic(
							self.builder.strings,
							&cycle,
							reference,
						));
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
				self.sema.diagnostics.push(report_ambiguous_type_member(
					self.scope.file_id,
					self.builder.strings,
					&self.sema.decls,
					member.ident,
					&candidates,
				));
				return None;
			}
		};
		self.sema.resolutions.record(
			(reference, Tier::Value),
			Referent::Member(found.selected_kind(&self.sema.decls)),
		);
		self.check_member_access(found, key, member);
		let receiver = self.context().normalized(receiver);
		// The impl's arguments, and whether the selection proved them; a
		// trait's declaration is selected over `[Self]` instead.
		let (kind, impl_args, proven) = match found {
			ApplicableMember::Inherent { kind, .. }
				if let Some(impl_args) = learned =>
			{
				(kind, Some(impl_args), false)
			}
			ApplicableMember::Inherent { impl_index, kind } => {
				let header = self.sema.inherent_impls[usize::from(impl_index)]
					.as_ref()
					.expect("a selected impl has a header");
				// The lookup matched this impl's target to the receiver.
				let leading = self
					.sema
					.types
					.match_impl_target(
						header.target.inner,
						receiver,
						&self.sema.generic_envs,
						header.type_params,
					)
					.expect("the selected impl's target matches the receiver");
				(kind, Some(leading), true)
			}
			ApplicableMember::TraitImplMember {
				trait_index,
				impl_index,
				declaration,
			} => match self
				.sema
				.decls
				.select_trait_member(impl_index, declaration)
			{
				TraitMemberSelection::Impl(kind) => {
					let Ok(Some(TraitImplLookup::Concrete { args, .. })) =
						self.sema.find_trait_impl_query(
							self.builder.strings,
							self.scope.assumption_env,
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
				self.sema, function, leading, proven,
			)),
			MemberKind::Method(function) => Member::Method(Callee::new(
				self.sema, function, leading, proven,
			)),
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
			ImplTarget::from_type(self.sema.types.resolve(receiver))
		else {
			self.report_no_member(receiver, member);
			return None;
		};
		let mut candidates =
			self.inherent_candidates_with_holes(target, receiver, key);
		// A type's inherent impls declare a name once between them, so a
		// second candidate is a duplicate already reported.
		if candidates.len() > 1 {
			return None;
		}
		let Some((impl_index, kind, impl_args)) = candidates.pop() else {
			let is_trait_member =
				self.sema.impl_dispatch.trait_candidates(target).iter().any(
					|&(trait_index, _)| {
						self.sema
							.decls
							.declared_trait_member(trait_index, key)
							.is_some()
					},
				);
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

	/// The inherent impls of `target` that declare `key` and whose target,
	/// with what `receiver` (partly unknown) teaches their parameters, still
	/// meets it: each with the member and the impl's arguments learned.
	/// Reports nothing.
	fn inherent_candidates_with_holes(
		&mut self,
		target: ImplTarget,
		receiver: TypeIndex,
		key: BindingKey,
	) -> Vec<(InherentImplIdx, MemberKind, Box<[TypeIndex]>)> {
		let impl_dispatch = &self.sema.impl_dispatch;
		let mut candidates = Vec::new();
		for &impl_index in impl_dispatch.inherent_candidates(target) {
			let impl_decl =
				&self.sema.decls.inherent_impls[usize::from(impl_index)];
			let Some(&member_index) = impl_decl.bindings.get(&key) else {
				continue;
			};
			let kind = impl_decl.members[usize::from(member_index)].kind;
			let Some(header) =
				&self.sema.inherent_impls[usize::from(impl_index)]
			else {
				continue;
			};
			let (env, pattern) = (header.type_params, header.target.inner);
			let count = self.sema.generic_envs.generic_count(env);
			let mut impl_args =
				vec![TypeIndex::INFER; count].into_boxed_slice();
			self.sema.types.learn(
				&self.sema.generic_envs,
				env,
				&mut impl_args,
				pattern,
				receiver,
			);
			let instantiated = self.sema.types.substitute(
				pattern,
				Substitution {
					envs: &self.sema.generic_envs,
					env,
					args: &impl_args,
				},
			);
			if self.sema.types.meet(instantiated, receiver).is_some() {
				candidates.push((impl_index, kind, impl_args));
			}
		}
		candidates
	}

	/// What a method call expects of its receiver, before the receiver has
	/// settled its type arguments: `shape` is the receiver's type as far as
	/// it knows it (`RawPtr<_, _>`), and the method `receiver_of` names,
	/// found on that shape, learns its arguments from the type expected of
	/// the call (`heap::*u8` against `Mem::*T`) and instantiates its `self`
	/// (`RawPtr<heap, u8>`). Only a hint: the method is selected again, and
	/// reported, once the receiver is built. `INFER` when the shape is known
	/// already or the method is not found on it.
	pub(super) fn receiver_expectation(
		&mut self,
		shape: TypeIndex,
		receiver_of: ReceiverOf,
	) -> TypeIndex {
		let ReceiverOf { method, expected } = receiver_of;
		if !self.sema.types.has_infer(shape)
			|| expected == TypeIndex::INFER
			|| expected == TypeIndex::ERROR
		{
			return TypeIndex::INFER;
		}
		let pointer = match *self.sema.types.resolve(shape) {
			Type::Pointer { to, ownership, .. } => Some((to, ownership)),
			_ => None,
		};
		let selected = pointer.map_or(shape, |(to, _)| to);
		let Some(target) =
			ImplTarget::from_type(self.sema.types.resolve(selected))
		else {
			return TypeIndex::INFER;
		};
		let mut candidates =
			self.inherent_candidates_with_holes(target, selected, method);
		// More than one is a duplicate, reported where it is declared.
		if candidates.len() != 1 {
			return TypeIndex::INFER;
		}
		let (_, kind, impl_args) = candidates.pop().unwrap();
		let MemberKind::Method(function) = kind else {
			return TypeIndex::INFER;
		};
		let Callee { mut type_args, .. } =
			Callee::new(self.sema, function, &impl_args, 0);
		let (env, _) = self.function_frames(function);
		let signature = &self.sema.functions[usize::from(function)];
		let (return_type, params) =
			(signature.return_type, signature.param_types);
		let expected = self.context().normalized(expected);
		self.sema.types.learn(
			&self.sema.generic_envs,
			env,
			&mut type_args,
			return_type,
			expected,
		);
		let Some(&declared) = self.sema.types.list(params).first() else {
			return TypeIndex::INFER;
		};
		let hint = self.instantiate(declared, env, &type_args);
		// A receiver's pointer gives a method taking `self` by either kind
		// of pointer (`*` for `&` is `receiver.*.&`), so its own kind is
		// kept: the parts are what the call learns from.
		match (pointer, *self.sema.types.resolve(hint)) {
			(Some((_, ownership)), Type::Pointer { to, memory, .. }) => {
				self.sema.types.intern(Type::Pointer {
					to,
					memory,
					ownership,
				})
			}
			(None, Type::Pointer { .. }) | (Some(_), _) => TypeIndex::INFER,
			(None, _) => hint,
		}
	}

	/// Reports a member not visible here: an inherent member by its own
	/// visibility, a trait's by the trait's.
	fn check_member_access(
		&mut self,
		found: ApplicableMember,
		key: BindingKey,
		member: &ast::PathSegment,
	) {
		let decls = &self.sema.decls;
		let (namespace, visibility) = match found {
			ApplicableMember::Inherent { impl_index, .. } => {
				let impl_decl = &decls.inherent_impls[usize::from(impl_index)];
				let index = impl_decl.bindings[&key];
				(
					impl_decl.namespace,
					impl_decl.members[usize::from(index)].visibility,
				)
			}
			ApplicableMember::TraitImplMember { trait_index, .. }
			| ApplicableMember::AbstractTraitMember { trait_index, .. } => {
				let trait_decl = &decls.traits[usize::from(trait_index)];
				(trait_decl.namespace, Visibility::from(trait_decl.pub_span))
			}
		};
		if decls.namespaces.is_accessible_from(
			self.scope.namespace,
			namespace.into(),
			visibility,
		) {
			return;
		}
		let noun = member_noun(found.selected_kind(decls));
		let name = self.builder.strings.resolve(member.ident.inner).unwrap();
		self.sema.diagnostics.push(
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
		let name = self.builder.strings.resolve(member.ident.inner).unwrap();
		let receiver = self
			.sema
			.type_formatter(self.builder.strings)
			.display_type(receiver);
		self.sema.diagnostics.push(
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

impl BodyBuilder<'_, '_> {
	fn report_not_a_method(
		&mut self,
		receiver: TypeIndex,
		method: &ast::PathSegment,
	) {
		let name = self.builder.strings.resolve(method.ident.inner).unwrap();
		let receiver = self
			.sema
			.type_formatter(self.builder.strings)
			.display_type(receiver);
		self.sema.diagnostics.push(
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

	/// The exclusive pointer `receiver` to `to` in `memory`, as a shared one:
	/// `receiver.*.&`.
	fn shared_receiver(
		&mut self,
		receiver: ExprIdx,
		to: TypeIndex,
		memory: TypeIndex,
	) -> ExprIdx {
		let span = self.body.span(receiver);
		let place = self.body.push_place(Place {
			kind: PlaceKind::Deref { pointer: receiver },
			ty: to,
			memory,
			mutable: true,
			span,
		});
		let ty = self.sema.types.intern(Type::Pointer {
			to,
			memory,
			ownership: Ownership::Shared,
		});
		self.body.push(ExprKind::AddressOf(place), ty, span)
	}

	/// A method that takes `self` by exclusive pointer, called on a shared
	/// one.
	fn report_shared_receiver(
		&mut self,
		receiver: ExprIdx,
		method: &ast::PathSegment,
	) {
		let at = self.context().source_span(receiver);
		let name = self.builder.strings.resolve(method.ident.inner).unwrap();
		let found = self
			.sema
			.type_formatter(self.builder.strings)
			.display_type(self.body.ty(receiver));
		self.sema.diagnostics.push(
			Diagnostic::error()
				.with_code(DiagnosticCode::TypeMistmatch.code())
				.with_message(format!(
					"`{name}` takes `self` by exclusive pointer, but the \
					 receiver is `{found}`"
				))
				.with_label(at.primary_label().with_message("a shared pointer"))
				.with_label(Label::secondary(
					self.scope.file_id,
					method.ident.span,
				)),
		);
	}

	fn report_by_value_through_pointer(
		&mut self,
		receiver: TypeIndex,
		method: &ast::PathSegment,
	) {
		let name = self.builder.strings.resolve(method.ident.inner).unwrap();
		let receiver = self
			.sema
			.type_formatter(self.builder.strings)
			.display_type(receiver);
		self.sema.diagnostics.push(
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
