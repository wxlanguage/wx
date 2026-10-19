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
use crate::tir::defs::{BindingKey, MemberKind, Tier, TraitIdx, Visibility};
use crate::tir::members::{
	ApplicableMember, MemberLookup, TraitImplLookup, TraitMemberSelection,
	report_ambiguous_type_member,
};
use crate::tir::resolutions::Referent;
use crate::tir::signatures::InferPolicy;
use crate::tir::types::TypeIndex;

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
	Function(Callee),
	Constant,
}

impl BodyContext<'_, '_, '_, '_> {
	/// `<T as Trait>::member` or `<T>::member`: a member of the bracketed
	/// type. Only one segment may follow a trait-qualified root.
	pub(super) fn resolve_rooted_path<'s>(
		&mut self,
		expr: &'s Spanned<ast::Expression>,
	) -> Result<MemberPath<'s>, ExprIdx> {
		let mut obligations = Vec::new();
		let path = match &expr.inner {
			ast::Expression::Grouped { inner, segments } => {
				let (member, prefix) = segments.split_last().unwrap();
				let root = self.cx.resolve_type(
					&mut obligations,
					self.scope,
					inner,
					InferPolicy::Allow,
				);
				let receiver = self.cx.resolve_type_member_path(
					&mut obligations,
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
					&mut obligations,
					self.scope,
					&root.self_type,
					InferPolicy::Allow,
				);
				let qualified = self.cx.resolve_trait_bound_path(
					self.scope.file_id,
					self.scope.namespace,
					&root.trait_path,
				);
				self.cx.check_now(&obligations);
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
		self.cx.check_now(&obligations);
		Ok(path)
	}

	/// `Type::member` without a call: a function as a value, which needs its
	/// own type arguments written.
	pub(super) fn build_member_value(
		&mut self,
		path: MemberPath<'_>,
		span: TextSpan,
	) -> ExprIdx {
		match self.select_member(&path) {
			Some(Member::Function(callee)) => {
				self.build_function_value(callee, path.member, span)
			}
			Some(Member::Constant) => {
				self.unsupported(span, "an associated constant")
			}
			None => self.body.push(ExprKind::Error, TypeIndex::ERROR, span),
		}
	}

	/// `Type::member(a, b)`: a call of the function the member selects, by
	/// position. A method is called like any function here, its receiver the
	/// first argument.
	pub(super) fn build_member_call(
		&mut self,
		path: MemberPath<'_>,
		arguments: Arguments<'_>,
		expected: TypeIndex,
		span: TextSpan,
	) -> ExprIdx {
		let Arguments::Positional(arguments) = arguments else {
			return self.unsupported(span, "a function call by name");
		};
		match self.select_member(&path) {
			Some(Member::Function(callee)) => self.build_function_call(
				callee,
				path.member,
				None,
				arguments,
				expected,
				span,
			),
			Some(Member::Constant) => {
				self.unsupported(span, "a call of an associated constant")
			}
			None => self.body.push(ExprKind::Error, TypeIndex::ERROR, span),
		}
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
		let lookup = match qualified {
			// The named trait alone is searched; that the receiver implements
			// it is checked, and reported, here.
			Some(trait_index) => {
				let mut obligations = Vec::new();
				let found = self.cx.resolve_trait_qualified_value(
					&mut obligations,
					self.scope.env,
					receiver,
					trait_index,
					member.ident,
					self.scope.file_id,
				);
				self.cx.check_now(&obligations);
				match found {
					Ok(found) => MemberLookup::Found(found),
					Err(()) => MemberLookup::Error,
				}
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
				let _ =
					self.cx.report_solver_error::<()>(Err(error), reference);
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
		let (kind, leading, dispatch) = match found {
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
				(kind, leading, Dispatch::Direct)
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
					(kind, args, Dispatch::Direct)
				}
				TraitMemberSelection::TraitDeclaration(declaration) => {
					(declaration, Box::from([receiver]), Dispatch::Abstract)
				}
			},
			ApplicableMember::AbstractTraitMember { declaration, .. } => {
				(declaration, Box::from([receiver]), Dispatch::Abstract)
			}
		};
		Some(match kind {
			MemberKind::Function(function) | MemberKind::Method(function) => {
				Member::Function(Callee {
					function,
					leading,
					dispatch,
				})
			}
			MemberKind::Constant(_) => Member::Constant,
			MemberKind::AssociatedType(_) => {
				unreachable!("a value lookup finds no associated type")
			}
		})
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

fn member_noun(kind: MemberKind) -> &'static str {
	match kind {
		MemberKind::Function(_) => "associated function",
		MemberKind::Method(_) => "method",
		MemberKind::Constant(_) => "associated constant",
		MemberKind::AssociatedType(_) => "associated type",
	}
}
