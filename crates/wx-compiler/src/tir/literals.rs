use std::borrow::Cow;
use std::fmt;

use codespan_reporting::diagnostic::Diagnostic;

use super::bounds::{AssumptionEnvIdx, BindingRef, Readiness};
use super::defs::{ConstIdx, TypesetIdx};
use super::eval::ResolvedConstant;
use super::signatures::TypeContext;
use super::solver::{NormalizationDepth, RewriteFlags, SolverError};
use super::types::{GenericEnvOwner, Substitution, Type, TypeIndex};
use crate::ast::{Spanned, UnaryOp};
use crate::{
	diagnostics::{DiagnosticCode, SourceSpan, TextSpan},
	vfs::FileId,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum StringLiteralErrorKind {
	UnknownEscape(char),
	Unterminated,
}

#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug))]
pub(super) struct StringLiteralError {
	pub kind: StringLiteralErrorKind,
	/// Byte range relative to the opening quote, including UTF-8 characters.
	pub span: TextSpan,
}

impl StringLiteralError {
	pub(super) fn diagnostic(self, literal: SourceSpan) -> Diagnostic<FileId> {
		let reference = SourceSpan::new(
			literal.file_id,
			TextSpan::new(
				literal.span.start + self.span.start,
				literal.span.start + self.span.end,
			),
		);
		let (code, message, label) = match self.kind {
			StringLiteralErrorKind::UnknownEscape(ch) => (
				DiagnosticCode::UnknownCharacterEscape,
				format!("unknown character escape: `{ch}`"),
				"unknown character escape",
			),
			StringLiteralErrorKind::Unterminated => (
				DiagnosticCode::UnterminatedStringLiteral,
				"unterminated string literal".to_string(),
				"missing closing quote",
			),
		};
		Diagnostic::error()
			.with_code(code.code())
			.with_message(message)
			.with_label(reference.primary_label().with_message(label))
	}
}

/// Decodes a quoted string token. Plain strings borrow their contents;
/// an owned buffer is allocated only when an escape needs decoding.
/// Unknown escapes are errors, rather than silently becoming literal backslashes.
pub(super) fn unescape_string_literal(
	source: &str,
) -> Result<Cow<'_, str>, StringLiteralError> {
	let unterminated = || StringLiteralError {
		kind: StringLiteralErrorKind::Unterminated,
		span: TextSpan::new(0, source.len() as u32),
	};
	let mut chars = source.char_indices();
	if chars.next() != Some((0, '"')) {
		return Err(unterminated());
	}
	let mut decoded: Option<String> = None;
	while let Some((offset, ch)) = chars.next() {
		match ch {
			'"' if offset + 1 == source.len() => {
				return Ok(match decoded {
					Some(value) => Cow::Owned(value),
					None => Cow::Borrowed(&source[1..offset]),
				});
			}
			'"' => return Err(unterminated()),
			'\\' => {
				let Some((escape_offset, escape)) = chars.next() else {
					return Err(unterminated());
				};
				let value = match escape {
					'n' => '\n',
					'r' => '\r',
					't' => '\t',
					'\\' => '\\',
					'"' => '"',
					'0' => '\0',
					ch => {
						return Err(StringLiteralError {
							kind: StringLiteralErrorKind::UnknownEscape(ch),
							span: TextSpan::new(
								escape_offset as u32,
								(escape_offset + ch.len_utf8()) as u32,
							),
						});
					}
				};
				let output = decoded.get_or_insert_with(|| {
					let mut value =
						String::with_capacity(source.len().saturating_sub(2));
					value.push_str(&source[1..offset]);
					value
				});
				output.push(value);
			}
			ch => {
				if let Some(output) = &mut decoded {
					output.push(ch);
				}
			}
		}
	}
	Err(unterminated())
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn decodes_supported_escapes_and_borrows_plain_strings() {
		for (source, expected) in [
			(r#""plain λ""#, "plain λ"),
			(r#""""#, ""),
			(r#""\n\r\t\\\"\0""#, "\n\r\t\\\"\0"),
			(r#""slash\\n""#, "slash\\n"),
		] {
			assert_eq!(unescape_string_literal(source).unwrap(), expected);
		}
		assert!(matches!(
			unescape_string_literal(r#""plain""#).unwrap(),
			Cow::Borrowed("plain")
		));
	}

	#[test]
	fn unknown_escapes_have_utf8_byte_ranges() {
		for (source, ch, start, end) in [
			(r#""\o""#, 'o', 2, 3),
			(r#""λ\💥""#, '💥', 4, 8),
			(r#""\x41""#, 'x', 2, 3),
		] {
			let error = unescape_string_literal(source).unwrap_err();
			assert_eq!(error.kind, StringLiteralErrorKind::UnknownEscape(ch));
			assert_eq!(error.span, TextSpan::new(start, end));
		}
	}

	#[test]
	fn escaped_quotes_and_dangling_backslashes_do_not_terminate_strings() {
		for source in ["\"", "\"text", "\"text\\", r#""text\""#, "not quoted"] {
			let error = unescape_string_literal(source).unwrap_err();
			assert_eq!(error.kind, StringLiteralErrorKind::Unterminated);
			assert_eq!(error.span, TextSpan::new(0, source.len() as u32));
		}
	}
}

#[cfg_attr(test, derive(Debug, PartialEq))]
pub enum CharLiteralError {
	Empty,
	TooLong,
}

pub fn parse_char_literal(s: &str) -> Result<char, CharLiteralError> {
	let content = if s.starts_with('\'') && s.ends_with('\'') && s.len() >= 2 {
		&s[1..s.len() - 1]
	} else {
		s
	};

	let mut chars = content.chars();
	let value = match chars.next() {
		None => return Err(CharLiteralError::Empty),
		Some('\\') => match chars.next() {
			None => return Err(CharLiteralError::Empty),
			Some('n') => '\n',
			Some('r') => '\r',
			Some('t') => '\t',
			Some('\\') => '\\',
			Some('\'') => '\'',
			Some('0') => '\0',
			Some('x') => {
				let hi = chars.next().and_then(|c| c.to_digit(16));
				let lo = chars.next().and_then(|c| c.to_digit(16));
				match (hi, lo) {
					(Some(h), Some(l)) => {
						let codepoint = h * 16 + l;
						char::from_u32(codepoint).unwrap()
					}
					_ => return Err(CharLiteralError::TooLong),
				}
			}
			Some(c) => c,
		},
		Some(c) => c,
	};

	if chars.next().is_some() {
		return Err(CharLiteralError::TooLong);
	}

	Ok(value)
}

/// An integer type, for the range of a literal or a constant of it.
#[derive(Clone, Copy)]
pub(super) enum Integer {
	I8,
	U8,
	I16,
	U16,
	I32,
	U32,
	I64,
	U64,
}

impl Integer {
	pub(super) fn from_type(ty: TypeIndex) -> Option<Self> {
		Some(match ty {
			TypeIndex::U8 => Self::U8,
			TypeIndex::I8 => Self::I8,
			TypeIndex::U16 => Self::U16,
			TypeIndex::I16 => Self::I16,
			TypeIndex::U32 => Self::U32,
			TypeIndex::I32 => Self::I32,
			TypeIndex::U64 => Self::U64,
			TypeIndex::I64 => Self::I64,
			_ => return None,
		})
	}

	/// Whether `value` is in the type's range.
	pub(super) fn contains(self, value: i128) -> bool {
		i128::from(self.min()) <= value && value <= i128::from(self.max())
	}

	pub(super) fn is_signed(self) -> bool {
		match self {
			Self::I8 | Self::I16 | Self::I32 | Self::I64 => true,
			Self::U8 | Self::U16 | Self::U32 | Self::U64 => false,
		}
	}

	pub(super) fn max(self) -> u64 {
		match self {
			Self::I8 => i8::MAX as u64,
			Self::U8 => u8::MAX as u64,
			Self::I16 => i16::MAX as u64,
			Self::U16 => u16::MAX as u64,
			Self::I32 => i32::MAX as u64,
			Self::U32 => u32::MAX as u64,
			Self::I64 => i64::MAX as u64,
			Self::U64 => u64::MAX,
		}
	}

	fn min(self) -> i64 {
		match self {
			Self::I8 => i8::MIN as i64,
			Self::U8 => 0,
			Self::I16 => i16::MIN as i64,
			Self::U16 => 0,
			Self::I32 => i32::MIN as i64,
			Self::U32 => 0,
			Self::I64 => i64::MIN,
			Self::U64 => 0,
		}
	}
}

#[derive(Clone, Copy)]
pub(super) enum Float {
	F32,
	F64,
}

impl Float {
	pub(super) fn from_type(ty: TypeIndex) -> Option<Self> {
		Some(match ty {
			TypeIndex::F32 => Self::F32,
			TypeIndex::F64 => Self::F64,
			_ => return None,
		})
	}

	fn mantissa_bits(self) -> u32 {
		match self {
			Self::F32 => 24,
			Self::F64 => 53,
		}
	}

	/// Whether the integer `value` is a value of the type, exactly.
	fn holds_exactly(self, value: i128) -> bool {
		let value = value.unsigned_abs();
		value == 0
			|| 128 - value.leading_zeros() - value.trailing_zeros()
				<= self.mantissa_bits()
	}
}

/// A concrete type a target may be: the target itself, or, for an abstract
/// target, a member of a typeset it is bounded by, as written. An untyped
/// value given the target must be representable as every one.
#[derive(Clone, Copy)]
pub(super) enum ConcreteType {
	Target(TypeIndex),
	Member(TypesetIdx, Spanned<TypeIndex>),
}

/// Why a concrete type does not hold an integer.
#[derive(Clone, Copy)]
pub(super) enum IntegerMiss {
	/// Outside an integer type's range.
	OutOfRange,
	/// Not exactly a value of a float type.
	Inexact,
	/// Neither an integer nor a float type.
	WrongKind,
}

/// Why a concrete type does not hold a character.
#[derive(Clone, Copy)]
pub(super) enum CharMiss {
	/// A code point outside an integer type's range.
	OutOfRange,
	/// Neither `Char` nor an integer type.
	WrongKind,
}

/// Why a concrete type does not hold a float literal.
#[derive(Clone, Copy)]
pub(super) enum FloatMiss {
	/// It reads as infinity at the concrete type's width.
	TooLarge,
	/// It is nonzero in text but reads as zero at the concrete type's width.
	TooSmall,
	/// It is no float type.
	WrongKind,
}

impl ConcreteType {
	pub(super) fn ty(&self) -> TypeIndex {
		match *self {
			ConcreteType::Target(ty) => ty,
			ConcreteType::Member(_, member) => member.inner,
		}
	}

	/// An integer: an integer type's value, or a float type's exactly.
	pub(super) fn holds_integer(&self, value: i128) -> Result<(), IntegerMiss> {
		if let Some(integer) = Integer::from_type(self.ty()) {
			integer
				.contains(value)
				.then_some(())
				.ok_or(IntegerMiss::OutOfRange)
		} else if let Some(float) = Float::from_type(self.ty()) {
			float
				.holds_exactly(value)
				.then_some(())
				.ok_or(IntegerMiss::Inexact)
		} else {
			Err(IntegerMiss::WrongKind)
		}
	}

	/// A character: a `Char`, or an integer type its code point is a value
	/// of.
	pub(super) fn holds_char(&self, code_point: u32) -> Result<(), CharMiss> {
		if self.ty() == TypeIndex::CHAR {
			return Ok(());
		}
		match Integer::from_type(self.ty()) {
			Some(integer) if integer.contains(i128::from(code_point)) => Ok(()),
			Some(_) => Err(CharMiss::OutOfRange),
			None => Err(CharMiss::WrongKind),
		}
	}

	/// A float literal written `text`, read at the concrete type's width.
	/// `None` when the text is no float, which the parser has reported.
	pub(super) fn read_float(
		&self,
		text: &str,
	) -> Result<Option<f64>, FloatMiss> {
		let Some(float) = Float::from_type(self.ty()) else {
			return Err(FloatMiss::WrongKind);
		};
		let read = match float {
			// f64::from is a lossless conversion
			Float::F32 => text.parse::<f32>().map(f64::from),
			Float::F64 => text.parse::<f64>(),
		};
		match read {
			Ok(value) if value.is_infinite() => Err(FloatMiss::TooLarge),
			Ok(value)
				if value == 0.0
					&& text
						.bytes()
						.any(|b| b.is_ascii_digit() && b != b'0') =>
			{
				Err(FloatMiss::TooSmall)
			}
			Ok(value) => Ok(Some(value)),
			Err(_) => Ok(None),
		}
	}

	/// Whether `op` means anything over a value of the concrete type.
	pub(super) fn allows_unary(&self, op: UnaryOp) -> bool {
		let ty = self.ty();
		match op {
			UnaryOp::InvertSign => {
				Integer::from_type(ty).is_some_and(Integer::is_signed)
					|| Float::from_type(ty).is_some()
			}
			UnaryOp::BitNot => Integer::from_type(ty).is_some(),
			UnaryOp::Not => false,
		}
	}

	pub(super) fn is_float(&self) -> bool {
		Float::from_type(self.ty()).is_some()
	}
}

/// What an untyped constant reads as.
pub(super) enum UntypedValue {
	Known(i128),
	/// A trait's constant over a `Self` not known here: only a representability
	/// clause says what it is representable as.
	Abstract,
	/// It has no value; why was reported where it is.
	Failed,
}

impl TypeContext<'_, '_, '_> {
	/// The value of `constant` read with `args` (a trait constant's are
	/// `[Self]`), in `env`.
	pub(super) fn untyped_value(
		&mut self,
		env: AssumptionEnvIdx,
		constant: ConstIdx,
		args: &[TypeIndex],
	) -> Result<UntypedValue, SolverError> {
		let resolved = match self.resolve_constant(constant, args) {
			Ok(resolved) => resolved,
			Err(SolverError::Pending) => return Err(SolverError::Pending),
			Err(_) => return Ok(UntypedValue::Failed),
		};
		Ok(match resolved {
			ResolvedConstant::Length(length) => {
				let length = match self.normalize(
					env,
					length,
					NormalizationDepth::Deep,
					RewriteFlags::ALL,
				) {
					Ok(length) => length,
					Err(SolverError::Pending) => {
						return Err(SolverError::Pending);
					}
					Err(_) => return Ok(UntypedValue::Failed),
				};
				match *self.types.resolve(length) {
					Type::Value { bits } => {
						UntypedValue::Known(i128::from(bits))
					}
					_ => UntypedValue::Abstract,
				}
			}
			ResolvedConstant::Instance(instance) => self
				.exact_value(instance.constant)
				.map_or(UntypedValue::Failed, UntypedValue::Known),
			ResolvedConstant::Abstract => UntypedValue::Abstract,
		})
	}

	/// The types an untyped value given `ty` must be representable as: `ty`
	/// itself when it is a scalar or `Char`, or every member of every typeset
	/// an abstract `ty` is bounded by. Empty when no untyped value can be
	/// given `ty`.
	pub(super) fn concrete_types(
		&self,
		env: AssumptionEnvIdx,
		ty: TypeIndex,
	) -> Vec<ConcreteType> {
		if Integer::from_type(ty).is_some()
			|| Float::from_type(ty).is_some()
			|| ty == TypeIndex::CHAR
		{
			return vec![ConcreteType::Target(ty)];
		}
		// An abstract type is constrained by its own bounds alone, so read
		// the typesets those name rather than probing every typeset.
		let mut concrete_types = Vec::new();
		for trait_index in self.clause_tables().declared_traits(
			&self.types,
			env,
			ty,
			self.solver.state.recursion_budget,
		) {
			let Some(typeset) =
				self.defs.traits[usize::from(trait_index)].typeset
			else {
				continue;
			};
			for &member in self.typeset_members(typeset) {
				concrete_types.push(ConcreteType::Member(typeset, member));
			}
		}
		concrete_types
	}

	/// The integers every concrete type of `ty` holds, as an inclusive range.
	/// `None` when a concrete type is no integer type, or there is none.
	fn integer_range(
		&self,
		env: AssumptionEnvIdx,
		ty: TypeIndex,
	) -> Option<(i128, i128)> {
		let mut range: Option<(i128, i128)> = None;
		for concrete in self.concrete_types(env, ty) {
			let integer = Integer::from_type(concrete.ty())?;
			let (low, high) =
				(i128::from(integer.min()), i128::from(integer.max()));
			let (lowest, highest) = range.unwrap_or((low, high));
			range = Some((lowest.max(low), highest.min(high)));
		}
		range
	}

	/// Whether `value` is representable as `ty`.
	pub(super) fn value_representable(
		&self,
		env: AssumptionEnvIdx,
		ty: TypeIndex,
		value: i128,
	) -> bool {
		self.integer_range(env, ty)
			.is_some_and(|(low, high)| low <= value && value <= high)
	}

	/// Whether being representable as `assumed` implies being representable as
	/// `target`.
	fn representable_implies(
		&self,
		env: AssumptionEnvIdx,
		assumed: TypeIndex,
		target: TypeIndex,
	) -> bool {
		if assumed == target {
			return true;
		}
		match (
			self.integer_range(env, assumed),
			self.integer_range(env, target),
		) {
			(Some((low, high)), Some((lowest, highest))) => {
				lowest <= low && high <= highest
			}
			_ => false,
		}
	}

	/// Whether a representability clause in `env`, or on a declaration along
	/// `subject`'s projection path, says `subject`'s `constant` is
	/// representable as `ty` (normalized).
	pub(super) fn assumed_representable(
		&mut self,
		env: AssumptionEnvIdx,
		subject: TypeIndex,
		constant: ConstIdx,
		ty: TypeIndex,
	) -> Result<bool, SolverError> {
		let tables = self.clause_tables();
		let sources = tables.declarations_of(
			&self.types,
			env,
			subject,
			self.solver.state.recursion_budget,
		);
		match sources.readiness {
			Readiness::Ready => {}
			Readiness::Pending => return Err(SolverError::Pending),
			Readiness::Overflowed => return Err(SolverError::Overflow),
		}
		let mut stated = Vec::new();
		for source in sources {
			for clause in tables.clauses.representable(source.clauses.range()) {
				if clause.target.constant == constant
					&& source.names(
						&self.types,
						&self.generic_envs,
						clause.subject,
						subject,
					) {
					stated.push((clause.ty, source.context));
				}
			}
		}
		for (assumed, context) in stated {
			// A declaration's clause names its trait's `Self`, which is the
			// projection's base here.
			let assumed = match context {
				Some(context) => self.types.substitute(
					assumed,
					Substitution {
						envs: &self.generic_envs,
						env: context.env,
						args: &[context.receiver],
					},
				),
				None => assumed,
			};
			let assumed = self.normalize(
				env,
				assumed,
				NormalizationDepth::Deep,
				RewriteFlags::ALL,
			)?;
			if self.representable_implies(env, assumed, ty) {
				return Ok(true);
			}
		}
		Ok(false)
	}

	/// E2004: `what` ("literal `300`") is outside the range of the integer
	/// type `ty`.
	pub(super) fn report_out_of_range(
		&self,
		what: impl fmt::Display,
		ty: TypeIndex,
		at: SourceSpan,
	) -> Diagnostic<FileId> {
		Diagnostic::error()
			.with_code(DiagnosticCode::IntegerLiteralOutOfRange.code())
			.with_message(format!(
				"{what} cannot be represented as `{}`",
				self.type_formatter().display_type(ty)
			))
			.with_label(at.primary_label())
	}

	/// E2047: `what` is not representable as `member`, one of the members of
	/// `typeset` an abstract target may be.
	pub(super) fn report_typeset_member(
		&self,
		what: impl fmt::Display,
		typeset: TypesetIdx,
		member: Spanned<TypeIndex>,
		at: SourceSpan,
	) -> Diagnostic<FileId> {
		let def = &self.defs.typesets[usize::from(typeset)];
		let name = self.strings.resolve(def.name.inner).unwrap();
		let member_name = self.type_formatter().display_type(member.inner);
		Diagnostic::error()
			.with_code(DiagnosticCode::TypesetBoundViolation.code())
			.with_message(format!(
				"{what} is not representable by every member of typeset \
				 `{name}`"
			))
			.with_label(at.primary_label().with_message(format!(
				"cannot be represented as `{member_name}`"
			)))
			.with_label(
				SourceSpan::new(def.file_id, member.span)
					.secondary_label()
					.with_message(format!("`{member_name}` is a member here")),
			)
	}

	/// E2134: a bound states what `constant` is representable as, but the
	/// constant has a type, `declared`.
	pub(super) fn report_typed_constant_bound(
		&self,
		at: SourceSpan,
		constant: ConstIdx,
		declared: TypeIndex,
	) -> Diagnostic<FileId> {
		let def = &self.defs.constants[usize::from(constant)];
		let name = self.strings.resolve(def.name.inner).unwrap();
		let declared = self.type_formatter().display_type(declared);
		Diagnostic::error()
			.with_code(DiagnosticCode::TypedConstantBound.code())
			.with_message(format!(
				"constant `{name}` has a type, so a bound cannot state what it \
				 is representable as"
			))
			.with_label(at.primary_label())
			.with_label(
				SourceSpan::new(def.file_id, def.name.span)
					.secondary_label()
					.with_message(format!(
						"`{name}` is declared `{declared}` here"
					)),
			)
			.with_note(
				"only an untyped constant (`{integer}`, `{char}`) takes its type \
				 from where it is used",
			)
	}

	/// `subject`'s `constant` is not representable as `ty`, which the entry
	/// `source` requires: `value` is its value, or `None` when it has none
	/// here and no representability clause in scope says it is.
	pub(super) fn report_unrepresentable_constant(
		&mut self,
		reference: SourceSpan,
		(subject, constant): (TypeIndex, ConstIdx),
		ty: TypeIndex,
		value: Option<i128>,
		source: Option<(BindingRef, GenericEnvOwner)>,
	) -> Diagnostic<FileId> {
		let read = self.types.intern_const(constant, &[subject]);
		let formatter = self.type_formatter();
		let (read, ty) =
			(formatter.display_type(read), formatter.display_type(ty));
		let name = self.defs.constants[usize::from(constant)].name.inner;
		let name = self.strings.resolve(name).unwrap();
		let label = match value {
			Some(value) => {
				format!("its value `{value}` is out of range for `{ty}`")
			}
			None => "its value is not known here".to_owned(),
		};
		let mut diagnostic = Diagnostic::error()
			.with_code(DiagnosticCode::UnrepresentableConstant.code())
			.with_message(format!(
				"constant `{read}` cannot be represented as `{ty}`"
			))
			.with_label(reference.primary_label().with_message(label));
		if let Some((source, owner)) = source {
			diagnostic = diagnostic.with_label(
				self.binding_span(source).secondary_label().with_message(
					match owner.name(self.defs) {
						Some(owner) => format!(
							"required by this bound in `{}`",
							self.strings.resolve(owner.inner).unwrap()
						),
						None => "required by this bound".to_owned(),
					},
				),
			);
		}
		if value.is_none() {
			diagnostic = diagnostic.with_note(format!(
				"state it in a bound: `where {{ const {name}: {ty} }}`"
			));
		}
		diagnostic
	}
}
