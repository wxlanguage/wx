//! Exact decimal literals in flat, source-independent storage. Big integers
//! are temporary parsing/conversion values; expressions own only limb ranges.

use num_bigint::{BigInt, BigUint, Sign};

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct LimbRange {
	start: u32,
	len: u32,
}

/// `(-1)^negative * significand * 10^(signed exponent)`. Range equality is
/// storage identity, not numeric equality. Negation preserves negative zero.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) struct DecimalFloat {
	significand: LimbRange,
	exponent: LimbRange,
	pub(super) negative: bool,
	exponent_negative: bool,
}

#[derive(Default)]
pub(super) struct NumberStorage {
	/// Unsigned base-2^32 magnitudes, least significant limb first.
	limbs: Vec<u32>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(super) enum NumberError {
	InvalidLiteral,
	StorageLimit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum FloatRangeError {
	TooLarge,
	TooSmall,
}

impl NumberStorage {
	/// Parse the unsigned decimal spelling accepted by WX's lexer. Decimal
	/// zeros are removed before converting the significand to binary limbs.
	pub(super) fn parse_float(
		&mut self,
		text: &str,
	) -> Result<DecimalFloat, NumberError> {
		let (mantissa, exponent) =
			text.split_once(['e', 'E']).unwrap_or((text, "0"));
		let mut exponent = BigInt::parse_bytes(exponent.as_bytes(), 10)
			.ok_or(NumberError::InvalidLiteral)?;
		let fraction_len = mantissa
			.split_once('.')
			.map_or(0, |(_, fraction)| fraction.len());
		let digits: Vec<_> = mantissa.bytes().filter(|&b| b != b'.').collect();
		if digits.is_empty()
			|| !digits.iter().all(u8::is_ascii_digit)
			|| mantissa.bytes().filter(|&b| b == b'.').count() > 1
		{
			return Err(NumberError::InvalidLiteral);
		}
		let significand =
			if let Some(first) = digits.iter().position(|&b| b != b'0') {
				let end = digits.iter().rposition(|&b| b != b'0').unwrap() + 1;
				exponent -= BigInt::from(fraction_len);
				exponent += BigInt::from(digits.len() - end);
				BigUint::parse_bytes(&digits[first..end], 10)
					.ok_or(NumberError::InvalidLiteral)?
			} else {
				// Every spelling of zero has the same unsigned numeric value.
				exponent = BigInt::from(0);
				BigUint::default()
			};
		let significand_len = significand.iter_u32_digits().len();
		let exponent_len = exponent.magnitude().iter_u32_digits().len();
		let total = significand_len
			.checked_add(exponent_len)
			.ok_or(NumberError::StorageLimit)?;
		let end = self
			.limbs
			.len()
			.checked_add(total)
			.ok_or(NumberError::StorageLimit)?;
		u32::try_from(end).map_err(|_| NumberError::StorageLimit)?;
		self.limbs
			.try_reserve(total)
			.map_err(|_| NumberError::StorageLimit)?;
		// All capacity checks precede either append, so failure leaves storage intact.
		let significand_range = LimbRange {
			start: self.limbs.len() as u32,
			len: significand_len as u32,
		};
		self.limbs.extend(significand.iter_u32_digits());
		let exponent_range = LimbRange {
			start: self.limbs.len() as u32,
			len: exponent_len as u32,
		};
		self.limbs.extend(exponent.magnitude().iter_u32_digits());
		Ok(DecimalFloat {
			significand: significand_range,
			exponent: exponent_range,
			negative: false,
			exponent_negative: exponent.sign() == Sign::Minus,
		})
	}

	fn magnitude(&self, range: LimbRange) -> BigUint {
		let start = range.start as usize;
		BigUint::from_slice(&self.limbs[start..start + range.len as usize])
	}

	/// Exact scientific notation for display and target-width conversion.
	pub(super) fn decimal_text(&self, value: DecimalFloat) -> String {
		let mut text = String::new();
		if value.negative {
			text.push('-');
		}
		text.push_str(&self.magnitude(value.significand).to_str_radix(10));
		text.push('e');
		if value.exponent_negative {
			text.push('-');
		}
		text.push_str(&self.magnitude(value.exponent).to_str_radix(10));
		text
	}

	pub(super) fn is_zero(&self, value: DecimalFloat) -> bool {
		value.significand.len == 0
	}

	/// Let Rust's parser handle rounding directly at the requested width.
	pub(super) fn to_f32(
		&self,
		value: DecimalFloat,
	) -> Result<f32, FloatRangeError> {
		let read = self
			.decimal_text(value)
			.parse::<f32>()
			.expect("exact decimal storage formats a valid float");
		self.check_float_range(value, f64::from(read))?;
		Ok(read)
	}

	pub(super) fn to_f64(
		&self,
		value: DecimalFloat,
	) -> Result<f64, FloatRangeError> {
		let read = self
			.decimal_text(value)
			.parse::<f64>()
			.expect("exact decimal storage formats a valid float");
		self.check_float_range(value, read)?;
		Ok(read)
	}

	fn check_float_range(
		&self,
		literal: DecimalFloat,
		read: f64,
	) -> Result<(), FloatRangeError> {
		if read.is_infinite() {
			Err(FloatRangeError::TooLarge)
		} else if read == 0.0 && !self.is_zero(literal) {
			Err(FloatRangeError::TooSmall)
		} else {
			Ok(())
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn target_conversion_accepts_subnormals_and_reports_range_errors() {
		let mut numbers = NumberStorage::default();
		for (source, expected) in [
			("1e-45", Ok(1)),
			("1.1754943508222875e-38", Ok(0x0080_0000)),
			("3.4028234663852886e38", Ok(0x7f7f_ffff)),
			("1e-46", Err(FloatRangeError::TooSmall)),
			("1e39", Err(FloatRangeError::TooLarge)),
		] {
			let value = numbers.parse_float(source).unwrap();
			assert_eq!(
				numbers.to_f32(value).map(f32::to_bits),
				expected,
				"{source}"
			);
		}
		for (source, expected) in [
			("5e-324", Ok(1)),
			("2.2250738585072014e-308", Ok(0x0010_0000_0000_0000)),
			("1.7976931348623157e308", Ok(0x7fef_ffff_ffff_ffff)),
			("1e-324", Err(FloatRangeError::TooSmall)),
			("1e309", Err(FloatRangeError::TooLarge)),
		] {
			let value = numbers.parse_float(source).unwrap();
			assert_eq!(
				numbers.to_f64(value).map(f64::to_bits),
				expected,
				"{source}"
			);
		}
	}

	#[test]
	fn decimal_values_are_normalized_without_precision_limits() {
		let mut numbers = NumberStorage::default();
		for (source, expected) in [
			("1.25", "125e-2"),
			("001.2500e+2", "125e0"),
			("0.0e999999999999999999999999999999999999999999", "0e0"),
			(
				"1.234567890123456789012345678901234567890123456789",
				"1234567890123456789012345678901234567890123456789e-48",
			),
			(
				"1e999999999999999999999999999999999999999999",
				"1e999999999999999999999999999999999999999999",
			),
			(
				"1e-999999999999999999999999999999999999999999",
				"1e-999999999999999999999999999999999999999999",
			),
		] {
			let value = numbers.parse_float(source).unwrap();
			assert_eq!(numbers.decimal_text(value), expected);
		}
		let mut zero = numbers.parse_float("0.0").unwrap();
		zero.negative = true;
		assert!(numbers.is_zero(zero));
		assert_eq!(numbers.decimal_text(zero), "-0e0");
		assert_eq!(
			numbers.to_f32(zero).unwrap().to_bits(),
			(-0.0_f32).to_bits()
		);
		assert_eq!(
			numbers.to_f64(zero).unwrap().to_bits(),
			(-0.0_f64).to_bits()
		);
	}
}
