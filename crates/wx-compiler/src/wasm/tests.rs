use super::*;

#[test]
fn flatten_type_to_scalars_unit_and_never_produce_no_slots() {
	assert_eq!(flatten_type_to_scalars(mir::Type::Unit, &[]), vec![]);
	assert_eq!(flatten_type_to_scalars(mir::Type::Never, &[]), vec![]);
}

#[test]
fn flatten_type_to_scalars_scalar_is_one_slot() {
	assert_eq!(
		flatten_type_to_scalars(mir::Type::I64, &[]),
		vec![ScalarType::I64]
	);
}
