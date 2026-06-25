use prover::field::Mersenne31Field;
use prover::field::PrimeField;

/// Trait for obtaining information from the circuit's field that is useful for building IR.
pub trait FieldInfo: PrimeField {
    /// Returns the name of the field in a format compatible with LLZK.
    fn field_name() -> &'static str;
    /// Indicate whether the field is built in to LLZK or if it needs to be specified
    /// via a field.spec attribute in the LLZK module.
    fn is_built_in() -> bool;
}

impl FieldInfo for Mersenne31Field {
    fn field_name() -> &'static str {
        "mersenne31"
    }

    fn is_built_in() -> bool {
        true
    }
}
