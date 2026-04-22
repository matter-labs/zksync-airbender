// Alias external crates explicitly so the generated layout code resolves them
// unambiguously even when this verifier crate re-exports similarly named modules.
use ::field as field_crate;
use ::verifier_common as verifier_common_crate;
use field_crate::Mersenne31Field;
use verifier_common_crate::cs::definitions::*;

include!("../generated/circuit_layout.rs");
