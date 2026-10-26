#![no_std]
#![no_main]

// Blake base-round comparison sweep variant of `blake2_with_extended_control`
// (pessimistic conjecture): no physical packing, one value per column per base leaf (virtual packing). Verifies
// `prover/test_proofs/blake2_with_extended_control_sec_100_virtual_gkr_proof.json`.
#[path = "../../../../../../verifier/src/generated/blake2_with_extended_control/pessimistic_conjecture_virtual/mod.rs"]
mod generated_gkr;

include!("../../../common.rs");
