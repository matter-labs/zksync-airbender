#![no_std]
#![no_main]

// Blake base-round comparison sweep variant of `blake2_with_extended_control`
// (pessimistic conjecture): physical packing 2^4, two values per column per base leaf. Verifies
// `prover/test_proofs/blake2_with_extended_control_sec_100_pack4_gkr_proof.json`.
#[path = "../../../../../../verifier/src/generated/blake2_with_extended_control/pessimistic_conjecture_pack4/mod.rs"]
mod generated_gkr;

include!("../../../common.rs");
