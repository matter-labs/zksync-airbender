#![no_std]
#![no_main]

// Blake base-round comparison sweep variant of `blake2_with_extended_control_sec_100`:
// physical packing 2^2, two values per column per base leaf. Verifies
// `prover/test_proofs/blake2_with_extended_control_sec_100_pack2_gkr_proof.json`.
#[path = "../../../../verifier/src/generated/blake2_with_extended_control/sec_100_pack2/mod.rs"]
mod generated_gkr;

include!("../common.rs");
