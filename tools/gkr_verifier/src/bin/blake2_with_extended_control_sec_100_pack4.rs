#![no_std]
#![no_main]

// The PACKED-base-commitment variant of `blake2_with_extended_control_sec_100`:
// the same 2^20 circuit proved with `ProverConfig::pack_log2 = 4` (2^24 WHIR
// message). Verifies `prover/test_proofs/blake2_with_extended_control_sec_100_pack4_gkr_proof.json`.
#[path = "../../../../verifier/src/generated/blake2_with_extended_control/sec_100_pack4/mod.rs"]
mod generated_gkr;

include!("../common.rs");
