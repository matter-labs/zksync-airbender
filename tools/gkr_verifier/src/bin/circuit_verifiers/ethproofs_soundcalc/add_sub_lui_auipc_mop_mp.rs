#![no_std]
#![no_main]

// ONE-OFF experiment: the add/sub ethproofs verifier with pruned Merkle multiproofs
// (`verifier/src/generated/add_sub_lui_auipc_mop/ethproofs_soundcalc_mp`, generated from
// the fixture config with `merkle_multiproofs: true`).
#[path = "../../../../../../verifier/src/generated/add_sub_lui_auipc_mop/ethproofs_soundcalc_mp/mod.rs"]
mod generated_gkr;

include!("../../../common.rs");
