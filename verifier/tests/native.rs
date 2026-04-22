#![cfg(feature = "gkr_verify")]

#[macro_use]
mod common;

use verifier_common::errors::DebugErrorCreator;
use verifier_common::prover::nd_source_std::{set_iterator, ThreadLocalBasedSource};

fn run_native(name: &str) {
    let (nds, external_challenges) = common::load_nds(name);
    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name(format!("gkr verifier {}", name))
            .stack_size(common::VERIFIER_STACK_SIZE)
            .spawn_scoped(s, move || {
                set_iterator(nds.into_iter());
                with_circuit!(name, |m| {
                    m::verify::<ThreadLocalBasedSource, DebugErrorCreator>(&external_challenges)
                        .unwrap_or_else(|e| panic!("{} failed: {:?}", name, e));
                });
            })
            .expect("failed to spawn verifier thread");

        match handle.join() {
            Ok(()) => println!("{}: verification passed", name),
            Err(e) => std::panic::resume_unwind(e),
        }
    });
}

macro_rules! generate_native_tests {
    ($($name:ident: $schedule:ident: $layout_suffix:expr),* $(,)?) => {
        $(
            #[test]
            fn $name() {
                run_native(stringify!($name));
            }
        )*
    };
}
verifier_common::gkr_circuits!(generate_native_tests);

// #[test]
// fn oracle_cap_ordering_matches_nds() {
//     use verifier_common::blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;

//     for circuit_data in common::CIRCUITS.iter() {
//         let nds = circuit_data.load_nds();
//         let proof = circuit_data.proof();

//         let caps_by_eval_idx = [
//             &proof.whir_proof.memory_commitment.commitment.cap,
//             &proof.whir_proof.witness_commitment.commitment.cap,
//             &proof.whir_proof.setup_commitment.commitment.cap,
//         ];

//         with_circuit!(circuit_data.name, |m| {
//             let offsets = m::constants::ORACLE_CAP_TRANSCRIPT_OFFSETS;
//             let cap_words = m::constants::ORACLE_CAP_WORDS;
//             let caps_base = m::constants::CAPS_OFFSET_IN_TRANSCRIPT;

//             for oracle_idx in 0..m::constants::NUM_ORACLES {
//                 let nds_start = caps_base + offsets[oracle_idx];
//                 let nds_cap = &nds[nds_start..nds_start + cap_words[oracle_idx]];

//                 let mut expected = Vec::new();
//                 for hash in caps_by_eval_idx[oracle_idx].cap.iter() {
//                     expected.extend_from_slice(hash);
//                 }

//                 assert_eq!(
//                     nds_cap,
//                     &expected[..],
//                     "{}: oracle {} cap data mismatch at NDS offset {}",
//                     circuit_data.name,
//                     oracle_idx,
//                     nds_start
//                 );
//             }
//         });
//     }
// }

// #[test]
// fn initial_whir_claim_indices_mapping_is_correct() {
//     use verifier_common::cs::definitions::GKRAddress;

//     for circuit_data in common::CIRCUITS.iter() {
//         with_circuit!(circuit_data.name, |m| {
//             let sorted_addrs = m::constants::LAYER_0_SORTED_ADDRS;
//             let indices = m::constants::INITIAL_WHIR_CLAIM_INDICES;
//             let num_cols = m::constants::ORACLE_NUM_COLS;
//             let total_cols = m::constants::TOTAL_ORACLE_COLS;

//             let mem_count = num_cols[0];
//             let wit_count = num_cols[1];

//             for col in 0..total_cols {
//                 let claim_idx = indices[col];
//                 assert!(
//                     claim_idx < sorted_addrs.len(),
//                     "{}: INITIAL_WHIR_CLAIM_INDICES[{}] = {} out of bounds for LAYER_0_SORTED_ADDRS (len {})",
//                     circuit_data.name, col, claim_idx, sorted_addrs.len()
//                 );
//                 let actual_addr = sorted_addrs[claim_idx];

//                 let expected_addr = if col < mem_count {
//                     GKRAddress::BaseLayerMemory(col)
//                 } else if col < mem_count + wit_count {
//                     GKRAddress::BaseLayerWitness(col - mem_count)
//                 } else {
//                     GKRAddress::Setup(col - mem_count - wit_count)
//                 };

//                 assert_eq!(
//                     actual_addr, expected_addr,
//                     "{}: WHIR column {} (oracle-order [mem,wit,setup]) maps via INITIAL_WHIR_CLAIM_INDICES[{}]={} to LAYER_0_SORTED_ADDRS[{}]={:?}, expected {:?}",
//                     circuit_data.name, col, col, claim_idx, claim_idx, actual_addr, expected_addr
//                 );
//             }
//         });
//     }
// }
