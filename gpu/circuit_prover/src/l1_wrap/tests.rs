use super::geometry::cpu_tests::wrap_geometry;
use super::inputs::ALLOCATOR_BLOCK_BYTES;
use super::*;
use crate::proof::memory_policy::presets::INPUTS_RESERVE_BYTES;
use gpu_prover_context::ProverContextConfig;
use gpu_trace::witness::circuit_type::CircuitType;
use std::alloc::Global;

#[test]
fn cpu_l1_inputs_fit_reserve() {
    assert_eq!(
        ALLOCATOR_BLOCK_BYTES,
        1 << ProverContextConfig::default().allocator_block_log_size
    );
    let (geometry, _) = wrap_geometry(CircuitType::L1Wrap);
    let bytes = L1WrapInputs::<'static, Global>::phase_one_capacity_bytes(
        &geometry,
        crate::proof::memory_policy::presets::l1_wrap::PARTIAL_TREES.setup,
    );
    let mib = 1 << 20;
    // Tracing data, I&T pages/values/timestamps, decoder, transcript prefix,
    // then the setup's raw evaluations, packed monomials and depth-10 trees.
    assert_eq!(bytes, (112 + 1 + 16 + 32 + 3 + 1 + 320 + 512 + 64) * mib);
    assert!(bytes <= INPUTS_RESERVE_BYTES);
}

#[test]
fn cpu_l1_whir_slab_preserves_the_committed_proof() {
    use gpu_core::primitives::field::PR;
    use gpu_gkr::proth120::programs::GkrProgramsPr;
    use gpu_gkr::proth120::proof_layout::{ProofLayoutPr, WhirBaseOpeningsLayoutPr};
    use gpu_whir::proth120::L1WhirReadback;
    use prover::gkr::whir::BaseFieldQuery;
    use serde::Deserialize;
    use std::ops::Range;
    use std::sync::Arc;

    #[derive(Deserialize)]
    struct Reference {
        l1: Bundle,
    }
    #[derive(Deserialize)]
    struct Bundle {
        proof: L1Proof,
    }
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../prover_pipeline/fixtures/l1_reference_2p21/l1.json");
    let reference: Reference = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    let expected = &reference.l1.proof.whir_proof;
    let (_, config) = wrap_geometry(CircuitType::L1Wrap21);
    let programs = GkrProgramsPr::compile(
        CircuitType::L1Wrap21,
        Arc::new(super::geometry::cpu_tests::committed_layout(
            CircuitType::L1Wrap21,
        )),
    );
    let layout = Arc::new(ProofLayoutPr::new(&programs, &config));
    #[repr(align(32))]
    #[derive(Clone)]
    struct Block {
        bytes: [u8; 32],
    }
    let mut storage = vec![Block { bytes: [0; 32] }; layout.bytes_len().div_ceil(32)];
    // SAFETY: Block is exactly 32 bytes with 32-byte alignment; all bytes are initialized.
    let bytes = unsafe {
        std::slice::from_raw_parts_mut(storage[0].bytes.as_mut_ptr(), storage.len() * 32)
    };
    fn write<T: Copy>(bytes: &mut [u8], range: &Range<usize>, values: &[T]) {
        assert_eq!(range.len(), size_of_val(values));
        // SAFETY: these proof types are initialized PR/u32/u64/Digest scalars with no padding.
        let source = unsafe {
            std::slice::from_raw_parts(values.as_ptr().cast::<u8>(), size_of_val(values))
        };
        bytes[range.clone()].copy_from_slice(source);
    }
    let fill_base =
        |bytes: &mut [u8],
         target: &WhirBaseOpeningsLayoutPr,
         queries: &[BaseFieldQuery<PR, crate::upstream::Keccak256MerkleTreeWithCap>]| {
            let leaves: Vec<_> = queries
                .iter()
                .flat_map(|q| q.leaf_values_concatenated.iter().copied())
                .collect();
            let paths: Vec<_> = queries
                .iter()
                .flat_map(|q| q.path.iter().copied())
                .collect();
            let indexes: Vec<u32> = queries.iter().map(|q| q.index as u32).collect();
            write(bytes, &target.leaves, &leaves);
            write(bytes, &target.paths, &paths);
            write(bytes, &target.tree_indexes, &indexes);
        };
    fill_base(
        bytes,
        &layout.whir.memory,
        &expected.memory_commitment.queries,
    );
    fill_base(
        bytes,
        &layout.whir.setup,
        &expected.setup_commitment.queries,
    );
    let mut ood = Vec::new();
    let mut polys: Vec<PR> = expected
        .base_sumcheck_polys
        .iter()
        .flatten()
        .copied()
        .collect();
    let mut nonces = vec![expected.base_queries_pow_nonce];
    assert_eq!(
        layout.whir.intermediate.len(),
        expected.intermediate_whir_oracles.len()
    );
    for (target, oracle) in layout
        .whir
        .intermediate
        .iter()
        .zip(&expected.intermediate_whir_oracles)
    {
        write(bytes, &target.cap, &oracle.commitment.cap.cap);
        let leaves: Vec<_> = oracle
            .queries
            .iter()
            .flat_map(|q| q.leaf_values_concatenated.iter().copied())
            .collect();
        let paths: Vec<_> = oracle
            .queries
            .iter()
            .flat_map(|q| q.path.iter().copied())
            .collect();
        let indexes: Vec<u32> = oracle.queries.iter().map(|q| q.index as u32).collect();
        write(bytes, &target.openings.leaves, &leaves);
        write(bytes, &target.openings.paths, &paths);
        write(bytes, &target.openings.tree_indexes, &indexes);
        ood.extend_from_slice(&oracle.ood_samples);
        polys.extend(oracle.sumcheck_polys.iter().flatten().copied());
        nonces.push(oracle.queries_pow_nonce);
    }
    write(
        bytes,
        &layout.whir.memory_cap,
        &expected.memory_commitment.commitment.cap.cap,
    );
    write(bytes, &layout.whir.ood_samples, &ood);
    write(bytes, &layout.whir.sumcheck_polys, &polys);
    write(bytes, &layout.whir.pow_nonces, &nonces);
    write(
        bytes,
        &layout.whir.final_monomials,
        &expected.final_monomials,
    );
    let readback = L1WhirReadback::new(
        Arc::clone(&layout),
        config.whir_schedule,
        expected.setup_commitment.commitment.cap.cap.clone(),
    );
    let actual = readback.assemble(
        bytes,
        &expected.memory_commitment.evals,
        &expected.setup_commitment.evals,
        expected.batching_challenge_pow_nonce,
    );
    assert_eq!(
        serde_json::to_vec(&actual).unwrap(),
        serde_json::to_vec(expected).unwrap()
    );
}
