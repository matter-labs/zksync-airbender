use super::*;
use prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture as packed_config;

#[test]
#[ignore = "fresh CPU merged cap parity through the combined stage1 producer"]
fn packed_merged_commit_unpacked_cpu_parity() {
    use crate::proof::merged_commitment::{
        commit_merged_from_transfers_for_geometry, validate_merged_commitment_geometry,
        GpuGKRMergedCommitTransfer,
    };
    use gpu_gkr::setup::GpuGKRSetupTransfer;
    // CPU-expressible test construction; canonical BF configs stay unchanged.
    let mut config = packed_config(20, 0, SecurityLevel::Sec100);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    let fixture = proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    let base = &fixture.base;
    let geometry = BaseCommitmentGeometry::from_config(
        &base.prover_config,
        BaseColumns::of(&base.compiled_circuit),
    )
    .unwrap();
    validate_merged_commitment_geometry(&base.prover_config, &geometry, &base.compiled_circuit);
    assert_eq!(
        geometry.oracle(BaseOracleRole::Memory).logical_columns(),
        763
    );
    assert_eq!(
        geometry.oracle(BaseOracleRole::Witness).logical_columns(),
        0
    );
    let baseline = base.context.get_used_mem_current();
    let setup = GpuGKRSetupTransfer::new(
        Arc::clone(base.gpu_setup_host.as_ref().unwrap()),
        &base.context,
    )
    .unwrap();
    let trace = TracingDataTransfer::new(
        base.tracing_data_host.clone(),
        base.compiled_circuit.trace_len,
        &base.context,
    )
    .unwrap();
    let mut inputs =
        GpuGKRMergedCommitTransfer::<Global>::new(setup, None, None, Some(trace), &base.context)
            .unwrap();
    inputs.schedule(&base.context).unwrap();
    let job = commit_merged_from_transfers_for_geometry(
        &base.gkr_programs,
        &base.prover_config,
        geometry,
        inputs,
        &base.context,
    )
    .unwrap();
    assert_eq!(job.base_commitment_geometry(), Some(geometry));
    let (caps, _) = job.finish().unwrap();
    assert_eq!(
        caps, base.memory_tree_caps,
        "GPU combined cap differs from the fresh CPU merged proof"
    );
    assert_eq!(base.context.get_used_mem_current(), baseline);
}

fn gpu_memory_caps(
    base: &BasicUnrolledFixture,
    geometry: BaseCommitmentGeometry,
) -> Vec<MerkleTreeCapVarLength> {
    let context = &base.context;
    let baseline = context.get_used_mem_current();
    let decoder = base
        .compiled_circuit
        .has_decoder_lookup
        .then(|| DecoderTableTransfer::new(Arc::clone(&base.decoder_table_host), context).unwrap());
    let inits = base.inits_and_teardowns_host.clone().map(|host| {
        InitsAndTeardownsTransfer::new(
            Some(host),
            base.compiled_circuit.memory_layout.teardown_sets.len(),
            base.compiled_circuit.trace_len,
            context,
        )
        .unwrap()
    });
    let trace = TracingDataTransfer::new(
        base.tracing_data_host.clone(),
        base.compiled_circuit.trace_len,
        context,
    )
    .unwrap();
    let job = if geometry.commitment_mode() == CommitmentMode::MergedMemoryAndWitness {
        use crate::proof::merged_commitment::{
            commit_merged_from_transfers_for_geometry, GpuGKRMergedCommitTransfer,
        };
        let setup = gpu_gkr::setup::GpuGKRSetupTransfer::new(
            Arc::clone(base.gpu_setup_host.as_ref().unwrap()),
            context,
        )
        .unwrap();
        let mut inputs =
            GpuGKRMergedCommitTransfer::new(setup, decoder, inits, Some(trace), context).unwrap();
        inputs.schedule(context).unwrap();
        commit_merged_from_transfers_for_geometry(
            &base.gkr_programs,
            &base.prover_config,
            geometry,
            inputs,
            context,
        )
        .unwrap()
    } else {
        let mut inputs = gpu_trace::trace::memory_transfer::GpuGKRCommitMemoryTransfer::new(
            decoder,
            inits,
            Some(trace),
            context,
        )
        .unwrap();
        inputs.schedule(context).unwrap();
        gpu_trace::trace::memory::commit_memory_from_transfers_for_geometry(
            base.circuit_type,
            &base.compiled_circuit,
            inputs,
            &base.prover_config,
            geometry,
            context,
        )
        .unwrap()
    };
    assert_eq!(job.base_commitment_geometry(), Some(geometry));
    let (caps, _) = job.finish().unwrap();
    assert_eq!(context.get_used_mem_current(), baseline);
    assert_eq!(
        caps, base.memory_tree_caps,
        "GPU memory caps differ from fresh CPU proof caps"
    );
    caps
}

pub(super) fn geometry_proof(mut fixture: BasicUnrolledProofFixture) {
    let base = &mut fixture.base;
    let policy = ProofMemoryPolicy::default();
    let preflight = base.dr_tail_plan_for_policy(policy).unwrap();
    let geometry = preflight.geometry();
    let expected_batching_bits = base.prover_config.base_round().batching_pow_bits::<BF, E4>(
        base.prover_config.security_level.security_bits(),
        geometry.message_size_log2(),
        geometry.total_physical_columns(),
    );
    if !geometry.is_virtual_packing() {
        assert_eq!(expected_batching_bits, 8);
    }
    assert!(gpu_trace::trace::memory::uses_base_commitment_geometry(
        &geometry
    ));
    assert_eq!(
        preflight.batching_pow_bits_for_test(),
        expected_batching_bits
    );
    eprintln!(
        "packed preflight: m={}, Q={}, batching_bits={expected_batching_bits}",
        geometry.message_size_log2(),
        geometry.total_physical_columns()
    );
    assert_eq!(
        geometry.message_size_log2(),
        base.prover_config.whir_message_size_log2()
    );
    if geometry.commitment_mode() == CommitmentMode::MergedMemoryAndWitness {
        assert_eq!((geometry.trace_len_log2(), geometry.pack_log2()), (20, 4));
        assert_eq!(
            geometry.oracle(BaseOracleRole::Memory).logical_columns(),
            763
        );
        assert_eq!(
            geometry.oracle(BaseOracleRole::Memory).padded_columns(),
            768
        );
        assert_eq!(
            geometry.oracle(BaseOracleRole::Memory).physical_columns(),
            48
        );
        assert_eq!(
            geometry.oracle(BaseOracleRole::Witness).physical_columns(),
            0
        );
        assert_eq!(geometry.oracle(BaseOracleRole::Setup).physical_columns(), 1);
        assert_eq!(geometry.total_physical_columns(), 49);
    }
    if geometry.is_virtual_packing() {
        assert_eq!(
            base.prover_config,
            base.circuit_type
                .prover_config(base.prover_config.security_level)
        );
        assert_eq!(geometry.message_size_log2(), 22);
        assert_eq!(
            geometry.logical_columns(),
            BaseColumns::of(&base.compiled_circuit)
        );
        assert_eq!(
            geometry.total_physical_columns(),
            BaseColumns::of(&base.compiled_circuit).committed_polys(
                base.prover_config.pack_log2(),
                base.prover_config.merged_memory_and_witness()
            )
        );
    } else if geometry.trace_len_log2() == 23 {
        assert_eq!(
            geometry.logical_columns(),
            BaseColumns {
                memory: 38,
                witness: 58,
                setup: 10
            }
        );
        assert!(
            base.inits_and_teardowns_host.is_some(),
            "unified gate must exercise inits/teardowns"
        );
    } else {
        assert_eq!(
            geometry.logical_columns(),
            BaseColumns {
                memory: 225,
                witness: 538,
                setup: 6
            }
        );
    }
    // Replace CPU fixture caps with actual GPU producer output before proving.
    base.memory_tree_caps = gpu_memory_caps(base, geometry);
    let setup_and_memory_peak = base.context.get_used_mem_peak();
    base.context.reset_used_mem_peak();
    let baseline = base.context.get_used_mem_current();
    let mut jobs = Vec::new();
    for _ in 0..2 {
        // Bundle allocation fence follows the packed setup tail memset.
        let mut inputs = base.create_transfers().unwrap();
        inputs.schedule(&base.context).unwrap();
        jobs.push(
            prove::<Global>(
                &base.gkr_programs,
                &base.prover_config,
                base.final_trace_size_log_2,
                inputs,
                &preflight,
                policy,
                &base.context,
            )
            .unwrap(),
        );
        assert_eq!(
            base.context.get_used_mem_current(),
            baseline,
            "prove must retire all reservations before finish"
        );
    }
    let cpu_bytes = serde_json::to_vec(&fixture.expected_cpu_proof).unwrap();
    for (index, job) in jobs.into_iter().enumerate() {
        let (proof, _) = job.finish().unwrap();
        for (name, actual, expected) in [
            (
                "memory",
                &proof.whir_proof.memory_commitment,
                &fixture.expected_cpu_proof.whir_proof.memory_commitment,
            ),
            (
                "witness",
                &proof.whir_proof.witness_commitment,
                &fixture.expected_cpu_proof.whir_proof.witness_commitment,
            ),
            (
                "setup",
                &proof.whir_proof.setup_commitment,
                &fixture.expected_cpu_proof.whir_proof.setup_commitment,
            ),
        ] {
            assert_eq!(
                actual.commitment.cap, expected.commitment.cap,
                "{name} caps before batching"
            );
            assert_eq!(
                actual.num_columns, expected.num_columns,
                "{name} physical width"
            );
            assert_eq!(
                actual.evals, expected.evals,
                "{name} physical claims before batching"
            );
        }
        assert_gkr_proof_eq_for_test(&proof, &fixture.expected_cpu_proof);
        let gpu_bytes = serde_json::to_vec(&proof).unwrap();
        assert!(
            gpu_bytes == cpu_bytes,
            "queued proof {index} differs from fresh CPU: GPUlen={}, CPUlen={}, first={:?}",
            gpu_bytes.len(),
            cpu_bytes.len(),
            gpu_bytes.iter().zip(&cpu_bytes).position(|(a, b)| a != b)
        );
        eprintln!(
            "queued packed proof {index}: serialized equality, {} bytes",
            gpu_bytes.len()
        );
    }
    assert_eq!(base.context.get_used_mem_current(), baseline);
    eprintln!("base proof resources: circuit={:?}, arena_bytes={}, setup_memory_pool_peak_bytes={}, proof_pool_peak_bytes={}, baseline_bytes={}",
        base.circuit_type,base.context.get_mem_size(),setup_and_memory_peak,
        base.context.get_used_mem_peak(),baseline);
}

#[test]
#[ignore = "fresh CPU/GPU production physical packed proof parity"]
fn packed_full_proof_blake20_pack4_cpu_parity() {
    geometry_proof(proof_matrix::prepare_blake2_with_compression_proof_fixture_with_packing(4));
}

#[test]
#[ignore = "fresh CPU/GPU production physical packed proof parity with unified inits/teardowns"]
fn packed_full_proof_unified23_pack1_cpu_parity() {
    geometry_proof(prepare_unified_proof_fixture_with_packing(1));
}

#[test]
#[ignore = "fresh CPU/GPU physical-only Blake k2/f1 proof parity"]
fn packed_full_proof_blake20_pack2_cpu_parity() {
    geometry_proof(proof_matrix::prepare_blake2_with_compression_proof_fixture_with_packing(2));
}

#[test]
#[ignore = "fresh CPU/GPU merged physical proof parity"]
fn packed_full_proof_blake20_pack4_merged_cpu_parity() {
    // The CPU already exposes this mode; no canonical BF default selects it.
    let mut config = packed_config(20, 4, SecurityLevel::Sec100);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    geometry_proof(proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config));
}
