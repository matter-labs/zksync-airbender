use super::*;
use prover::tests::gkr::orchestration::canonical_fixtures::canonical_circuits;
use std::collections::BTreeSet;

/// Queue both jobs before either finish so the second reuses retired blocks.
fn run_multi_schedule(fixture: &BasicUnrolledProofFixture) {
    let base = &fixture.base;
    let preparation_peak = base.context.get_used_mem_peak();
    let baseline = base.context.get_used_mem_current();
    base.context.reset_used_mem_peak();
    let jobs = [
        fixture.schedule_prove().unwrap(),
        fixture.schedule_prove().unwrap(),
    ];
    let mut checked = 0;
    for job in jobs {
        let (proof, _) = job.finish().unwrap();
        fixture.assert_proof(&proof);
        checked += 1;
        assert_eq!(
            base.context.get_used_mem_current(),
            baseline,
            "device memory must return to baseline after each finish"
        );
    }
    assert_eq!(checked, 2);
    record_test_resources(base, preparation_peak, checked);
}

fn canonical_case(circuit: CanonicalCircuit, mode: circuit_common::SoundnessMode) {
    let fixture = prepare_canonical_proof_fixture(circuit, mode);
    run_multi_schedule(&fixture);
}

macro_rules! canonical_matrix {
    ($(($p:ident, $e:ident, $profile:ident, $circuit:ident)),* $(,)?) => {
        const CANONICAL_GPU_CASES: &[(&str, CanonicalCircuit, circuit_common::SoundnessMode)] = &[
            $(
                (concat!("tests::proof_matrix::", stringify!($p)), CanonicalCircuit::$circuit, circuit_common::SoundnessMode::PessimisticConjecture),
                (concat!("tests::proof_matrix::", stringify!($e)), CanonicalCircuit::$circuit, circuit_common::SoundnessMode::EthproofsSoundnessCalc),
            )*
        ];
        $(
            #[test]
            #[ignore = "canonical GPU proof bytes and two-enqueue allocator coverage"]
            fn $p() { canonical_case(CanonicalCircuit::$circuit, circuit_common::SoundnessMode::PessimisticConjecture); }
            #[test]
            #[ignore = "canonical GPU proof bytes and two-enqueue allocator coverage"]
            fn $e() { canonical_case(CanonicalCircuit::$circuit, circuit_common::SoundnessMode::EthproofsSoundnessCalc); }
            #[test]
            #[ignore = "canonical GPU profile"]
            fn $profile() {
                run_profile(&prepare_canonical_proof_fixture(CanonicalCircuit::$circuit, circuit_common::SoundnessMode::DEFAULT));
            }
        )*
    };
}

canonical_matrix! {
    (canonical_add_sub_lui_auipc_mop_pessimistic_conjecture, canonical_add_sub_lui_auipc_mop_ethproofs_soundcalc, profile_add_sub_lui_auipc_mop, AddSubLuiAuipcMop),
    (canonical_jump_branch_slt_pessimistic_conjecture, canonical_jump_branch_slt_ethproofs_soundcalc, profile_jump_branch_slt, JumpBranchSlt),
    (canonical_shift_binop_pessimistic_conjecture, canonical_shift_binop_ethproofs_soundcalc, profile_shift_binop, ShiftBinop),
    (canonical_unsigned_mul_div_pessimistic_conjecture, canonical_unsigned_mul_div_ethproofs_soundcalc, profile_unsigned_mul_div, UnsignedMulDiv),
    (canonical_mem_word_only_pessimistic_conjecture, canonical_mem_word_only_ethproofs_soundcalc, profile_mem_word_only, MemWordOnly),
    (canonical_mem_subword_only_pessimistic_conjecture, canonical_mem_subword_only_ethproofs_soundcalc, profile_mem_subword_only, MemSubwordOnly),
    (canonical_inits_and_teardowns_pessimistic_conjecture, canonical_inits_and_teardowns_ethproofs_soundcalc, profile_inits_and_teardowns, InitsAndTeardowns),
    (canonical_unified_reduced_machine_pessimistic_conjecture, canonical_unified_reduced_machine_ethproofs_soundcalc, profile_unified_reduced_machine, UnifiedReducedMachine),
    (canonical_bigint_with_extended_control_pessimistic_conjecture, canonical_bigint_with_extended_control_ethproofs_soundcalc, profile_bigint_with_extended_control, BigintWithExtendedControl),
    (canonical_blake2_with_extended_control_pessimistic_conjecture, canonical_blake2_with_extended_control_ethproofs_soundcalc, profile_blake2_with_extended_control, Blake2WithExtendedControl),
    (canonical_keccak_special5_pessimistic_conjecture, canonical_keccak_special5_ethproofs_soundcalc, profile_keccak_special5, KeccakSpecial5),
    (canonical_keccak_column_parity_pessimistic_conjecture, canonical_keccak_column_parity_ethproofs_soundcalc, profile_keccak_column_parity, KeccakColumnParity),
    (canonical_keccak_theta_rho_pessimistic_conjecture, canonical_keccak_theta_rho_ethproofs_soundcalc, profile_keccak_theta_rho, KeccakThetaRho),
    (canonical_keccak_chi5_pessimistic_conjecture, canonical_keccak_chi5_ethproofs_soundcalc, profile_keccak_chi5, KeccakChi5),
}

const SPECIAL_CANONICAL_GPU_CASES: &[(&str, CanonicalCircuit, circuit_common::SoundnessMode)] = &[
    (
        "tests::proof_matrix::canonical_compression_pessimistic_conjecture",
        CanonicalCircuit::Compression,
        circuit_common::SoundnessMode::PessimisticConjecture,
    ),
    (
        "tests::proof_matrix::canonical_compression_ethproofs_soundcalc",
        CanonicalCircuit::Compression,
        circuit_common::SoundnessMode::EthproofsSoundnessCalc,
    ),
    (
        "tests::proof_matrix::canonical_compression_final_pessimistic_conjecture",
        CanonicalCircuit::CompressionFinal,
        circuit_common::SoundnessMode::PessimisticConjecture,
    ),
];

#[test]
#[ignore = "canonical GPU proof bytes and two-enqueue allocator coverage"]
fn canonical_compression_pessimistic_conjecture() {
    canonical_case(
        CanonicalCircuit::Compression,
        circuit_common::SoundnessMode::PessimisticConjecture,
    );
}

#[test]
#[ignore = "canonical GPU proof bytes and two-enqueue allocator coverage"]
fn canonical_compression_ethproofs_soundcalc() {
    canonical_case(
        CanonicalCircuit::Compression,
        circuit_common::SoundnessMode::EthproofsSoundnessCalc,
    );
}

#[test]
#[ignore = "canonical GPU proof bytes and two-enqueue allocator coverage"]
fn canonical_compression_final_pessimistic_conjecture() {
    canonical_case(
        CanonicalCircuit::CompressionFinal,
        circuit_common::SoundnessMode::PessimisticConjecture,
    );
}

#[test]
fn cpu_canonical_matrix_inventory() {
    let expected: BTreeSet<_> = circuit_common::SoundnessMode::ALL
        .iter()
        .flat_map(|&mode| {
            canonical_circuits(mode).map(move |circuit| {
                format!(
                    "tests::proof_matrix::canonical_{}_{}",
                    circuit.stem(),
                    mode.file_suffix()
                )
            })
        })
        .collect();
    assert_eq!(expected.len(), 31);
    let registered: BTreeSet<_> = CANONICAL_GPU_CASES
        .iter()
        .chain(SPECIAL_CANONICAL_GPU_CASES)
        .map(|&(name, circuit, mode)| {
            assert_eq!(
                name,
                format!(
                    "tests::proof_matrix::canonical_{}_{}",
                    circuit.stem(),
                    mode.file_suffix()
                )
            );
            name.to_owned()
        })
        .collect();
    assert_eq!(
        registered.len(),
        CANONICAL_GPU_CASES.len() + SPECIAL_CANONICAL_GPU_CASES.len(),
        "duplicate canonical GPU key"
    );
    assert_eq!(
        registered, expected,
        "GPU matrix differs from canonical input registry"
    );

    for &mode in circuit_common::SoundnessMode::ALL {
        let expected: BTreeSet<_> = canonical_circuits(mode)
            .map(|circuit| format!("{}.json.zlib", circuit.stem()))
            .collect();
        let actual: BTreeSet<_> = std::fs::read_dir(
            proof_fixtures::root()
                .join("fixtures/circuits")
                .join(mode.file_suffix()),
        )
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect();
        assert_eq!(actual, expected, "uncovered circuit fixture in {mode:?}");
    }
}

#[test]
#[ignore = "mixed-circuit queueing over canonical inputs"]
fn run_mixed_circuit_multi_schedule_test() {
    let add_sub = prepare_canonical_proof_fixture(
        CanonicalCircuit::AddSubLuiAuipcMop,
        circuit_common::SoundnessMode::DEFAULT,
    );
    // Both contexts use the default twiddle geometry. Keep Keccak's context
    // alive through finish: its construction replaces the shared twiddle pointers.
    let keccak = prepare_canonical_proof_fixture(
        CanonicalCircuit::KeccakSpecial5,
        circuit_common::SoundnessMode::DEFAULT,
    );
    let context = &add_sub.base.context;
    let preparation_peak = context.get_used_mem_peak();
    let baseline = context.get_used_mem_current();
    context.reset_used_mem_peak();
    let fixtures = [&add_sub, &keccak, &add_sub];
    let mut jobs = Vec::with_capacity(fixtures.len());
    for fixture in fixtures {
        let base = &fixture.base;
        let mut transfers = base.create_transfers_for_context(context).unwrap();
        transfers.schedule(context).unwrap();
        jobs.push(
            prove(
                crate::proof::BabyBearProofRequest::new(
                    &base.gkr_programs,
                    &base.prover_config,
                    base.final_trace_size_log_2,
                    transfers,
                    ProofMemoryPolicy::default(),
                    crate::proof::memory_policy::PartialTreePolicy::DEFAULT,
                ),
                context,
            )
            .unwrap(),
        );
        assert_eq!(context.get_used_mem_current(), baseline);
    }
    for (job, fixture) in jobs.into_iter().zip(fixtures) {
        let (proof, _) = job.finish().unwrap();
        fixture.assert_proof(&proof);
    }
    assert_eq!(context.get_used_mem_current(), baseline);
    record_test_resources(&add_sub.base, preparation_peak, 3);
}

pub(super) fn run_profile(fixture: &BasicUnrolledProofFixture) {
    let base = &fixture.base;
    let baseline = base.context.get_used_mem_current();
    let warm = base.schedule_transfers().unwrap();
    base.context.get_h2d_stream().synchronize().unwrap();
    let warm_job = base.prove(warm).unwrap();
    let (warm_proof, _warm_ms) = warm_job.finish().unwrap();

    fixture.assert_proof(&warm_proof);
    drop(warm_proof);
    let prof = base.schedule_transfers().unwrap();
    base.context.get_h2d_stream().synchronize().unwrap();
    base.context.reset_used_mem_peak();
    let (prof_proof, _prof_ms) = {
        let _range = scoped_range(
            Some("gpu_circuit_prover.tests"),
            "test.gpu.prove.profiled_call",
        );
        base.prove(prof).unwrap().finish().unwrap()
    };

    fixture.assert_proof(&prof_proof);
    drop(prof_proof);
    let peak = base.context.get_used_mem_peak();

    assert!(peak > baseline);
    assert_eq!(base.context.get_used_mem_current(), baseline);
}

fn assert_device_slices_equal_chunked<T>(
    label: &str,
    lhs: &era_cudart::slice::DeviceSlice<T>,
    rhs: &era_cudart::slice::DeviceSlice<T>,
    context: &ProverContext,
) where
    T: Copy + Default + PartialEq + std::fmt::Debug,
{
    assert_eq!(lhs.len(), rhs.len(), "{label} length mismatch");
    const CHUNK_BYTES: usize = 64 << 20;
    let chunk_len = (CHUNK_BYTES / std::mem::size_of::<T>()).max(1);
    let mut lhs_host = vec![T::default(); chunk_len.min(lhs.len())];
    let mut rhs_host = vec![T::default(); chunk_len.min(rhs.len())];
    for offset in (0..lhs.len()).step_by(chunk_len) {
        let len = chunk_len.min(lhs.len() - offset);
        memory_copy_async(
            &mut lhs_host[..len],
            &lhs[offset..offset + len],
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut rhs_host[..len],
            &rhs[offset..offset + len],
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        if lhs_host[..len] != rhs_host[..len] {
            let local = lhs_host[..len]
                .iter()
                .zip(&rhs_host[..len])
                .position(|(lhs, rhs)| lhs != rhs)
                .unwrap();
            assert_eq!(
                lhs_host[local],
                rhs_host[local],
                "{label} mismatch at element {}",
                offset + local
            );
        }
    }
}

fn run_stage1_buffer_parity(fixture: &BasicUnrolledFixture) {
    let preparation_peak = fixture.context.get_used_mem_peak();
    let baseline = fixture.context.get_used_mem_current();
    fixture.context.reset_used_mem_peak();
    {
        use gpu_gkr::proof_layout::GpuGKRTraceGeometry;
        use gpu_gkr::stage1::{
            generate_with_witness_strategy, GpuGKRStage1Output, WitnessGenerationStrategy,
        };

        let transfers = fixture.schedule_transfers().unwrap();
        transfers
            .transfer
            .ensure_transferred(&fixture.context)
            .unwrap();
        let setup = transfers
            .setup
            .as_ref()
            .expect("stage-1 parity fixture requires a setup transfer");
        let geometry = GpuGKRTraceGeometry {
            log_domain_size: setup.trace_holder.log_domain_size,
            log_lde_factor: setup.trace_holder.log_lde_factor,
            log_rows_per_leaf: setup.trace_holder.log_rows_per_leaf,
            log_tree_cap_size: setup.trace_holder.log_tree_cap_size,
        };
        let generate = |strategy| -> GpuGKRStage1Output {
            generate_with_witness_strategy(
                fixture.circuit_type,
                &fixture.compiled_circuit,
                geometry,
                BaseCommitmentGeometry::from_config(
                    &fixture.prover_config,
                    BaseColumns::of(&fixture.compiled_circuit),
                ),
                Some(setup.trace_holder.get_hypercube_evals()),
                transfers
                    .decoder
                    .as_ref()
                    .map(|decoder| &decoder.data_device[..]),
                transfers
                    .inits_and_teardowns
                    .as_ref()
                    .map(|transfer| &transfer.data_device),
                transfers
                    .tracing_data
                    .as_ref()
                    .map(|transfer| &transfer.data_device),
                None,
                &fixture.context,
                strategy,
            )
            .unwrap()
        };

        let split = generate(WitnessGenerationStrategy::Split);
        fixture.context.get_exec_stream().synchronize().unwrap();
        let fused = generate(WitnessGenerationStrategy::Fused);
        fixture.context.get_exec_stream().synchronize().unwrap();
        assert_device_slices_equal_chunked(
            "memory hypercube",
            split.memory_trace_holder.get_hypercube_evals(),
            fused.memory_trace_holder.get_hypercube_evals(),
            &fixture.context,
        );
        assert_device_slices_equal_chunked(
            "witness hypercube",
            split.witness_trace_holder.get_hypercube_evals(),
            fused.witness_trace_holder.get_hypercube_evals(),
            &fixture.context,
        );
        match (
            split.scratch_space_for_test(),
            fused.scratch_space_for_test(),
        ) {
            (Some(split), Some(fused)) => {
                assert_device_slices_equal_chunked("scratch", split, fused, &fixture.context)
            }
            (None, None) => {}
            _ => panic!("scratch allocation presence differs"),
        }
        assert_device_slices_equal_chunked(
            "generic/decoder mappings",
            split.lookup_mappings.generic_family(),
            fused.lookup_mappings.generic_family(),
            &fixture.context,
        );
        assert_device_slices_equal_chunked(
            "range-16 mappings",
            split.lookup_mappings.range_check_16(),
            fused.lookup_mappings.range_check_16(),
            &fixture.context,
        );
        assert_device_slices_equal_chunked(
            "timestamp mappings",
            split.lookup_mappings.timestamp(),
            fused.lookup_mappings.timestamp(),
            &fixture.context,
        );
    }
    assert_eq!(fixture.context.get_used_mem_current(), baseline);
    record_test_resources(fixture, preparation_peak, 0);
}

#[test]
#[ignore]
fn run_add_sub_stage1_buffer_parity_test() {
    run_stage1_buffer_parity(
        &prepare_canonical_proof_fixture(
            CanonicalCircuit::AddSubLuiAuipcMop,
            circuit_common::SoundnessMode::DEFAULT,
        )
        .base,
    );
}

#[test]
#[ignore]
fn run_load_store_subword_stage1_buffer_parity_test() {
    run_stage1_buffer_parity(
        &prepare_canonical_proof_fixture(
            CanonicalCircuit::MemSubwordOnly,
            circuit_common::SoundnessMode::DEFAULT,
        )
        .base,
    );
}

#[test]
#[ignore]
fn run_unified_stage1_buffer_parity_test() {
    run_stage1_buffer_parity(
        &prepare_canonical_proof_fixture(
            CanonicalCircuit::UnifiedReducedMachine,
            circuit_common::SoundnessMode::DEFAULT,
        )
        .base,
    );
}

#[test]
#[ignore]
fn run_blake2_compression_delegation_stage1_buffer_parity_test() {
    run_stage1_buffer_parity(
        &prepare_canonical_proof_fixture(
            CanonicalCircuit::Blake2WithExtendedControl,
            circuit_common::SoundnessMode::DEFAULT,
        )
        .base,
    );
}

#[test]
#[ignore]
fn run_keccak_chi5_stage1_buffer_parity_test() {
    run_stage1_buffer_parity(
        &prepare_canonical_proof_fixture(
            CanonicalCircuit::KeccakChi5,
            circuit_common::SoundnessMode::DEFAULT,
        )
        .base,
    );
}

#[test]
#[ignore]
fn run_keccak_column_parity_stage1_buffer_parity_test() {
    run_stage1_buffer_parity(
        &prepare_canonical_proof_fixture(
            CanonicalCircuit::KeccakColumnParity,
            circuit_common::SoundnessMode::DEFAULT,
        )
        .base,
    );
}

#[test]
#[ignore]
fn run_keccak_theta_rho_stage1_buffer_parity_test() {
    run_stage1_buffer_parity(
        &prepare_canonical_proof_fixture(
            CanonicalCircuit::KeccakThetaRho,
            circuit_common::SoundnessMode::DEFAULT,
        )
        .base,
    );
}
