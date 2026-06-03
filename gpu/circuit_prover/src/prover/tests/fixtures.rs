use super::*;

pub(super) type DelegationSnapshotter =
    SimpleSnapshotter<DelegationsAndFamiliesCounters, { ROM_SECOND_WORD_BITS }>;
pub(super) type DelegationState = State<DelegationsAndFamiliesCounters>;

pub(super) struct DelegationReplayFixture {
    pub(super) instructions: Vec<Instruction>,
    pub(super) snapshotter: DelegationSnapshotter,
    pub(super) cycles_bound: usize,
    pub(super) expected_final_state: DelegationState,
}

pub(super) fn build_delegation_replay_fixture(
    non_determinism_reads: &[u32],
) -> DelegationReplayFixture {
    let binary = read_test_words("riscv_transpiler/examples/keccak_f1600/app.bin");
    let text_section = read_test_words("riscv_transpiler/examples/keccak_f1600/app.text");
    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(&binary, 1 << 30);
    let cycles_bound = 1 << 20;

    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
    let mut snapshotter = SimpleSnapshotter::<
        DelegationsAndFamiliesCounters,
        { ROM_SECOND_WORD_BITS },
    >::new_with_cycle_limit(cycles_bound, state);
    let mut non_determinism = QuasiUARTSource::new_with_reads(non_determinism_reads.to_vec());
    let is_finished = VM::<DelegationsAndFamiliesCounters>::run_basic_unrolled::<_, _, _, BF>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut non_determinism,
    );
    assert!(is_finished);

    let mut expected_final_state = state;
    expected_final_state.counters = Default::default();

    DelegationReplayFixture {
        instructions,
        snapshotter,
        cycles_bound,
        expected_final_state,
    }
}

pub(super) fn replay_delegation_trace_buffer<W: Clone>(
    zero_call: bool,
    count_from_counters: impl FnOnce(&DelegationsAndFamiliesCounters) -> usize,
    empty_witness: W,
    replay: fn(
        &SimpleTape,
        usize,
        &mut DelegationState,
        &mut ReplayerRam<{ ROM_SECOND_WORD_BITS }>,
        &mut [W],
    ),
) -> Vec<W> {
    if zero_call {
        return Vec::new();
    }

    let fixture = build_delegation_replay_fixture(&[15, 1]);
    let num_calls =
        count_from_counters(&fixture.snapshotter.snapshots.last().unwrap().state.counters);
    let mut replay_state = fixture.snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = fixture
        .snapshotter
        .reads_buffer
        .make_range(0..fixture.snapshotter.reads_buffer.len());
    let mut replay_ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let tape = SimpleTape::new(&fixture.instructions);
    let mut buffer = vec![empty_witness; num_calls];
    replay(
        &tape,
        fixture.cycles_bound,
        &mut replay_state,
        &mut replay_ram,
        &mut buffer,
    );
    assert_eq!(fixture.expected_final_state, replay_state);
    buffer
}

pub(super) fn delegation_prover_config(circuit_type: DelegationCircuitType) -> ProverConfig {
    crate::prover::config::prover_config(
        CircuitType::Delegation(circuit_type),
        SecurityLevel::Sec80,
    )
    .unwrap()
}

pub(super) fn test_external_challenges() -> GKRExternalChallenges<BF, E4> {
    let memory_argument_alpha =
        E4::from_array_of_base([BF::new(2), BF::new(5), BF::new(42), BF::new(123)]);
    let permutation_argument_additive_part =
        E4::from_array_of_base([BF::new(7), BF::new(11), BF::new(1024), BF::new(8000)]);
    let permutation_argument_linearization_challenges: [E4; NUM_PERMUTATION_ARGUMENT_KEY_PARTS
        - 1] = materialize_powers_serial_starting_with_elem::<_, Global>(
        memory_argument_alpha,
        NUM_PERMUTATION_ARGUMENT_KEY_PARTS - 1,
    )
    .try_into()
    .unwrap();

    GKRExternalChallenges {
        permutation_argument_linearization_challenges,
        permutation_argument_additive_part,
        _marker: std::marker::PhantomData,
    }
}

#[allow(unused_imports)]
pub(super) mod add_sub_lui_auipc_mod {
    use crate::primitives::field::BF;
    use cs::oracle::Placeholder;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
    use cs::witness_placer::WitnessTypeSet;
    use cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use field::baby_bear::base::BabyBearField;
    use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use prover::gkr::witness_gen::oracles::NonMemoryCircuitOracle;
    use prover::gkr::witness_gen::witness_proxy::WitnessProxy;

    include!("../../../../../prover/compiled_circuits/add_sub_lui_auipc_mop_generated_gkr.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BF>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BF, true>,
            ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BF>,
        >;
        fn_ptr(proxy);
    }
}

#[allow(unused_imports)]
pub(super) mod jump_branch_slt_mod {
    use crate::primitives::field::BF;
    use cs::oracle::Placeholder;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
    use cs::witness_placer::WitnessTypeSet;
    use cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use field::baby_bear::base::BabyBearField;
    use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use prover::gkr::witness_gen::oracles::NonMemoryCircuitOracle;
    use prover::gkr::witness_gen::witness_proxy::WitnessProxy;

    include!("../../../../../prover/compiled_circuits/jump_branch_slt_generated_gkr.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BF>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BF, true>,
            ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BF>,
        >;
        fn_ptr(proxy);
    }
}

#[allow(unused_imports)]
pub(super) mod shift_binop_mod {
    use crate::primitives::field::BF;
    use cs::oracle::Placeholder;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
    use cs::witness_placer::WitnessTypeSet;
    use cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use field::baby_bear::base::BabyBearField;
    use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use prover::gkr::witness_gen::oracles::NonMemoryCircuitOracle;
    use prover::gkr::witness_gen::witness_proxy::WitnessProxy;

    include!("../../../../../prover/compiled_circuits/shift_binop_generated_gkr.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BF>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BF, true>,
            ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BF>,
        >;
        fn_ptr(proxy);
    }
}

#[allow(unused_imports)]
pub(super) mod mem_word_only_mod {
    use crate::primitives::field::BF;
    use cs::oracle::Placeholder;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
    use cs::witness_placer::WitnessTypeSet;
    use cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use field::baby_bear::base::BabyBearField;
    use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use prover::gkr::witness_gen::oracles::MemoryCircuitOracle;
    use prover::gkr::witness_gen::witness_proxy::WitnessProxy;

    include!("../../../../../prover/compiled_circuits/mem_word_only_generated_gkr.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, MemoryCircuitOracle<'b>, BF>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BF, true>,
            ColumnMajorWitnessProxy<'a, MemoryCircuitOracle<'b>, BF>,
        >;
        fn_ptr(proxy);
    }
}

#[allow(unused_imports)]
pub(super) mod mem_subword_only_mod {
    use crate::primitives::field::BF;
    use cs::oracle::Placeholder;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
    use cs::witness_placer::WitnessTypeSet;
    use cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use field::baby_bear::base::BabyBearField;
    use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use prover::gkr::witness_gen::oracles::MemoryCircuitOracle;
    use prover::gkr::witness_gen::witness_proxy::WitnessProxy;

    include!("../../../../../prover/compiled_circuits/mem_subword_only_generated_gkr.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, MemoryCircuitOracle<'b>, BF>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BF, true>,
            ColumnMajorWitnessProxy<'a, MemoryCircuitOracle<'b>, BF>,
        >;
        fn_ptr(proxy);
    }
}

#[allow(unused_imports)]
pub(super) mod blake2_with_extended_control_mod {
    use crate::primitives::field::BF;
    use cs::oracle::Placeholder;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
    use cs::witness_placer::WitnessTypeSet;
    use cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use field::baby_bear::base::BabyBearField;
    use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use prover::gkr::witness_gen::witness_proxy::WitnessProxy;
    use prover::tracers::oracles::transpiler_oracles::delegation::Blake2sDelegationOracle;

    include!(
        "../../../../../prover/compiled_circuits/blake2_with_extended_control_generated_gkr.rs"
    );

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, Blake2sDelegationOracle<'b>, BF>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BF, true>,
            ColumnMajorWitnessProxy<'a, Blake2sDelegationOracle<'b>, BF>,
        >;
        fn_ptr(proxy);
    }
}

#[allow(unused_imports)]
pub(super) mod bigint_with_extended_control_mod {
    use crate::primitives::field::BF;
    use cs::oracle::Placeholder;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
    use cs::witness_placer::WitnessTypeSet;
    use cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use field::baby_bear::base::BabyBearField;
    use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use prover::gkr::witness_gen::witness_proxy::WitnessProxy;
    use prover::tracers::oracles::transpiler_oracles::delegation::BigintDelegationOracle;

    include!(
        "../../../../../prover/compiled_circuits/bigint_with_extended_control_generated_gkr.rs"
    );

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, BigintDelegationOracle<'b>, BF>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BF, true>,
            ColumnMajorWitnessProxy<'a, BigintDelegationOracle<'b>, BF>,
        >;
        fn_ptr(proxy);
    }
}

#[allow(unused_imports)]
pub(super) mod keccak_special5_mod {
    use crate::primitives::field::BF;
    use cs::oracle::Placeholder;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
    use cs::witness_placer::WitnessTypeSet;
    use cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use field::baby_bear::base::BabyBearField;
    use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use prover::gkr::witness_gen::witness_proxy::WitnessProxy;
    use prover::tracers::oracles::transpiler_oracles::delegation::KeccakDelegationOracle;

    include!("../../../../../prover/compiled_circuits/keccak_special5_generated_gkr.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, KeccakDelegationOracle<'b>, BF>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BF, true>,
            ColumnMajorWitnessProxy<'a, KeccakDelegationOracle<'b>, BF>,
        >;
        fn_ptr(proxy);
    }
}
