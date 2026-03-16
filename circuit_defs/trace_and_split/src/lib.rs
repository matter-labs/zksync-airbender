#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use crate::cs::cs::oracle::ExecutorFamilyDecoderData;
use common_constants::INITIAL_PC;
use merkle_trees::MerkleTreeCapVarLength;
use prover::cs::definitions::TimestampScalar;
use prover::cs::utils::split_timestamp;
use prover::definitions::LazyInitAndTeardown;
use prover::tracers::oracles::transpiler_oracles::delegation::DelegationOracle;
use riscv_transpiler::machine_mode_only_unrolled::MemoryOpcodeTracingDataWithTimestamp;
use riscv_transpiler::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;
use riscv_transpiler::machine_mode_only_unrolled::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::DelegationAbiDescription;
use setups::prover::definitions::OPTIMAL_FOLDING_PROPERTIES;
use setups::prover::fft::*;
use setups::prover::field::*;
use setups::prover::merkle_trees::DefaultTreeConstructor;
use setups::prover::merkle_trees::MerkleTreeConstructor;
use setups::prover::transcript::Seed;
use setups::prover::*;
use worker::Worker;

pub const ENTRY_POINT: u32 = INITIAL_PC;

pub use prover;
pub use setups;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct FinalRegisterValue {
    pub value: u32,
    pub last_access_timestamp: TimestampScalar,
}

pub fn commit_memory_tree_for_unrolled_nonmem_circuits<A: GoodAllocator>(
    circuit: &setups::prover::cs::one_row_compiler::CompiledCircuitArtifact<Mersenne31Field>,
    witness_chunk: &[NonMemoryOpcodeTracingDataWithTimestamp],
    twiddles: &Twiddles<Mersenne31Complex, A>,
    lde_precomputations: &LdePrecomputations<A>,
    default_pc_value_in_padding: u32,
    decoder_data: &[ExecutorFamilyDecoderData],
    worker: &Worker,
) -> Vec<MerkleTreeCapVarLength> {
    use prover::unrolled::evaluate_memory_witness_for_executor_family;
    use prover::unrolled::NonMemoryCircuitOracle;
    let lde_factor = lde_precomputations.lde_factor;
    assert_eq!(twiddles.domain_size, lde_precomputations.domain_size);
    use setups::prover::prover_stages::stage1::compute_wide_ldes;
    let trace_len = twiddles.domain_size;

    let optimal_folding = OPTIMAL_FOLDING_PROPERTIES[trace_len.trailing_zeros() as usize];

    let num_cycles_in_chunk = trace_len - 1;
    assert!(witness_chunk.len() <= num_cycles_in_chunk);
    let now = std::time::Instant::now();

    let oracle = NonMemoryCircuitOracle {
        inner: witness_chunk,
        decoder_table: decoder_data,
        default_pc_value_in_padding,
    };

    let memory_trace = evaluate_memory_witness_for_executor_family::<_, A>(
        &circuit,
        num_cycles_in_chunk,
        &oracle,
        &worker,
        A::default(),
    );

    println!(
        "Materializing memory trace for {} cycles took {:?}",
        num_cycles_in_chunk,
        now.elapsed()
    );

    let MemoryOnlyWitnessEvaluationDataForExecutionFamily { memory_trace } = memory_trace;
    // now we should commit to it
    let width = memory_trace.width();
    let mut memory_trace = memory_trace;
    adjust_to_zero_c0_var_length(&mut memory_trace, 0..width, worker);

    let memory_ldes = compute_wide_ldes(
        memory_trace,
        twiddles,
        lde_precomputations,
        0,
        lde_factor,
        worker,
    );
    assert_eq!(memory_ldes.len(), lde_factor);

    // now form a tree
    let subtree_cap_size = (1 << optimal_folding.total_caps_size_log2) / lde_factor;
    assert!(subtree_cap_size > 0);

    let mut memory_subtrees = Vec::with_capacity(lde_factor);
    let now = std::time::Instant::now();
    for domain in memory_ldes.iter() {
        let memory_tree = DefaultTreeConstructor::construct_for_coset(
            &domain.trace,
            subtree_cap_size,
            true,
            worker,
        );
        memory_subtrees.push(memory_tree);
    }

    let dump_fn = |caps: &[DefaultTreeConstructor]| {
        let mut result = Vec::with_capacity(caps.len());
        for el in caps.iter() {
            result.push(el.get_cap());
        }

        result
    };

    let caps = dump_fn(&memory_subtrees);
    println!("Memory witness commitment took {:?}", now.elapsed());

    caps
}

pub fn commit_memory_tree_for_unrolled_mem_circuits<A: GoodAllocator>(
    circuit: &setups::prover::cs::one_row_compiler::CompiledCircuitArtifact<Mersenne31Field>,
    witness_chunk: &[MemoryOpcodeTracingDataWithTimestamp],
    twiddles: &Twiddles<Mersenne31Complex, A>,
    lde_precomputations: &LdePrecomputations<A>,
    decoder_data: &[ExecutorFamilyDecoderData],
    worker: &Worker,
) -> Vec<MerkleTreeCapVarLength> {
    use prover::unrolled::evaluate_memory_witness_for_executor_family;
    use prover::unrolled::MemoryCircuitOracle;
    let lde_factor = lde_precomputations.lde_factor;
    assert_eq!(twiddles.domain_size, lde_precomputations.domain_size);
    use setups::prover::prover_stages::stage1::compute_wide_ldes;
    let trace_len = twiddles.domain_size;

    let optimal_folding = OPTIMAL_FOLDING_PROPERTIES[trace_len.trailing_zeros() as usize];

    let num_cycles_in_chunk = trace_len - 1;
    assert!(witness_chunk.len() <= num_cycles_in_chunk);
    let now = std::time::Instant::now();

    let oracle = MemoryCircuitOracle {
        inner: witness_chunk,
        decoder_table: decoder_data,
    };

    let memory_trace = evaluate_memory_witness_for_executor_family::<_, A>(
        &circuit,
        num_cycles_in_chunk,
        &oracle,
        &worker,
        A::default(),
    );

    println!(
        "Materializing memory trace for {} cycles took {:?}",
        num_cycles_in_chunk,
        now.elapsed()
    );

    let MemoryOnlyWitnessEvaluationDataForExecutionFamily { memory_trace } = memory_trace;
    // now we should commit to it
    let width = memory_trace.width();
    let mut memory_trace = memory_trace;
    adjust_to_zero_c0_var_length(&mut memory_trace, 0..width, worker);

    let memory_ldes = compute_wide_ldes(
        memory_trace,
        twiddles,
        lde_precomputations,
        0,
        lde_factor,
        worker,
    );
    assert_eq!(memory_ldes.len(), lde_factor);

    // now form a tree
    let subtree_cap_size = (1 << optimal_folding.total_caps_size_log2) / lde_factor;
    assert!(subtree_cap_size > 0);

    let mut memory_subtrees = Vec::with_capacity(lde_factor);
    let now = std::time::Instant::now();
    for domain in memory_ldes.iter() {
        let memory_tree = DefaultTreeConstructor::construct_for_coset(
            &domain.trace,
            subtree_cap_size,
            true,
            worker,
        );
        memory_subtrees.push(memory_tree);
    }

    let dump_fn = |caps: &[DefaultTreeConstructor]| {
        let mut result = Vec::with_capacity(caps.len());
        for el in caps.iter() {
            result.push(el.get_cap());
        }

        result
    };

    let caps = dump_fn(&memory_subtrees);
    println!("Memory witness commitment took {:?}", now.elapsed());

    caps
}

pub fn commit_memory_tree_for_inits_and_teardowns_unrolled_circuit<A: GoodAllocator>(
    circuit: &setups::prover::cs::one_row_compiler::CompiledCircuitArtifact<Mersenne31Field>,
    lazy_init_data: &[LazyInitAndTeardown],
    twiddles: &Twiddles<Mersenne31Complex, A>,
    lde_precomputations: &LdePrecomputations<A>,
    worker: &Worker,
) -> (Vec<MerkleTreeCapVarLength>, WitnessEvaluationAuxData) {
    use prover::unrolled::evaluate_init_and_teardown_memory_witness;
    let lde_factor = lde_precomputations.lde_factor;
    assert_eq!(twiddles.domain_size, lde_precomputations.domain_size);
    use setups::prover::prover_stages::stage1::compute_wide_ldes;
    let trace_len = twiddles.domain_size;

    let optimal_folding = OPTIMAL_FOLDING_PROPERTIES[trace_len.trailing_zeros() as usize];

    let num_cycles_in_chunk = trace_len - 1;
    let max_to_init =
        circuit.memory_layout.shuffle_ram_inits_and_teardowns.len() * num_cycles_in_chunk;
    assert!(max_to_init > 0);
    assert!(lazy_init_data.len() <= max_to_init);
    let now = std::time::Instant::now();

    let memory_trace = evaluate_init_and_teardown_memory_witness::<A>(
        &circuit,
        num_cycles_in_chunk,
        lazy_init_data,
        &worker,
        A::default(),
    );

    println!(
        "Materializing memory trace for {} cycles took {:?}",
        num_cycles_in_chunk,
        now.elapsed()
    );

    let MemoryOnlyWitnessEvaluationData {
        aux_data,
        memory_trace,
    } = memory_trace;
    // now we should commit to it
    let width = memory_trace.width();
    let mut memory_trace = memory_trace;
    adjust_to_zero_c0_var_length(&mut memory_trace, 0..width, worker);

    let memory_ldes = compute_wide_ldes(
        memory_trace,
        twiddles,
        lde_precomputations,
        0,
        lde_factor,
        worker,
    );
    assert_eq!(memory_ldes.len(), lde_factor);

    // now form a tree
    let subtree_cap_size = (1 << optimal_folding.total_caps_size_log2) / lde_factor;
    assert!(subtree_cap_size > 0);

    let mut memory_subtrees = Vec::with_capacity(lde_factor);
    let now = std::time::Instant::now();
    for domain in memory_ldes.iter() {
        let memory_tree = DefaultTreeConstructor::construct_for_coset(
            &domain.trace,
            subtree_cap_size,
            true,
            worker,
        );
        memory_subtrees.push(memory_tree);
    }

    let dump_fn = |caps: &[DefaultTreeConstructor]| {
        let mut result = Vec::with_capacity(caps.len());
        for el in caps.iter() {
            result.push(el.get_cap());
        }

        result
    };

    let caps = dump_fn(&memory_subtrees);
    println!("Memory witness commitment took {:?}", now.elapsed());

    (caps, aux_data)
}

pub fn commit_memory_tree_for_unified_circuits<A: GoodAllocator>(
    circuit: &setups::prover::cs::one_row_compiler::CompiledCircuitArtifact<Mersenne31Field>,
    witness_chunk: &[UnifiedOpcodeTracingDataWithTimestamp],
    lazy_init_data: &[LazyInitAndTeardown],
    twiddles: &Twiddles<Mersenne31Complex, A>,
    lde_precomputations: &LdePrecomputations<A>,
    decoder_data: &[ExecutorFamilyDecoderData],
    worker: &Worker,
) -> Vec<MerkleTreeCapVarLength> {
    use prover::unrolled::evaluate_memory_witness_for_unified_executor;
    use prover::unrolled::UnifiedRiscvCircuitOracle;
    let lde_factor = lde_precomputations.lde_factor;
    assert_eq!(twiddles.domain_size, lde_precomputations.domain_size);
    use setups::prover::prover_stages::stage1::compute_wide_ldes;
    let trace_len = twiddles.domain_size;

    let optimal_folding = OPTIMAL_FOLDING_PROPERTIES[trace_len.trailing_zeros() as usize];

    let num_cycles_in_chunk = trace_len - 1;
    assert!(witness_chunk.len() <= num_cycles_in_chunk);
    let now = std::time::Instant::now();

    let oracle = UnifiedRiscvCircuitOracle {
        inner: witness_chunk,
        decoder_table: decoder_data,
    };

    let memory_trace = evaluate_memory_witness_for_unified_executor::<_, A>(
        &circuit,
        num_cycles_in_chunk,
        lazy_init_data,
        &oracle,
        &worker,
        A::default(),
    );

    println!(
        "Materializing memory trace for {} cycles took {:?}",
        num_cycles_in_chunk,
        now.elapsed()
    );

    let MemoryOnlyWitnessEvaluationDataForExecutionFamily { memory_trace } = memory_trace;
    // now we should commit to it
    let width = memory_trace.width();
    let mut memory_trace = memory_trace;
    adjust_to_zero_c0_var_length(&mut memory_trace, 0..width, worker);

    let memory_ldes = compute_wide_ldes(
        memory_trace,
        twiddles,
        lde_precomputations,
        0,
        lde_factor,
        worker,
    );
    assert_eq!(memory_ldes.len(), lde_factor);

    // now form a tree
    let subtree_cap_size = (1 << optimal_folding.total_caps_size_log2) / lde_factor;
    assert!(subtree_cap_size > 0);

    let mut memory_subtrees = Vec::with_capacity(lde_factor);
    let now = std::time::Instant::now();
    for domain in memory_ldes.iter() {
        let memory_tree = DefaultTreeConstructor::construct_for_coset(
            &domain.trace,
            subtree_cap_size,
            true,
            worker,
        );
        memory_subtrees.push(memory_tree);
    }

    let dump_fn = |caps: &[DefaultTreeConstructor]| {
        let mut result = Vec::with_capacity(caps.len());
        for el in caps.iter() {
            result.push(el.get_cap());
        }

        result
    };

    let caps = dump_fn(&memory_subtrees);
    println!("Memory witness commitment took {:?}", now.elapsed());

    caps
}

pub fn commit_memory_tree_for_delegation_circuit_with_replayer_format<
    A: GoodAllocator,
    D: DelegationAbiDescription,
    const REG_ACCESSES: usize,
    const INDIRECT_READS: usize,
    const INDIRECT_WRITES: usize,
    const VARIABLE_OFFSETS: usize,
>(
    compiled_machine: &setups::prover::cs::one_row_compiler::CompiledCircuitArtifact<
        Mersenne31Field,
    >,
    witness_chunk: &[riscv_transpiler::witness::DelegationWitness<
        REG_ACCESSES,
        INDIRECT_READS,
        INDIRECT_WRITES,
        VARIABLE_OFFSETS,
    >],
    num_cycles_in_circuit: usize,
    twiddles: &Twiddles<Mersenne31Complex, A>,
    lde_precomputations: &LdePrecomputations<A>,
    lde_factor: usize,
    _tree_cap_size: usize,
    worker: &Worker,
) -> Vec<MerkleTreeCapVarLength> {
    use setups::prover::prover_stages::stage1::compute_wide_ldes;
    assert!((num_cycles_in_circuit + 1).is_power_of_two());
    let trace_len = num_cycles_in_circuit + 1;

    assert!(trace_len.is_power_of_two());
    let optimal_folding = OPTIMAL_FOLDING_PROPERTIES[trace_len.trailing_zeros() as usize];

    let now = std::time::Instant::now();
    let oracle = DelegationOracle::<D, _, _, _, _> {
        cycle_data: witness_chunk,
        marker: core::marker::PhantomData,
    };
    let memory_chunk = evaluate_delegation_memory_witness(
        compiled_machine,
        num_cycles_in_circuit,
        &oracle,
        &worker,
        A::default(),
    );
    println!(
        "Materializing memory for delegation type {} trace for {} cycles took {:?}",
        D::DELEGATION_TYPE,
        num_cycles_in_circuit,
        now.elapsed()
    );

    let DelegationMemoryOnlyWitnessEvaluationData { memory_trace } = memory_chunk;
    // now we should commit to it
    let width = memory_trace.width();
    let mut memory_trace = memory_trace;
    adjust_to_zero_c0_var_length(&mut memory_trace, 0..width, worker);

    let memory_ldes = compute_wide_ldes(
        memory_trace,
        twiddles,
        lde_precomputations,
        0,
        lde_factor,
        worker,
    );
    assert_eq!(memory_ldes.len(), lde_factor);

    // now form a tree
    let subtree_cap_size = (1 << optimal_folding.total_caps_size_log2) / lde_factor;
    assert!(subtree_cap_size > 0);

    let mut memory_subtrees = Vec::with_capacity(lde_factor);
    let now = std::time::Instant::now();
    for domain in memory_ldes.iter() {
        let memory_tree = DefaultTreeConstructor::construct_for_coset(
            &domain.trace,
            subtree_cap_size,
            true,
            worker,
        );
        memory_subtrees.push(memory_tree);
    }

    let dump_fn = |caps: &[DefaultTreeConstructor]| {
        let mut result = Vec::with_capacity(caps.len());
        for el in caps.iter() {
            result.push(el.get_cap());
        }

        result
    };

    let caps = dump_fn(&memory_subtrees);
    println!("Memory witness commitment took {:?}", now.elapsed());

    caps
}

fn flatten_merkle_caps(trees: &[MerkleTreeCapVarLength]) -> Vec<u32> {
    let mut result = vec![];
    for subtree in trees.iter() {
        for cap_element in subtree.cap.iter() {
            result.extend_from_slice(cap_element);
        }
    }

    result
}

/// We need to draw a common challenge based on all the values that will contribute to the memory permutation grand product, and
/// delegation argument set equality
pub fn fs_transform_for_memory_and_delegation_arguments_for_unrolled_circuits(
    final_register_values: &[FinalRegisterValue],
    final_pc: u32,
    final_timestamp: TimestampScalar,
    circuit_families_memory_caps: &[(u32, Vec<Vec<MerkleTreeCapVarLength>>)],
    inits_and_teardowns_memory_caps: &[Vec<MerkleTreeCapVarLength>],
    delegation_circuits_memory_caps: &[(u32, Vec<Vec<MerkleTreeCapVarLength>>)],
) -> Seed {
    use transcript::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS;

    let mut memory_trace_transcript = transcript::Blake2sBufferingTranscript::new();

    // commit all registers
    let mut register_values_and_timestamps = Vec::with_capacity(32 + 32 * 2);
    for register in final_register_values.iter() {
        register_values_and_timestamps.push(register.value);
        let (low, high) = split_timestamp(register.last_access_timestamp);
        register_values_and_timestamps.push(low);
        register_values_and_timestamps.push(high);
    }

    memory_trace_transcript.absorb(&register_values_and_timestamps);

    // then final PC
    let (ts_low, ts_high) = split_timestamp(final_timestamp);
    let mut final_pc_buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
    final_pc_buffer[0] = final_pc;
    final_pc_buffer[1] = ts_low;
    final_pc_buffer[2] = ts_high;

    memory_trace_transcript.absorb(&final_pc_buffer);

    // then we commit all main RISC-V circuits
    assert!(circuit_families_memory_caps.is_sorted_by(|a, b| a.0 < b.0));
    for (family, caps) in circuit_families_memory_caps.iter() {
        if caps.len() > 0 {
            let mut buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
            buffer[0] = *family;
            memory_trace_transcript.absorb(&buffer);
        }
        for caps in caps.iter() {
            let caps = flatten_merkle_caps(&caps);
            memory_trace_transcript.absorb(&caps);
        }
    }

    // inits and teardowns
    {
        if inits_and_teardowns_memory_caps.len() > 0 {
            let mut buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
            buffer[0] =
                common_constants::circuit_families::INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX
                    as u32;
            memory_trace_transcript.absorb(&buffer);
        }
        for caps in inits_and_teardowns_memory_caps.iter() {
            let caps = flatten_merkle_caps(&caps);
            memory_trace_transcript.absorb(&caps);
        }
    }

    assert_eq!(
        memory_trace_transcript.get_current_buffer_offset(),
        BLAKE2S_BLOCK_SIZE_U32_WORDS
    );

    // then for delegation circuits: delegation type contributes to the delegation argument's expressions, and as we have a variable number of them
    // we will always commit a tuple of delegation type + caps. This way the order is not too important, but we adhere to convention that
    // those should be batched and sorted

    assert!(delegation_circuits_memory_caps.is_sorted_by(|a, b| a.0 < b.0));
    for (delegation_type, caps) in delegation_circuits_memory_caps.iter() {
        if caps.len() > 0 {
            let mut buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
            buffer[0] = *delegation_type;
            memory_trace_transcript.absorb(&buffer);
        }
        for caps in caps.iter() {
            let caps = flatten_merkle_caps(&caps);
            memory_trace_transcript.absorb(&caps);
        }

        assert_eq!(
            memory_trace_transcript.get_current_buffer_offset(),
            BLAKE2S_BLOCK_SIZE_U32_WORDS
        );
    }

    let memory_challenges_seed = memory_trace_transcript.finalize();

    memory_challenges_seed
}
