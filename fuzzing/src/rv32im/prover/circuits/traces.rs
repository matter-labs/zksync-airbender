use std::alloc::Allocator;
use std::alloc::Global;

use prover::check_satisfied;
use prover::cs::cs::oracle::Oracle;
use prover::cs::one_row_compiler::CompiledCircuitArtifact;
use prover::cs::tables::TableDriver;
use prover::field::Mersenne31Field;
use prover::tests::unrolled::ensure_memory_trace_consistency;
use prover::tests::unrolled::parse_shuffle_ram_accesses_from_full_trace;
use prover::tests::unrolled::parse_state_permutation_elements_from_full_trace;
use prover::unrolled::evaluate_memory_witness_for_executor_family;
use prover::unrolled::evaluate_witness_for_executor_family;
use prover::worker::Worker;
use prover::MemoryOnlyWitnessEvaluationDataForExecutionFamily;
use prover::SimpleWitnessProxy;
use prover::WitnessEvaluationDataForExecutionFamily;
use prover::DEFAULT_TRACE_PADDING_MULTIPLE;

use crate::rv32im::prover::sets::ReadSets;
use crate::rv32im::prover::sets::WriteSets;
pub trait TracesFactory<I> {
    type FullTrace;
    type MemoryTrace;

    fn new(
        circuit: &CompiledCircuitArtifact<Mersenne31Field>,
        init: I,
        table_driver: &TableDriver<Mersenne31Field>,
        worker: &Worker,
    ) -> Self;

    fn take_full_trace(self) -> Self::FullTrace;
}

type FullTrace<A, const N: usize> = WitnessEvaluationDataForExecutionFamily<N, A>;

pub struct FullAndMemTraces<A, const N: usize>
where
    A: Allocator + Clone,
{
    full_trace: FullTrace<A, N>,
    _memory_trace: MemoryOnlyWitnessEvaluationDataForExecutionFamily<N, A>,
}

impl<O: Oracle<Mersenne31Field>>
    TracesFactory<(
        &O,
        fn(&mut SimpleWitnessProxy<'_, O>),
        usize,
        &mut ReadSets,
        &mut WriteSets,
    )> for FullAndMemTraces<Global, DEFAULT_TRACE_PADDING_MULTIPLE>
{
    type FullTrace = FullTrace<Global, DEFAULT_TRACE_PADDING_MULTIPLE>;

    type MemoryTrace =
        MemoryOnlyWitnessEvaluationDataForExecutionFamily<DEFAULT_TRACE_PADDING_MULTIPLE, Global>;

    fn new(
        circuit: &CompiledCircuitArtifact<Mersenne31Field>,
        (oracle, witness_eval, num_cycles_per_chunk, read_sets, write_sets): (
            &O,
            fn(&mut SimpleWitnessProxy<'_, O>),
            usize,
            &mut ReadSets,
            &mut WriteSets,
        ),
        table_driver: &TableDriver<Mersenne31Field>,
        worker: &Worker,
    ) -> Self {
        let memory_trace = evaluate_memory_witness_for_executor_family::<_, Global>(
            circuit,
            num_cycles_per_chunk,
            oracle,
            worker,
            Global,
        );

        let full_trace = evaluate_witness_for_executor_family::<_, Global>(
            circuit,
            witness_eval,
            num_cycles_per_chunk,
            oracle,
            table_driver,
            worker,
            Global,
        );

        ensure_memory_trace_consistency(&memory_trace, &full_trace);

        parse_state_permutation_elements_from_full_trace(
            circuit,
            &full_trace,
            write_sets.write_set_mut(),
            read_sets.read_set_mut(),
        );
        parse_shuffle_ram_accesses_from_full_trace(
            circuit,
            &full_trace,
            write_sets.memory_write_set_mut(),
            read_sets.memory_read_set_mut(),
        );

        let is_satisfied = check_satisfied(
            circuit,
            &full_trace.exec_trace,
            full_trace.num_witness_columns,
        );
        assert!(is_satisfied);

        Self {
            full_trace,
            _memory_trace: memory_trace,
        }
    }

    fn take_full_trace(self) -> Self::FullTrace {
        self.full_trace
    }
}
