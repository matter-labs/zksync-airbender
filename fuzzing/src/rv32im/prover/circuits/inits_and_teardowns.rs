use std::alloc::Global;

use prover::check_satisfied;
use prover::cs::one_row_compiler::OneRowCompiler;
use prover::cs::tables::TableDriver;
use prover::fft::LdePrecomputations;
use prover::fft::Twiddles;
use prover::field::Field as _;
use prover::field::Mersenne31Field;
use prover::merkle_trees::DefaultTreeConstructor;
use prover::prover_stages::SetupPrecomputations;
use prover::unrolled::evaluate_init_and_teardown_memory_witness;
use prover::unrolled::evaluate_init_and_teardown_witness;
use prover::ExecutorFamilyWitnessEvaluationAuxData;
use prover::ShuffleRamSetupAndTeardown;
use prover::WitnessEvaluationData;
use prover::WitnessEvaluationDataForExecutionFamily;

use crate::rv32im::prover::accumulators::Accumulators;
use crate::rv32im::prover::Prover;
use crate::rv32im::prover::LDE_FACTOR;
use crate::rv32im::prover::NUM_CYCLES_PER_CHUNK;
use crate::rv32im::prover::NUM_INIT_AND_TEARDOWN_SETS;
use crate::rv32im::prover::TRACE_LEN;
use crate::rv32im::prover::TRACE_LEN_LOG2;
use crate::rv32im::prover::TREE_CAP_SIZE;

impl Prover {
    pub fn prove_init_and_teardowns(
        &self,
        accumulators: &mut Accumulators,
        inits_and_teardowns: &[ShuffleRamSetupAndTeardown],
    ) {
        println!("Will try to prove memory inits and teardowns circuit");

        let compiler = OneRowCompiler::<Mersenne31Field>::default();
        let inits_and_teardowns_circuit =
            compiler.compile_init_and_teardown_circuit(NUM_INIT_AND_TEARDOWN_SETS, TRACE_LEN_LOG2);

        let table_driver = TableDriver::<Mersenne31Field>::new();

        let inits_data = &inits_and_teardowns[0];

        let _memory_trace = evaluate_init_and_teardown_memory_witness::<Global>(
            &inits_and_teardowns_circuit,
            NUM_CYCLES_PER_CHUNK,
            &inits_data.lazy_init_data,
            self.worker(),
            Global,
        );

        let full_trace = evaluate_init_and_teardown_witness::<Global>(
            &inits_and_teardowns_circuit,
            NUM_CYCLES_PER_CHUNK,
            &inits_data.lazy_init_data,
            self.worker(),
            Global,
        );

        let WitnessEvaluationData {
            aux_data,
            exec_trace,
            num_witness_columns,
            lookup_mapping,
        } = full_trace;
        let full_trace = WitnessEvaluationDataForExecutionFamily {
            aux_data: ExecutorFamilyWitnessEvaluationAuxData {},
            exec_trace,
            num_witness_columns,
            lookup_mapping,
        };

        let is_satisfied = check_satisfied(
            &inits_and_teardowns_circuit,
            &full_trace.exec_trace,
            full_trace.num_witness_columns,
        );
        assert!(is_satisfied);

        let twiddles: Twiddles<_, Global> = Twiddles::new(TRACE_LEN, self.worker());
        let lde_precomputations =
            LdePrecomputations::new(TRACE_LEN, LDE_FACTOR, &[0, 1], self.worker());
        let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &[],
            TRACE_LEN,
            &inits_and_teardowns_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            LDE_FACTOR,
            TREE_CAP_SIZE,
            self.worker(),
        );

        let (_, proof) = self.run_prover_with_auxdata::<_, DefaultTreeConstructor, _>(
            &inits_and_teardowns_circuit,
            full_trace,
            &setup,
            &twiddles,
            &lde_precomputations,
            &aux_data.aux_boundary_data,
        );

        accumulators
            .permutation_argument_mut()
            .mul_assign(&proof.permutation_grand_product_accumulator);
    }
}
