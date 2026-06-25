use std::alloc::Global;

use prover::check_satisfied;
use prover::common_constants;
use prover::common_constants::BLAKE2S_DELEGATION_CSR_REGISTER;
use prover::cs::cs::circuit::Circuit as _;
use prover::cs::one_row_compiler::OneRowCompiler;
use prover::definitions::ExternalValues;
use prover::evaluate_delegation_memory_witness;
use prover::evaluate_witness;
use prover::fft::LdePrecomputations;
use prover::fft::Twiddles;
use prover::field::Field as _;
use prover::field::Mersenne31Field;
use prover::prover_stages::prove;
use prover::prover_stages::SetupPrecomputations;
use prover::tests::blake2s_delegation_with_transpiler;
use prover::tests::unrolled::parse_delegation_ram_accesses_from_full_trace;
use prover::tracers::oracles::transpiler_oracles::delegation::Blake2sDelegationOracle;
use prover::DEFAULT_TRACE_PADDING_MULTIPLE;
use riscv_transpiler::replayer::ReplayerRam;
use riscv_transpiler::replayer::ReplayerVM;
use riscv_transpiler::vm::DelegationsAndFamiliesCounters;
use riscv_transpiler::vm::ReplayBuffer as _;
use riscv_transpiler::vm::SimpleSnapshotter;
use riscv_transpiler::vm::SimpleTape;
use riscv_transpiler::vm::State;
use riscv_transpiler::witness::BlakeDelegationDestinationHolder;
use riscv_transpiler::witness::DelegationWitness;

use crate::rv32im::prover::accumulators::Accumulators;
use crate::rv32im::prover::sets::ReadSets;
use crate::rv32im::prover::sets::WriteSets;
use crate::rv32im::prover::Prover;
use crate::rv32im::prover::LDE_FACTOR;
use crate::rv32im::prover::NUM_DELEGATION_CYCLES;
use crate::rv32im::prover::TREE_CAP_SIZE;
use crate::rv32im::types::CountersT;

impl Prover {
    #[allow(clippy::too_many_arguments)]
    pub fn prove_blake_delegation(
        &self,
        accumulators: &mut Accumulators,
        counters: &DelegationsAndFamiliesCounters,
        snapshotter: &SimpleSnapshotter<CountersT, { common_constants::ROM_SECOND_WORD_BITS }>,
        read_sets: &mut ReadSets,
        write_sets: &mut WriteSets,
        tape: &SimpleTape,
        cycles_bound: usize,
        expected_final_state: State<CountersT>,
    ) {
        let mut external_values = ExternalValues {
            challenges: self.external_challenges,
            aux_boundary_values: Default::default(),
        };
        external_values.aux_boundary_values = Default::default();

        let (circuit, table_driver) = {
            use prover::cs::cs::cs_reference::BasicAssembly;
            use prover::cs::delegation::blake2_round_with_extended_control::define_blake2_with_extended_control_delegation_circuit;
            let mut cs = BasicAssembly::<Mersenne31Field>::new();
            define_blake2_with_extended_control_delegation_circuit(&mut cs);
            let (circuit_output, _) = cs.finalize();
            let table_driver = circuit_output.table_driver.clone();
            let compiler = OneRowCompiler::default();
            let circuit = compiler.compile_to_evaluate_delegations(
                circuit_output,
                (NUM_DELEGATION_CYCLES + 1).trailing_zeros() as usize,
            );

            (circuit, table_driver)
        };

        println!("Will try to prove Blake delegation");

        let num_calls = counters.blake_calls;
        dbg!(num_calls);

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram_log_buffers = snapshotter
            .reads_buffer
            .make_range(0..snapshotter.reads_buffer.len());

        let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
            ram_log: &mut ram_log_buffers,
        };

        let mut buffer = vec![DelegationWitness::empty(); num_calls];
        let mut buffers = [&mut buffer[..]];
        let mut tracer = BlakeDelegationDestinationHolder {
            buffers: &mut buffers[..],
        };

        ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
            &mut state,
            &mut ram,
            tape,
            &mut (),
            cycles_bound,
            &mut tracer,
        );
        assert_eq!(expected_final_state, state);

        // evaluate a witness and memory-only witness for each

        let delegation_type = BLAKE2S_DELEGATION_CSR_REGISTER as u16;
        let oracle = Blake2sDelegationOracle {
            cycle_data: &buffer,
            marker: core::marker::PhantomData,
        };
        let _mem_only_witness = evaluate_delegation_memory_witness(
            &circuit,
            NUM_DELEGATION_CYCLES,
            &oracle,
            self.worker(),
            Global,
        );

        let eval_fn = blake2s_delegation_with_transpiler::witness_eval_fn;

        let full_witness = evaluate_witness(
            &circuit,
            eval_fn,
            NUM_DELEGATION_CYCLES,
            &oracle,
            &[],
            &table_driver,
            0,
            self.worker(),
            Global,
        );

        parse_delegation_ram_accesses_from_full_trace(
            &circuit,
            &full_witness,
            write_sets.memory_write_set_mut(),
            read_sets.memory_read_set_mut(),
        );

        let is_satisfied = check_satisfied(
            &circuit,
            &full_witness.exec_trace,
            full_witness.num_witness_columns,
        );
        assert!(is_satisfied);

        let trace_len = NUM_DELEGATION_CYCLES + 1;

        // create setup
        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, self.worker());
        let lde_precomputations =
            LdePrecomputations::new(trace_len, LDE_FACTOR, &[0, 1], self.worker());

        let setup = SetupPrecomputations::from_tables_and_trace_len(
            &table_driver,
            NUM_DELEGATION_CYCLES + 1,
            &circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            LDE_FACTOR,
            TREE_CAP_SIZE,
            self.worker(),
        );

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove::<DEFAULT_TRACE_PADDING_MULTIPLE, _>(
            &circuit,
            &[],
            &external_values,
            full_witness,
            &setup,
            &twiddles,
            &lde_precomputations,
            0,
            Some(delegation_type),
            LDE_FACTOR,
            TREE_CAP_SIZE,
            self.default_security_config(),
            self.worker(),
        );
        println!(
            "Delegation circuit type {} proving time is {:?}",
            delegation_type,
            now.elapsed()
        );

        dbg!(prover_data.stage_2_result.grand_product_accumulator);
        dbg!(prover_data.stage_2_result.sum_over_delegation_poly);

        accumulators
            .permutation_argument_mut()
            .mul_assign(&proof.memory_grand_product_accumulator);
        accumulators
            .delegation_argument_mut()
            .sub_assign(&proof.delegation_argument_accumulator.unwrap());
    }
}
