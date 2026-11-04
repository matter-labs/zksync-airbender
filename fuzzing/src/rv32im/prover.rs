use prover::common_constants::{self};
use prover::cs::definitions::EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH;
use prover::cs::one_row_compiler::CompiledCircuitArtifact;
use prover::cs::tables::TableDriver;
use prover::definitions::AuxArgumentsBoundaryValues;
use prover::definitions::ExternalChallenges;
use prover::fft::GoodAllocator;
use prover::fft::LdePrecomputations;
use prover::fft::Twiddles;
use prover::field::Mersenne31Complex;
use prover::field::Mersenne31Field;
use prover::merkle_trees::MerkleTreeConstructor;
use prover::prover_stages;
use prover::prover_stages::unrolled_prover::prove_configured_for_unrolled_circuits;
use prover::prover_stages::unrolled_prover::UnrolledModeProof;
use prover::prover_stages::ProverData;
use prover::prover_stages::SetupPrecomputations;
use prover::worker::Worker;
use prover::ShuffleRamSetupAndTeardown;
use prover::WitnessEvaluationDataForExecutionFamily;
use riscv_transpiler::vm::State;
use std::alloc::Allocator;
use std::alloc::Global;

use crate::rv32im::prover::checks::validate_inits_and_teardowns;
use crate::rv32im::prover::checks::validate_sets;
use crate::rv32im::types::CountersT;
use crate::rv32im::vm::VMSnapshot;
use crate::utils::env_conf;

mod accumulators;
mod checks;
pub(crate) mod circuits;
mod factories;
pub(crate) mod sets;

use accumulators::Accumulators;
use checks::validate_counters;
use factories::make_external_challenges;
use factories::make_preprocessing_data;
use sets::ReadSets;
use sets::WriteSets;

const TRACE_LEN_LOG2: usize = 24;
const NUM_CYCLES_PER_CHUNK: usize = (1 << TRACE_LEN_LOG2) - 1;
pub(crate) const MUL_DIV_TRACE_LEN_LOG2: usize = 23;

const SUPPORT_SIGNED: bool = false;
const INITIAL_PC: u32 = 0;
const NUM_INIT_AND_TEARDOWN_SETS: usize = 6;
const NUM_DELEGATION_CYCLES: usize = (1 << 20) - 1;

const LDE_FACTOR: usize = 2;
const TREE_CAP_SIZE: usize = 32;
const TRACE_LEN: usize = 1 << TRACE_LEN_LOG2;
pub const DEFAULT_WORKERS: usize = 1;

#[derive(Clone)]
pub(crate) struct PreparedExecution {
    pub counters: CountersT,
    pub total_unique_teardowns: usize,
    pub inits_and_teardowns: Vec<ShuffleRamSetupAndTeardown>,
    pub flattened_inits_and_teardowns: Vec<(u32, (common_constants::TimestampScalar, u32))>,
    pub expected_final_state: State<CountersT>,
    pub preprocessing_data: factories::PreprocessingData,
}

struct ProvingPayload<'c, 'a, A, T, const N: usize>
where
    A: Allocator + Clone + GoodAllocator,
    T: MerkleTreeConstructor,
{
    compiled_circuit: &'c CompiledCircuitArtifact<Mersenne31Field>,
    full_trace: WitnessEvaluationDataForExecutionFamily<N, A>,
    setup: SetupPrecomputations<N, A, T>,
    twiddles: Twiddles<Mersenne31Complex, A>,
    lde_precomputations: LdePrecomputations<A>,
    aux_boundary_data: &'a [AuxArgumentsBoundaryValues],
}

impl<'c, 'a, A, T, const N: usize> ProvingPayload<'c, 'a, A, T, N>
where
    A: Allocator + Clone + GoodAllocator,
    T: MerkleTreeConstructor,
{
    pub fn new(
        compiled_circuit: &'c CompiledCircuitArtifact<Mersenne31Field>,
        full_trace: WitnessEvaluationDataForExecutionFamily<N, A>,
        table_driver: &TableDriver<Mersenne31Field>,
        decoder_table_data: &[[Mersenne31Field; EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH]],
        aux_boundary_data: &'a [AuxArgumentsBoundaryValues],
        trace_len: usize,
        worker: &Worker,
    ) -> Self {
        let twiddles: Twiddles<_, A> = Twiddles::new(trace_len, worker);
        let lde_precomputations = LdePrecomputations::new(trace_len, LDE_FACTOR, &[0, 1], worker);
        let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            table_driver,
            decoder_table_data,
            trace_len,
            &compiled_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            LDE_FACTOR,
            TREE_CAP_SIZE,
            worker,
        );
        Self {
            compiled_circuit,
            full_trace,
            setup,
            twiddles,
            lde_precomputations,
            aux_boundary_data,
        }
    }
}

pub(crate) struct Prover {
    worker: Worker,
    default_security_config: prover_stages::ProofSecurityConfig,
    external_challenges: ExternalChallenges,
}

impl Prover {
    pub fn new() -> Self {
        let default_security_config =
            prover_stages::ProofSecurityConfig::for_queries_only(5, 28, 63);

        let worker = Worker::new_with_num_threads(env_conf("PROVER_WORKERS", DEFAULT_WORKERS));
        Self {
            default_security_config,
            worker,
            external_challenges: make_external_challenges(),
        }
    }

    fn external_challenges(&self) -> &ExternalChallenges {
        &self.external_challenges
    }

    pub fn worker(&self) -> &Worker {
        &self.worker
    }

    fn default_security_config(&self) -> &prover_stages::ProofSecurityConfig {
        &self.default_security_config
    }

    fn run_prover2<A, T, const N: usize>(
        &self,
        payload: ProvingPayload<'_, '_, A, T, N>,
    ) -> (ProverData<N, A, T>, UnrolledModeProof)
    where
        T: MerkleTreeConstructor,
        A: GoodAllocator + Clone,
    {
        self.run_prover_with_auxdata(
            payload.compiled_circuit,
            payload.full_trace,
            &payload.setup,
            &payload.twiddles,
            &payload.lde_precomputations,
            payload.aux_boundary_data,
        )
    }

    fn run_prover_with_auxdata<A, T, const N: usize>(
        &self,
        compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
        full_trace: WitnessEvaluationDataForExecutionFamily<N, A>,
        setup: &SetupPrecomputations<N, A, T>,
        twiddles: &Twiddles<Mersenne31Complex, A>,
        lde_precomputations: &LdePrecomputations<A>,
        aux_boundary_data: &[AuxArgumentsBoundaryValues],
    ) -> (ProverData<N, A, T>, UnrolledModeProof)
    where
        T: MerkleTreeConstructor,
        A: GoodAllocator + Clone,
    {
        #[cfg(feature = "prover-messages")]
        println!("Trying to prove");

        let now = std::time::Instant::now();
        let _ = &now;
        let proof = prove_configured_for_unrolled_circuits::<N, A, T>(
            compiled_circuit,
            &[],
            self.external_challenges(),
            full_trace,
            aux_boundary_data,
            setup,
            twiddles,
            lde_precomputations,
            None,
            LDE_FACTOR,
            TREE_CAP_SIZE,
            self.default_security_config(),
            self.worker(),
        );
        #[cfg(feature = "prover-messages")]
        println!("Proving time is {:?}", now.elapsed());
        proof
    }
}

pub(crate) fn prepare_execution(snapshot: VMSnapshot, worker: &Worker) -> PreparedExecution {
    #[cfg(feature = "prover-messages")]
    {
        use crate::rv32im::prover::common_constants::INITIAL_TIMESTAMP;
        use crate::rv32im::prover::common_constants::TIMESTAMP_STEP;
        let exact_cycles_passed = (snapshot.state().timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;

        println!("Passed exactly {} cycles", exact_cycles_passed);
    }
    let counters = snapshot
        .snapshotter()
        .snapshots
        .last()
        .unwrap()
        .state
        .counters;

    let shuffle_ram_touched_addresses = snapshot.ram().collect_inits_and_teardowns(worker, Global);

    use prover::tracers::oracles::chunk_lazy_init_and_teardown;
    let total_unique_teardowns: usize = shuffle_ram_touched_addresses
        .iter()
        .map(|el| el.len())
        .sum();

    #[cfg(feature = "prover-messages")]
    println!("Touched {} unique addresses", total_unique_teardowns);

    let (num_trivial, inits_and_teardowns) = chunk_lazy_init_and_teardown::<Global, _>(
        1,
        NUM_CYCLES_PER_CHUNK * NUM_INIT_AND_TEARDOWN_SETS,
        &shuffle_ram_touched_addresses,
        worker,
    );
    assert_eq!(num_trivial, 0, "trivial padding is not expected in tests");

    let flattened_inits_and_teardowns: Vec<_> = shuffle_ram_touched_addresses
        .into_iter()
        .flatten()
        .collect();

    #[cfg(feature = "prover-messages")]
    {
        println!("Finished at PC = 0x{:08x}", snapshot.state().pc);
        for (reg_idx, reg) in snapshot.state().registers.iter().enumerate() {
            println!("x{} = {}", reg_idx, reg.value);
        }
    }

    let mut expected_final_state = snapshot.state();
    expected_final_state.counters = Default::default();

    let preprocessing_data = make_preprocessing_data(snapshot.text());

    validate_counters(&counters);

    PreparedExecution {
        counters,
        total_unique_teardowns,
        inits_and_teardowns,
        flattened_inits_and_teardowns,
        expected_final_state,
        preprocessing_data,
    }
}

pub fn prove_vm_result(snapshot: VMSnapshot) {
    let prover = Prover::new();
    let prepared = prepare_execution(snapshot, prover.worker());
    let external_challenges = make_external_challenges();
    let mut accumulators = Accumulators::new(snapshot.state(), &external_challenges);
    let mut read_sets = ReadSets::new(snapshot.state());
    let mut write_sets = WriteSets::new();

    prover.prove_add_sub_lui_auipc_mop(
        &mut accumulators,
        snapshot,
        &prepared,
        &mut read_sets,
        &mut write_sets,
    );

    prover.prove_jump_branch_slt(
        &mut accumulators,
        snapshot,
        &prepared,
        &mut read_sets,
        &mut write_sets,
    );

    prover.prove_xor_and_or_shift_csr(
        &mut accumulators,
        snapshot,
        &prepared,
        &mut read_sets,
        &mut write_sets,
    );

    prover.prove_mul_div(
        &mut accumulators,
        snapshot,
        &prepared,
        &mut read_sets,
        &mut write_sets,
    );

    prover.prove_load_store(
        &mut accumulators,
        snapshot,
        &prepared,
        &mut read_sets,
        &mut write_sets,
    );

    prover.prove_subword_load_store(
        &mut accumulators,
        snapshot,
        &prepared,
        &mut read_sets,
        &mut write_sets,
    );
    // Machine state permutation ended
    validate_sets(&read_sets, &write_sets);

    prover.prove_init_and_teardowns(&mut accumulators, &prepared.inits_and_teardowns);
    // now prove delegation circuits
    prover.prove_blake_delegation(
        &mut accumulators,
        &prepared.counters,
        snapshot.snapshotter(),
        &mut read_sets,
        &mut write_sets,
        snapshot.tape(),
        snapshot.cycles_bound(),
        prepared.expected_final_state,
    );

    prover.prove_keccak_delegation(
        &mut accumulators,
        &prepared.counters,
        snapshot.snapshotter(),
        &mut read_sets,
        &mut write_sets,
        snapshot.tape(),
        snapshot.cycles_bound(),
        prepared.expected_final_state,
    );

    dbg!(accumulators.permutation_argument());
    dbg!(accumulators.delegation_argument());

    // inits and teardowns
    validate_inits_and_teardowns(
        &read_sets,
        &write_sets,
        &prepared.flattened_inits_and_teardowns,
        &accumulators,
        prepared.total_unique_teardowns,
    );
}
