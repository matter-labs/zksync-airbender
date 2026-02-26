use std::alloc::Global;

use prover::common_constants;
use prover::cs::cs::oracle::ExecutorFamilyDecoderData;
use prover::cs::cs::oracle::Oracle;
use prover::cs::machine::ops::unrolled::materialize_flattened_decoder_table;
use prover::cs::one_row_compiler::CompiledCircuitArtifact;
use prover::cs::tables::TableDriver;
use prover::definitions::AuxArgumentsBoundaryValues;
use prover::field::Mersenne31Field;
use prover::merkle_trees::DefaultTreeConstructor;
use prover::prover_stages::unrolled_prover::UnrolledModeProof;
use prover::prover_stages::ProverData;
use prover::risc_v_simulator::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;
use prover::unrolled::NonMemoryCircuitOracle;
use prover::worker::Worker;
use prover::SimpleWitnessProxy;
use prover::WitnessEvaluationDataForExecutionFamily;
use prover::DEFAULT_TRACE_PADDING_MULTIPLE;
use riscv_transpiler::replayer::ReplayerRam;
use riscv_transpiler::replayer::ReplayerVM;
use riscv_transpiler::vm::Counters as _;
use riscv_transpiler::vm::ReplayBuffer as _;
use riscv_transpiler::vm::SimpleTape;
use riscv_transpiler::vm::State;
use riscv_transpiler::witness::NonMemDestinationHolder;
use riscv_transpiler::witness::WitnessTracer;

use crate::rv32im::prover::accumulators::Accumulators;
use crate::rv32im::prover::circuits::traces::FullAndMemTraces;
use crate::rv32im::prover::circuits::traces::TracesFactory;
use crate::rv32im::prover::factories::PreprocessingData;
use crate::rv32im::prover::sets::ReadSets;
use crate::rv32im::prover::sets::WriteSets;
use crate::rv32im::prover::PreparedExecution;
use crate::rv32im::prover::Prover;
use crate::rv32im::prover::ProvingPayload;
use crate::rv32im::prover::TRACE_LEN_LOG2;
use crate::rv32im::types::CountersT;
use crate::rv32im::types::Snapshotter;
use crate::rv32im::vm::VMSnapshot;

pub mod add_sub_lui_auipc_mop;
pub mod blake_delegation;
mod helpers;
pub mod inits_and_teardowns;
pub mod jump_branch_slt;
pub mod keccak_delegation;
pub mod load_store;
pub mod mul_div;
pub mod subword_load_store;
mod traces;
pub mod xor_and_or_shift_csr;

fn run_replayer_vm(
    snapshotter: &Snapshotter,
    tape: &SimpleTape,
    cycles_bound: usize,
    expected_final_state: State<CountersT>,
    tracer: &mut impl WitnessTracer,
) {
    let mut state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());

    let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };

    ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
        &mut state,
        &mut ram,
        tape,
        &mut (),
        cycles_bound,
        tracer,
    );
    assert_eq!(expected_final_state, state);
}

fn get_preprocessing_data(
    preprocessing_data: &PreprocessingData,
    idx: u8,
) -> (Vec<[Mersenne31Field; 10]>, &Vec<ExecutorFamilyDecoderData>) {
    let (decoder_table_data, witness_gen_data) = &preprocessing_data[&idx];
    let decoder_table_data = materialize_flattened_decoder_table(decoder_table_data);

    (decoder_table_data, witness_gen_data)
}

type FullTrace<A, const N: usize> = WitnessEvaluationDataForExecutionFamily<N, A>;

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ProofInputs<T> {
    pub(crate) family_idx: u8,
    pub(crate) circuit: CompiledCircuitArtifact<Mersenne31Field>,
    pub(crate) decoder_table_data: Vec<[Mersenne31Field; 10]>,
    pub(crate) witness_gen_data: Vec<ExecutorFamilyDecoderData>,
    pub(crate) buffer: Vec<T>,
}

impl<T> ProofInputs<T> {
    pub fn family_idx(&self) -> u8 {
        self.family_idx
    }

    pub fn compiled_circuit(&self) -> &CompiledCircuitArtifact<Mersenne31Field> {
        &self.circuit
    }
}

impl<T: PartialEq> PartialEq for ProofInputs<T> {
    fn eq(&self, other: &Self) -> bool {
        // We don't check equality of circuits because we don't (currently) mutate it.
        self.family_idx == other.family_idx
            && self.decoder_table_data == other.decoder_table_data
            && self.witness_gen_data == other.witness_gen_data
            && self.buffer == other.buffer
    }
}

pub(crate) trait CircuitProver<const CIRCUIT_FAMILY_IDX: u8> {
    type BufferElt: serde::Serialize + for<'de> serde::Deserialize<'de>;
    type Tracer<'t>: WitnessTracer;
    type Oracle<'o>: Oracle<Mersenne31Field>;
    type TracesFactory<'o, 'r>: TracesFactory<
        (
            &'r Self::Oracle<'o>,
            fn(&mut SimpleWitnessProxy<'_, Self::Oracle<'o>>),
            usize,
            &'r mut ReadSets,
            &'r mut WriteSets,
        ),
        FullTrace = FullTrace<Global, DEFAULT_TRACE_PADDING_MULTIPLE>,
    >
    where
        Self::Oracle<'o>: 'r,
        'o: 'r;

    fn create_proof_input(
        &self,
        snapshot: VMSnapshot,
        prepared: &PreparedExecution,
        table_driver: &mut TableDriver<Mersenne31Field>,
    ) -> ProofInputs<Self::BufferElt> {
        let circuit = self.compile_circuit();

        self.fill_table(table_driver);

        let num_calls = prepared
            .counters
            .get_calls_to_circuit_family::<CIRCUIT_FAMILY_IDX>();
        let mut buffer = self.create_buffer(num_calls);
        run_replayer_vm(
            snapshot.snapshotter(),
            snapshot.tape(),
            snapshot.cycles_bound(),
            prepared.expected_final_state,
            &mut self.create_tracer(&mut [&mut buffer[..]]),
        );

        let (decoder_table_data, witness_gen_data) =
            get_preprocessing_data(&prepared.preprocessing_data, CIRCUIT_FAMILY_IDX);

        ProofInputs {
            family_idx: CIRCUIT_FAMILY_IDX,
            circuit,
            decoder_table_data,
            witness_gen_data: witness_gen_data.clone(),
            buffer,
        }
    }

    #[allow(clippy::too_many_arguments)]
    /// Pass None to table_driver if the proof inputs come from deserialized data.
    fn generate_proof_with_data(
        &self,
        inputs: &ProofInputs<Self::BufferElt>,
        prover: &Prover,
        worker: &Worker,
        oracle: &Self::Oracle<'_>,
        read_sets: &mut ReadSets,
        write_sets: &mut WriteSets,
        table_driver: Option<&TableDriver<Mersenne31Field>>,
    ) -> (
        ProverData<DEFAULT_TRACE_PADDING_MULTIPLE, Global, DefaultTreeConstructor>,
        UnrolledModeProof,
    ) {
        let mut local_table_driver = TableDriver::new();
        let table_driver = match table_driver {
            Some(table_driver) => table_driver,
            None => {
                self.fill_table(&mut local_table_driver);
                &local_table_driver
            }
        };
        let traces = Self::TracesFactory::new(
            &inputs.circuit,
            (
                oracle,
                Self::witness_eval,
                self.num_cycles_per_chunk(),
                read_sets,
                write_sets,
            ),
            table_driver,
            worker,
        );
        let aux_data = self.create_aux_data(&traces);

        prover.run_prover2(ProvingPayload::<_, DefaultTreeConstructor, _>::new(
            &inputs.circuit,
            traces.take_full_trace(),
            table_driver,
            &inputs.decoder_table_data,
            &aux_data,
            1 << self.trace_len_log2(),
            worker,
        ))
    }

    #[allow(clippy::too_many_arguments)]
    /// Pass None to table_driver if the proof inputs come from deserialized data.
    fn generate_proof(
        &self,
        inputs: &ProofInputs<Self::BufferElt>,
        prover: &Prover,
        worker: &Worker,
        oracle: &Self::Oracle<'_>,
        read_sets: &mut ReadSets,
        write_sets: &mut WriteSets,
        table_driver: Option<&TableDriver<Mersenne31Field>>,
    ) -> UnrolledModeProof {
        let (_, proof) = self.generate_proof_with_data(
            inputs,
            prover,
            worker,
            oracle,
            read_sets,
            write_sets,
            table_driver,
        );
        proof
    }

    #[allow(clippy::too_many_arguments)]
    /// Pass None to table_driver if the proof inputs come from deserialized data.
    fn check_proof(
        &self,
        inputs: ProofInputs<Self::BufferElt>,
        accumulators: &mut Accumulators,
        read_sets: &mut ReadSets,
        write_sets: &mut WriteSets,
        prover: &Prover,
        worker: &Worker,
        table_driver: Option<&TableDriver<Mersenne31Field>>,
    ) {
        let oracle = self.create_oracle(&inputs.buffer, &inputs.witness_gen_data);
        let proof = self.generate_proof(
            &inputs,
            prover,
            worker,
            &oracle,
            read_sets,
            write_sets,
            table_driver,
        );
        self.validate_proof(&inputs, &proof)
            .expect("generated proof must pass verifier");
        self.check_constraints(&proof, &oracle);
        self.accumulate(accumulators, &proof);
    }

    fn prove_from_inputs(
        &self,
        inputs: ProofInputs<Self::BufferElt>,
        prover: &Prover,
        worker: &Worker,
    ) -> UnrolledModeProof {
        let oracle = self.create_oracle(&inputs.buffer, &inputs.witness_gen_data);
        self.generate_proof(
            &inputs,
            prover,
            worker,
            &oracle,
            &mut ReadSets::empty(),
            &mut WriteSets::empty(),
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn prove(
        &self,
        snapshot: VMSnapshot,
        prepared: &PreparedExecution,
        accumulators: &mut Accumulators,
        read_sets: &mut ReadSets,
        write_sets: &mut WriteSets,
        prover: &Prover,
        worker: &Worker,
    ) {
        println!("Will try to prove {} circuit", self.name());
        let mut table_driver = TableDriver::<Mersenne31Field>::new();
        let inputs = self.create_proof_input(snapshot, prepared, &mut table_driver);
        self.check_proof(
            inputs,
            accumulators,
            read_sets,
            write_sets,
            prover,
            worker,
            Some(&table_driver),
        );
    }

    fn compile_circuit(&self) -> CompiledCircuitArtifact<Mersenne31Field>;

    fn name(&self) -> &str;

    fn fill_table(&self, table_driver: &mut TableDriver<Mersenne31Field>);

    fn create_buffer(&self, size: usize) -> Vec<Self::BufferElt>;

    fn create_tracer<'t>(&self, buffers: &'t mut [&'t mut [Self::BufferElt]]) -> Self::Tracer<'t>;

    fn create_oracle<'o>(
        &self,
        buffer: &'o [Self::BufferElt],
        decoder_table: &'o [ExecutorFamilyDecoderData],
    ) -> Self::Oracle<'o>;

    fn witness_eval(w: &mut SimpleWitnessProxy<Self::Oracle<'_>>);

    fn check_constraints(&self, proof: &UnrolledModeProof, oracle: &Self::Oracle<'_>);

    fn accumulate(&self, accumulators: &mut Accumulators, proof: &UnrolledModeProof);

    fn validate_proof(
        &self,
        inputs: &ProofInputs<Self::BufferElt>,
        proof: &UnrolledModeProof,
    ) -> Result<(), ()>;

    #[allow(unused_variables)]
    fn create_aux_data<'i, 'r>(
        &self,
        traces: &Self::TracesFactory<'i, 'r>,
    ) -> Vec<AuxArgumentsBoundaryValues> {
        vec![]
    }

    fn trace_len_log2(&self) -> usize {
        TRACE_LEN_LOG2
    }

    fn num_cycles_per_chunk(&self) -> usize {
        (1 << self.trace_len_log2()) - 1
    }
}

trait NonMemoryCircuitProver<const N: u8> {
    fn compile_circuit(&self) -> CompiledCircuitArtifact<Mersenne31Field>;
    fn name(&self) -> &str;
    fn fill_table(&self, table_driver: &mut TableDriver<Mersenne31Field>);
    fn witness_eval(w: &mut SimpleWitnessProxy<NonMemoryCircuitOracle<'_>>);
    fn check_constraints(&self, proof: &UnrolledModeProof, is_empty: bool);
    fn accumulate(&self, accumulators: &mut Accumulators, proof: &UnrolledModeProof);
    fn validate_proof(
        &self,
        inputs: &ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>,
        proof: &UnrolledModeProof,
    ) -> Result<(), ()>;

    fn default_pc_value_in_padding(&self) -> u32 {
        4
    }

    fn trace_len_log2(&self) -> usize {
        TRACE_LEN_LOG2
    }
}

impl<const N: u8, T: NonMemoryCircuitProver<N>> CircuitProver<N> for T {
    type BufferElt = NonMemoryOpcodeTracingDataWithTimestamp;
    type Tracer<'t> = NonMemDestinationHolder<'t, N>;
    type Oracle<'o> = NonMemoryCircuitOracle<'o>;
    type TracesFactory<'o, 'r>
        = FullAndMemTraces<Global, DEFAULT_TRACE_PADDING_MULTIPLE>
    where
        NonMemoryCircuitOracle<'o>: 'r;

    fn compile_circuit(&self) -> CompiledCircuitArtifact<Mersenne31Field> {
        self.compile_circuit()
    }

    fn name(&self) -> &str {
        self.name()
    }

    fn fill_table(&self, table_driver: &mut TableDriver<Mersenne31Field>) {
        self.fill_table(table_driver);
    }

    fn create_buffer(&self, size: usize) -> Vec<Self::BufferElt> {
        vec![Self::BufferElt::default(); size]
    }

    fn create_tracer<'t>(&self, buffers: &'t mut [&'t mut [Self::BufferElt]]) -> Self::Tracer<'t> {
        NonMemDestinationHolder { buffers }
    }

    fn create_oracle<'o>(
        &self,
        inner: &'o [Self::BufferElt],
        decoder_table: &'o [ExecutorFamilyDecoderData],
    ) -> Self::Oracle<'o> {
        NonMemoryCircuitOracle {
            inner,
            decoder_table,
            default_pc_value_in_padding:
                <Self as NonMemoryCircuitProver<N>>::default_pc_value_in_padding(self),
        }
    }

    fn witness_eval(w: &mut SimpleWitnessProxy<Self::Oracle<'_>>) {
        <Self as NonMemoryCircuitProver<N>>::witness_eval(w)
    }

    fn check_constraints(&self, proof: &UnrolledModeProof, oracle: &Self::Oracle<'_>) {
        self.check_constraints(proof, oracle.inner.is_empty())
    }

    fn accumulate(&self, accumulators: &mut Accumulators, proof: &UnrolledModeProof) {
        self.accumulate(accumulators, proof);
    }

    fn validate_proof(
        &self,
        inputs: &ProofInputs<Self::BufferElt>,
        proof: &UnrolledModeProof,
    ) -> Result<(), ()> {
        self.validate_proof(inputs, proof)
    }

    fn trace_len_log2(&self) -> usize {
        <Self as NonMemoryCircuitProver<N>>::trace_len_log2(self)
    }
}
