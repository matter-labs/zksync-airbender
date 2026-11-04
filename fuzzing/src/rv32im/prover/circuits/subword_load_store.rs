use std::alloc::Global;

use load_store_subword_only_verifier::verify_80;
use prover::common_constants;
use prover::common_constants::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX;
use prover::cs::cs::circuit::Circuit as _;
use prover::cs::cs::oracle::ExecutorFamilyDecoderData;
use prover::cs::machine::ops::unrolled::compile_unrolled_circuit_state_transition;
use prover::cs::machine::ops::unrolled::load_store::*;
use prover::cs::machine::ops::unrolled::load_store_subword_only::subword_only_load_store_circuit_with_preprocessed_bytecode;
use prover::cs::machine::ops::unrolled::load_store_subword_only::subword_only_load_store_table_addition_fn;
use prover::cs::machine::ops::unrolled::load_store_subword_only::subword_only_load_store_table_driver_fn;
use prover::cs::one_row_compiler::CompiledCircuitArtifact;
use prover::cs::tables::LookupWrapper;
use prover::cs::tables::TableDriver;
use prover::cs::tables::TableType;
use prover::field::Field as _;
use prover::field::Mersenne31Field;
use prover::field::Mersenne31Quartic;
use prover::prover_stages::unrolled_prover::UnrolledModeProof;
use prover::tests::unrolled::subword_load_store;
use prover::unrolled::MemoryCircuitOracle;
use prover::SimpleWitnessProxy;
use prover::DEFAULT_TRACE_PADDING_MULTIPLE;
use riscv_transpiler::machine_mode_only_unrolled::MemoryOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::MemDestinationHolder;
use verifier_common::proof_flattener::flatten_query;
use verifier_common::proof_flattener::flatten_unrolled_circuits_proof_for_skeleton;

use crate::rv32im::prover::accumulators::Accumulators;
use crate::rv32im::prover::circuits::helpers::run_verifier_in_thread;
use crate::rv32im::prover::circuits::helpers::validator_outputs;
use crate::rv32im::prover::circuits::traces::FullAndMemTraces;
use crate::rv32im::prover::circuits::CircuitProver;
use crate::rv32im::prover::circuits::ProofInputs;
use crate::rv32im::prover::sets::ReadSets;
use crate::rv32im::prover::sets::WriteSets;
use crate::rv32im::prover::PreparedExecution;
use crate::rv32im::prover::Prover;
use crate::rv32im::prover::TRACE_LEN_LOG2;
use crate::rv32im::vm::VMSnapshot;

impl Prover {
    pub fn prove_subword_load_store(
        &self,
        accumulators: &mut Accumulators,
        snapshot: VMSnapshot,
        prepared: &PreparedExecution,
        read_sets: &mut ReadSets,
        write_sets: &mut WriteSets,
    ) {
        let circuit = LoadStoreSubwordCircuit::new(snapshot.binary());
        circuit.prove(
            snapshot,
            prepared,
            accumulators,
            read_sets,
            write_sets,
            self,
            self.worker(),
        );
    }
}

pub struct LoadStoreSubwordCircuit {
    extra_tables: [(TableType, LookupWrapper<Mersenne31Field>); 2],
}

impl LoadStoreSubwordCircuit {
    pub fn new(bytecode: &[u32]) -> Self {
        let extra_tables = create_load_store_special_tables::<
            _,
            { common_constants::ROM_SECOND_WORD_BITS },
        >(bytecode);
        Self { extra_tables }
    }

    pub fn validate_proof(
        inputs: &ProofInputs<MemoryOpcodeTracingDataWithTimestamp>,
        proof: &UnrolledModeProof,
    ) -> Result<(), ()> {
        let mut oracle_data =
            flatten_unrolled_circuits_proof_for_skeleton(proof, inputs.compiled_circuit());
        for query in proof.queries.iter() {
            oracle_data.extend(flatten_query(query));
        }

        run_verifier_in_thread("subword-load-store-verifier", oracle_data, move || {
            let (mut proof_state_dst, mut proof_input_dst) = validator_outputs();
            unsafe {
                // Fuzzing uses the verifier crate's fixed Security80 entrypoint to match the
                // prover configuration and avoid threading the newer generic security API here.
                verify_80(&mut proof_state_dst, &mut proof_input_dst)
            };
        })
    }
}

impl CircuitProver<LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX> for LoadStoreSubwordCircuit {
    type BufferElt = MemoryOpcodeTracingDataWithTimestamp;
    type Tracer<'t> = MemDestinationHolder<'t, LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX>;
    type Oracle<'o> = MemoryCircuitOracle<'o>;
    type TracesFactory<'o, 'r>
        = FullAndMemTraces<Global, DEFAULT_TRACE_PADDING_MULTIPLE>
    where
        MemoryCircuitOracle<'o>: 'r;

    fn compile_circuit(&self) -> CompiledCircuitArtifact<Mersenne31Field> {
        compile_unrolled_circuit_state_transition::<Mersenne31Field>(
            &|cs| {
                subword_only_load_store_table_addition_fn(cs);
                for (table_type, table) in self.extra_tables.clone() {
                    cs.add_table_with_content(table_type, table);
                }
            },
            &|cs| {
                subword_only_load_store_circuit_with_preprocessed_bytecode::<
                    _,
                    _,
                    { common_constants::ROM_SECOND_WORD_BITS },
                >(cs)
            },
            1 << 20,
            TRACE_LEN_LOG2,
        )
    }

    fn name(&self) -> &str {
        "subword LOAD/STORE"
    }

    fn fill_table(&self, table_driver: &mut TableDriver<Mersenne31Field>) {
        subword_only_load_store_table_driver_fn(table_driver);
        for (table_type, table) in self.extra_tables.clone() {
            table_driver.add_table_with_content(table_type, table);
        }
    }

    fn create_buffer(&self, size: usize) -> Vec<Self::BufferElt> {
        vec![Self::BufferElt::default(); size]
    }

    fn create_tracer<'t>(&self, buffers: &'t mut [&'t mut [Self::BufferElt]]) -> Self::Tracer<'t> {
        MemDestinationHolder { buffers }
    }

    fn create_oracle<'o>(
        &self,
        inner: &'o [Self::BufferElt],
        decoder_table: &'o [ExecutorFamilyDecoderData],
    ) -> Self::Oracle<'o> {
        MemoryCircuitOracle {
            inner,
            decoder_table,
        }
    }

    fn witness_eval(w: &mut SimpleWitnessProxy<Self::Oracle<'_>>) {
        subword_load_store::witness_eval_fn(w)
    }

    fn check_constraints(&self, proof: &UnrolledModeProof, oracle: &Self::Oracle<'_>) {
        if oracle.inner.is_empty() {
            assert_eq!(
                proof.permutation_grand_product_accumulator,
                Mersenne31Quartic::ONE
            );
        }
        assert!(proof.delegation_argument_accumulator.is_none());
    }

    fn accumulate(&self, accumulators: &mut Accumulators, proof: &UnrolledModeProof) {
        accumulators
            .permutation_argument_mut()
            .mul_assign(&proof.permutation_grand_product_accumulator);
    }

    fn validate_proof(
        &self,
        inputs: &ProofInputs<Self::BufferElt>,
        proof: &UnrolledModeProof,
    ) -> Result<(), ()> {
        LoadStoreSubwordCircuit::validate_proof(inputs, proof)
    }
}
