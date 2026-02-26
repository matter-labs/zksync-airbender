use prover::common_constants::BLAKE2S_DELEGATION_CSR_REGISTER;
use prover::common_constants::KECCAK_SPECIAL5_CSR_REGISTER;
use prover::common_constants::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX;
use prover::cs::cs::circuit::Circuit as _;
use prover::cs::machine::machine_configurations::create_csr_table_for_delegation;
use prover::cs::machine::ops::unrolled::compile_unrolled_circuit_state_transition;
use prover::cs::one_row_compiler::CompiledCircuitArtifact;
use prover::cs::tables::LookupTable;
use prover::cs::tables::LookupWrapper;
use prover::cs::tables::TableDriver;
use prover::cs::tables::TableType;
use prover::field::Field as _;
use prover::field::Mersenne31Field;
use prover::field::Mersenne31Quartic;
use prover::nd_source_std::ThreadLocalBasedSource;
use prover::prover_stages::unrolled_prover::UnrolledModeProof;
use prover::risc_v_simulator::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;
use prover::tests::unrolled::shift_binop_csrrw;
use prover::unrolled::NonMemoryCircuitOracle;
use prover::SimpleWitnessProxy;
use shift_binary_csr_verifier::verify_with_configuration;
use verifier_common::proof_flattener::flatten_query;
use verifier_common::proof_flattener::flatten_unrolled_circuits_proof_for_skeleton;
use verifier_common::DefaultLeafInclusionVerifier;

use crate::rv32im::prover::accumulators::Accumulators;
use crate::rv32im::prover::circuits::helpers::run_verifier_in_thread;
use crate::rv32im::prover::circuits::helpers::validator_outputs;
use crate::rv32im::prover::circuits::CircuitProver;
use crate::rv32im::prover::circuits::NonMemoryCircuitProver;
use crate::rv32im::prover::circuits::ProofInputs;
use crate::rv32im::prover::sets::ReadSets;
use crate::rv32im::prover::sets::WriteSets;
use crate::rv32im::prover::PreparedExecution;
use crate::rv32im::prover::Prover;
use crate::rv32im::prover::TRACE_LEN_LOG2;
use crate::rv32im::vm::VMSnapshot;

use prover::cs::machine::ops::unrolled::shift_binary_csr::*;

pub struct XorAndOrShiftCsrCircuit {
    csr_table: LookupTable<Mersenne31Field, 3>,
}

impl XorAndOrShiftCsrCircuit {
    pub fn new() -> Self {
        Self {
            csr_table: create_csr_table_for_delegation::<Mersenne31Field>(
                true,
                &[
                    BLAKE2S_DELEGATION_CSR_REGISTER,
                    KECCAK_SPECIAL5_CSR_REGISTER,
                ],
                TableType::SpecialCSRProperties.to_table_id(),
            ),
        }
    }

    pub fn validate_proof(
        inputs: &ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>,
        proof: &UnrolledModeProof,
    ) -> Result<(), ()> {
        let mut oracle_data =
            flatten_unrolled_circuits_proof_for_skeleton(proof, inputs.compiled_circuit());
        for query in proof.queries.iter() {
            oracle_data.extend(flatten_query(query));
        }

        run_verifier_in_thread("xor-and-or-shift-csr-verifier", oracle_data, move || {
            let (mut proof_state_dst, mut proof_input_dst) = validator_outputs();
            unsafe {
                verify_with_configuration::<ThreadLocalBasedSource, DefaultLeafInclusionVerifier>(
                    &mut proof_state_dst,
                    &mut proof_input_dst,
                )
            };
        })
    }
}

impl NonMemoryCircuitProver<SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX> for XorAndOrShiftCsrCircuit {
    fn compile_circuit(&self) -> CompiledCircuitArtifact<Mersenne31Field> {
        compile_unrolled_circuit_state_transition::<Mersenne31Field>(
            &|cs| {
                shift_binop_csrrw_table_addition_fn(cs);
                // and we need to add CSR table
                cs.add_table_with_content(
                    TableType::SpecialCSRProperties,
                    LookupWrapper::Dimensional3(self.csr_table.clone()),
                );
            },
            &|cs| shift_binop_csrrw_circuit_with_preprocessed_bytecode::<_, _>(cs),
            1 << 20,
            TRACE_LEN_LOG2,
        )
    }

    fn name(&self) -> &str {
        "XOR/AND/OR/SHIFT/CSR"
    }

    fn fill_table(&self, table_driver: &mut TableDriver<Mersenne31Field>) {
        shift_binop_csrrw_table_driver_fn(table_driver);
        table_driver.add_table_with_content(
            TableType::SpecialCSRProperties,
            LookupWrapper::Dimensional3(self.csr_table.clone()),
        );
    }

    fn witness_eval(w: &mut SimpleWitnessProxy<NonMemoryCircuitOracle<'_>>) {
        shift_binop_csrrw::witness_eval_fn(w)
    }

    fn check_constraints(&self, proof: &UnrolledModeProof, is_empty: bool) {
        if is_empty {
            assert_eq!(
                proof.permutation_grand_product_accumulator,
                Mersenne31Quartic::ONE
            );
            assert_eq!(
                proof.delegation_argument_accumulator.unwrap(),
                Mersenne31Quartic::ZERO
            );
        }
    }

    fn accumulate(&self, accumulators: &mut Accumulators, proof: &UnrolledModeProof) {
        dbg!(proof.delegation_argument_accumulator.unwrap());

        accumulators
            .delegation_argument_mut()
            .add_assign(&proof.delegation_argument_accumulator.unwrap());
        accumulators
            .permutation_argument_mut()
            .mul_assign(&proof.permutation_grand_product_accumulator);
    }

    fn validate_proof(
        &self,
        inputs: &ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>,
        proof: &UnrolledModeProof,
    ) -> Result<(), ()> {
        XorAndOrShiftCsrCircuit::validate_proof(inputs, proof)
    }
}

impl Prover {
    pub fn prove_xor_and_or_shift_csr(
        &self,
        accumulators: &mut Accumulators,
        snapshot: VMSnapshot,
        prepared: &PreparedExecution,
        read_sets: &mut ReadSets,
        write_sets: &mut WriteSets,
    ) {
        let circuit = XorAndOrShiftCsrCircuit::new();
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
