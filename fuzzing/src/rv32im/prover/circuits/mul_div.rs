use mul_div_unsigned_verifier::verify_80;
use prover::common_constants::MUL_DIV_CIRCUIT_FAMILY_IDX;
use prover::cs::machine::ops::unrolled::compile_unrolled_circuit_state_transition;
use prover::cs::machine::ops::unrolled::mul_div::*;
use prover::cs::one_row_compiler::CompiledCircuitArtifact;
use prover::cs::tables::TableDriver;
use prover::field::Field as _;
use prover::field::Mersenne31Field;
use prover::field::Mersenne31Quartic;
use prover::prover_stages::unrolled_prover::UnrolledModeProof;
use prover::tests::unrolled::mul_div;
use prover::tests::unrolled::mul_div_unsigned_only;
use prover::unrolled::NonMemoryCircuitOracle;
use prover::SimpleWitnessProxy;
use riscv_transpiler::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;
use verifier_common::proof_flattener::flatten_query;
use verifier_common::proof_flattener::flatten_unrolled_circuits_proof_for_skeleton;

use crate::rv32im::prover::accumulators::Accumulators;
use crate::rv32im::prover::circuits::helpers::run_verifier_in_thread;
use crate::rv32im::prover::circuits::helpers::validator_outputs;
use crate::rv32im::prover::circuits::CircuitProver as _;
use crate::rv32im::prover::circuits::NonMemoryCircuitProver;
use crate::rv32im::prover::circuits::ProofInputs;
use crate::rv32im::prover::sets::ReadSets;
use crate::rv32im::prover::sets::WriteSets;
use crate::rv32im::prover::PreparedExecution;
use crate::rv32im::prover::Prover;
use crate::rv32im::prover::MUL_DIV_TRACE_LEN_LOG2;
use crate::rv32im::prover::SUPPORT_SIGNED;
use crate::rv32im::vm::VMSnapshot;

pub struct MulDivCircuit;

impl MulDivCircuit {
    pub fn validate_proof(
        inputs: &ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>,
        proof: &UnrolledModeProof,
    ) -> Result<(), ()> {
        let mut oracle_data =
            flatten_unrolled_circuits_proof_for_skeleton(proof, inputs.compiled_circuit());
        for query in proof.queries.iter() {
            oracle_data.extend(flatten_query(query));
        }

        run_verifier_in_thread("mul-div-verifier", oracle_data, move || {
            let (mut proof_state_dst, mut proof_input_dst) = validator_outputs();
            unsafe {
                // Fuzzing uses the verifier crate's fixed Security80 entrypoint to match the
                // prover configuration and avoid threading the newer generic security API here.
                verify_80(&mut proof_state_dst, &mut proof_input_dst)
            };
        })
    }
}

impl NonMemoryCircuitProver<MUL_DIV_CIRCUIT_FAMILY_IDX> for MulDivCircuit {
    fn compile_circuit(&self) -> CompiledCircuitArtifact<Mersenne31Field> {
        compile_unrolled_circuit_state_transition::<Mersenne31Field>(
            &|cs| {
                mul_div_table_addition_fn(cs);
            },
            &|cs| mul_div_circuit_with_preprocessed_bytecode::<_, _, SUPPORT_SIGNED>(cs),
            1 << 20,
            MUL_DIV_TRACE_LEN_LOG2,
        )
    }

    fn name(&self) -> &str {
        "MUL/DIV"
    }

    fn fill_table(&self, table_driver: &mut TableDriver<Mersenne31Field>) {
        mul_div_table_driver_fn(table_driver);
    }

    fn witness_eval(w: &mut SimpleWitnessProxy<NonMemoryCircuitOracle<'_>>) {
        if SUPPORT_SIGNED {
            mul_div::witness_eval_fn(w)
        } else {
            mul_div_unsigned_only::witness_eval_fn(w)
        }
    }

    fn check_constraints(&self, proof: &UnrolledModeProof, is_empty: bool) {
        if is_empty {
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
        inputs: &ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>,
        proof: &UnrolledModeProof,
    ) -> Result<(), ()> {
        MulDivCircuit::validate_proof(inputs, proof)
    }

    fn trace_len_log2(&self) -> usize {
        MUL_DIV_TRACE_LEN_LOG2
    }
}

impl Prover {
    pub fn prove_mul_div(
        &self,
        accumulators: &mut Accumulators,
        snapshot: VMSnapshot,
        prepared: &PreparedExecution,
        read_sets: &mut ReadSets,
        write_sets: &mut WriteSets,
    ) {
        let circuit = MulDivCircuit;
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
