use add_sub_lui_auipc_mop_verifier::verify_80;
use prover::common_constants::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;
use prover::cs::machine::ops::unrolled::add_sub_lui_auipc_mop::*;
use prover::cs::machine::ops::unrolled::compile_unrolled_circuit_state_transition;
use prover::cs::one_row_compiler::CompiledCircuitArtifact;
use prover::cs::tables::TableDriver;
use prover::field::Field as _;
use prover::field::Mersenne31Field;
use prover::field::Mersenne31Quartic;
use prover::prover_stages::unrolled_prover::UnrolledModeProof;
use prover::tests::unrolled::add_sub_lui_auipc_mod;
use prover::unrolled::NonMemoryCircuitOracle;
use prover::SimpleWitnessProxy;
use riscv_transpiler::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;
use verifier_common::proof_flattener::flatten_query;
use verifier_common::proof_flattener::flatten_unrolled_circuits_proof_for_skeleton;

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

pub struct AddSubLuiAuipcMop;

impl AddSubLuiAuipcMop {
    pub fn validate_proof(
        inputs: &ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>,
        proof: &UnrolledModeProof,
    ) -> Result<(), ()> {
        let mut oracle_data =
            flatten_unrolled_circuits_proof_for_skeleton(proof, inputs.compiled_circuit());
        for query in proof.queries.iter() {
            oracle_data.extend(flatten_query(query));
        }

        run_verifier_in_thread("add-sub-lui-auipc-mop-verifier", oracle_data, move || {
            let (mut proof_state_dst, mut proof_input_dst) = validator_outputs();
            unsafe {
                // Fuzzing uses the verifier crate's fixed Security80 entrypoint to match the
                // prover configuration and avoid threading the newer generic security API here.
                verify_80(&mut proof_state_dst, &mut proof_input_dst)
            };
        })
    }
}

impl NonMemoryCircuitProver<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX> for AddSubLuiAuipcMop {
    fn compile_circuit(&self) -> CompiledCircuitArtifact<Mersenne31Field> {
        compile_unrolled_circuit_state_transition::<Mersenne31Field>(
            &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
            &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode(cs),
            1 << 20,
            TRACE_LEN_LOG2,
        )
    }

    fn name(&self) -> &str {
        "ADD/SUB/LUI/AUIPC/MOP"
    }

    fn fill_table(&self, _table_driver: &mut TableDriver<Mersenne31Field>) {}

    fn witness_eval(w: &mut SimpleWitnessProxy<NonMemoryCircuitOracle<'_>>) {
        add_sub_lui_auipc_mod::witness_eval_fn(w)
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
        AddSubLuiAuipcMop::validate_proof(inputs, proof)
    }
}

impl Prover {
    pub fn prove_add_sub_lui_auipc_mop(
        &self,
        accumulators: &mut Accumulators,
        snapshot: VMSnapshot,
        prepared: &PreparedExecution,
        read_sets: &mut ReadSets,
        write_sets: &mut WriteSets,
    ) {
        let circuit = AddSubLuiAuipcMop;
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
