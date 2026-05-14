use riscv_transpiler::machine_mode_only_unrolled::MemoryOpcodeTracingDataWithTimestamp;
use riscv_transpiler::machine_mode_only_unrolled::NonMemoryOpcodeTracingDataWithTimestamp;

use crate::prover::circuits::CircuitKind;
use crate::prover::seeds::StoredProofInputs;
#[cfg(feature = "prover")]
use crate::rv32im::prover::circuits::ProofInputs;

/// Compact structural facts about the input seen before deep proving artifacts are produced.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct OracleShapeSummary {
    circuit: CircuitKind,
    decoder_table_len: usize,
    witness_gen_len: usize,
    buffer_len: usize,
    bytecode_len: Option<usize>,
}

impl OracleShapeSummary {
    /// Extracts a small structural summary from the stored proof inputs without materializing huge
    /// diffs.
    pub fn from_input(input: &StoredProofInputs) -> OracleShapeSummary {
        // This summary captures cheap structural facts that can change prover behavior without
        // dumping or diffing the huge witness/proof artifacts themselves.
        match input {
            StoredProofInputs::AddSubLuiAuipcMop(inputs) => {
                oracle_shape_non_mem(CircuitKind::AddSubLuiAuipcMop, inputs)
            }
            StoredProofInputs::JumpBranchSlt(inputs) => {
                oracle_shape_non_mem(CircuitKind::JumpBranchSlt, inputs)
            }
            StoredProofInputs::XorAndOrShiftCsr(inputs) => {
                oracle_shape_non_mem(CircuitKind::XorAndOrShiftCsr, inputs)
            }
            StoredProofInputs::MulDiv(inputs) => oracle_shape_non_mem(CircuitKind::MulDiv, inputs),
            StoredProofInputs::LoadStore(inputs, bytecode) => {
                oracle_shape_mem(CircuitKind::LoadStore, inputs, Some(bytecode.len()))
            }
            StoredProofInputs::SubwordLoadStore(inputs, bytecode) => {
                oracle_shape_mem(CircuitKind::SubwordLoadStore, inputs, Some(bytecode.len()))
            }
            StoredProofInputs::InitsAndTeardowns(_) => todo!(),
            StoredProofInputs::BlakeDelegation(_) => todo!(),
            StoredProofInputs::KeccakDelegation(_) => todo!(),
        }
    }

    #[allow(dead_code)]
    #[cfg(test)]
    pub fn new(
        circuit: CircuitKind,
        decoder_table_len: usize,
        witness_gen_len: usize,
        buffer_len: usize,
        bytecode_len: Option<usize>,
    ) -> Self {
        Self {
            circuit,
            decoder_table_len,
            witness_gen_len,
            buffer_len,
            bytecode_len,
        }
    }
}

/// Builds an oracle-shape summary for non-memory circuits.
fn oracle_shape_non_mem(
    circuit: CircuitKind,
    inputs: &ProofInputs<NonMemoryOpcodeTracingDataWithTimestamp>,
) -> OracleShapeSummary {
    OracleShapeSummary {
        circuit,
        decoder_table_len: inputs.decoder_table_data.len(),
        witness_gen_len: inputs.witness_gen_data.len(),
        buffer_len: inputs.buffer.len(),
        bytecode_len: None,
    }
}

/// Builds an oracle-shape summary for memory circuits, including bytecode size.
fn oracle_shape_mem(
    circuit: CircuitKind,
    inputs: &ProofInputs<MemoryOpcodeTracingDataWithTimestamp>,
    bytecode_len: Option<usize>,
) -> OracleShapeSummary {
    OracleShapeSummary {
        circuit,
        decoder_table_len: inputs.decoder_table_data.len(),
        witness_gen_len: inputs.witness_gen_data.len(),
        buffer_len: inputs.buffer.len(),
        bytecode_len,
    }
}
