use field::PrimeField;

use crate::definitions::TimestampScalar;

use super::placeholder::Placeholder;

#[derive(Clone, Copy, Debug)]
pub struct ExecutorFamilyDecoderData {
    pub imm: u32,
    pub rs1_index: u8,
    pub rs2_index: u8,
    pub rd_index: u8,
    pub rd_is_zero: bool,
    pub funct3: u8,
    pub funct7: Option<u8>,
    pub opcode_family_bits: u8,
}

impl Default for ExecutorFamilyDecoderData {
    fn default() -> Self {
        // We make a value that is self-consistent, and as family-agnostic as possible
        ExecutorFamilyDecoderData {
            imm: 0,
            rs1_index: 0,
            rs2_index: 0,
            rd_index: 0,
            rd_is_zero: true, // consistency!
            funct3: 0,
            funct7: None,
            opcode_family_bits: 0,
        }
    }
}

pub trait Oracle<F: PrimeField>: Send + Sync {
    fn get_witness_from_placeholder(
        &self,
        placeholder: Placeholder,
        subindex: usize,
        trace_row: usize,
    ) -> F;

    fn get_u32_witness_from_placeholder(&self, placeholder: Placeholder, trace_row: usize) -> u32;

    fn get_u16_witness_from_placeholder(&self, placeholder: Placeholder, trace_row: usize) -> u16 {
        self.get_witness_from_placeholder(placeholder, 0, trace_row)
            .as_u64_reduced() as u16
    }

    fn get_u8_witness_from_placeholder(&self, placeholder: Placeholder, trace_row: usize) -> u8 {
        self.get_witness_from_placeholder(placeholder, 0, trace_row)
            .as_u64_reduced() as u8
    }

    fn get_boolean_witness_from_placeholder(
        &self,
        placeholder: Placeholder,
        trace_row: usize,
    ) -> bool {
        self.get_witness_from_placeholder(placeholder, 0, trace_row)
            .as_boolean()
    }

    fn get_timestamp_witness_from_placeholder(
        &self,
        placeholder: Placeholder,
        trace_row: usize,
    ) -> TimestampScalar;

    fn get_executor_family_data(&self, trace_row: usize) -> ExecutorFamilyDecoderData {
        let _ = trace_row;
        unimplemented!("unimplemented by default")
    }
}
