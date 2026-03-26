use crate::definitions::TimestampScalar;
use crate::gkr_circuits::ExecutorFamilyDecoderData;
use field::PrimeField;

mod placeholder;

pub use self::placeholder::Placeholder;

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
            .as_u32_reduced() as u16
    }

    fn get_u8_witness_from_placeholder(&self, placeholder: Placeholder, trace_row: usize) -> u8 {
        self.get_witness_from_placeholder(placeholder, 0, trace_row)
            .as_u32_reduced() as u8
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

    fn get_executor_family_data(&self, trace_row: usize) -> ExecutorFamilyDecoderData;
}
