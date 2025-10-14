use super::scalar_witness_type_set::ScalarWitnessTypeSet;
use super::*;
use crate::cs::oracle::{ExecutorFamilyDecoderData, Oracle};
use crate::definitions::Variable;
use crate::tables::TableDriver;
use field::PrimeField;

use super::WitnessPlacer;

pub struct CSDebugWitnessEvaluator<F: PrimeField> {
    pub(crate) values: Vec<F>,
    pub oracle: Option<Box<dyn Oracle<F>>>,
    pub(crate) table_driver: TableDriver<F>,
    pub(crate) preprocessed_decoder_table: Option<Vec<ExecutorFamilyDecoderData>>,
}

impl<F: PrimeField> CSDebugWitnessEvaluator<F> {
    pub fn new() -> Self {
        Self {
            values: Vec::new(),
            oracle: None,
            table_driver: TableDriver::new(),
            preprocessed_decoder_table: None,
        }
    }

    pub fn new_with_oracle<O: Oracle<F> + 'static>(oracle: O) -> Self {
        let mut new = Self::new();
        new.oracle = Some(Box::new(oracle));

        new
    }

    pub fn new_with_oracle_and_preprocessed_decoder<O: Oracle<F> + 'static>(
        oracle: O,
        preprocessed_decoder_table: Vec<ExecutorFamilyDecoderData>,
    ) -> Self {
        let mut new = Self::new();
        new.oracle = Some(Box::new(oracle));
        new.preprocessed_decoder_table = Some(preprocessed_decoder_table);

        new
    }

    pub fn get_value(&self, variable: Variable) -> Option<F> {
        if variable.is_placeholder() {
            panic!("variable is placeholder");
        }
        let idx = variable.0 as usize;
        if idx >= self.values.len() {
            None
        } else {
            Some(self.values[idx])
        }
    }

    pub fn evaluate(&mut self, node: &impl WitnessResolutionDescription<F, Self>) {
        node.evaluate(self);
    }

    pub fn resolve_placeholder(
        &mut self,
        variable: Variable,
        placeholder: Placeholder,
        subindex: usize,
    ) {
        if variable.is_placeholder() {
            panic!("variable is placeholder");
        }
        if let Some(oracle) = self.oracle.as_ref() {
            let value = oracle.get_witness_from_placeholder(placeholder, subindex, 0);
            let idx = variable.0 as usize;
            if idx >= self.values.len() {
                self.values.resize(idx + 1, F::ZERO);
            }
            self.values[idx] = value;
        }
    }
}

impl<F: PrimeField> WitnessTypeSet<F> for CSDebugWitnessEvaluator<F> {
    const CAN_BRANCH: bool = <ScalarWitnessTypeSet<F, true> as WitnessTypeSet<F>>::CAN_BRANCH;
    const MERGE_LOOKUP_AND_MULTIPLICITY_COUNT: bool = true;

    type Mask = <ScalarWitnessTypeSet<F, true> as WitnessTypeSet<F>>::Mask;
    type Field = <ScalarWitnessTypeSet<F, true> as WitnessTypeSet<F>>::Field;
    type I32 = <ScalarWitnessTypeSet<F, true> as WitnessTypeSet<F>>::I32;
    type U32 = <ScalarWitnessTypeSet<F, true> as WitnessTypeSet<F>>::U32;
    type U16 = <ScalarWitnessTypeSet<F, true> as WitnessTypeSet<F>>::U16;
    type U8 = <ScalarWitnessTypeSet<F, true> as WitnessTypeSet<F>>::U8;

    #[inline(always)]
    fn branch(mask: &Self::Mask) -> bool {
        *mask
    }
}

impl<F: PrimeField> WitnessPlacer<F> for CSDebugWitnessEvaluator<F> {
    fn record_resolver(&mut self, resolver: impl WitnessResolutionDescription<F, Self>) {
        resolver.evaluate(self);
    }

    fn get_oracle_field(&mut self, placeholder: Placeholder, subindex: usize) -> Self::Field {
        if let Some(oracle) = self.oracle.as_ref() {
            oracle.get_witness_from_placeholder(placeholder, subindex, 0)
        } else {
            F::ZERO
        }
    }

    fn get_oracle_u32(&mut self, placeholder: Placeholder) -> Self::U32 {
        if let Some(oracle) = self.oracle.as_ref() {
            oracle.get_u32_witness_from_placeholder(placeholder, 0)
        } else {
            0
        }
    }

    fn get_oracle_u16(&mut self, placeholder: Placeholder) -> Self::U16 {
        if let Some(oracle) = self.oracle.as_ref() {
            oracle.get_u16_witness_from_placeholder(placeholder, 0)
        } else {
            0
        }
    }

    fn get_oracle_u8(&mut self, placeholder: Placeholder) -> Self::U8 {
        if let Some(oracle) = self.oracle.as_ref() {
            oracle.get_u8_witness_from_placeholder(placeholder, 0)
        } else {
            0
        }
    }

    fn get_oracle_boolean(&mut self, placeholder: Placeholder) -> Self::Mask {
        if let Some(oracle) = self.oracle.as_ref() {
            oracle.get_boolean_witness_from_placeholder(placeholder, 0)
        } else {
            false
        }
    }

    #[track_caller]
    fn get_field(&mut self, variable: Variable) -> Self::Field {
        if variable.is_placeholder() {
            panic!("variable is placeholder");
        }
        let idx = variable.0 as usize;
        if idx >= self.values.len() {
            self.values.resize(idx + 1, F::ZERO);
        }
        self.values[idx]
    }

    #[inline(always)]
    fn get_boolean(&mut self, variable: Variable) -> Self::Mask {
        self.get_field(variable).as_boolean()
    }

    #[inline(always)]
    fn get_u16(&mut self, variable: Variable) -> Self::U16 {
        self.get_field(variable).as_u64_reduced() as u16
    }

    #[inline(always)]
    fn get_u8(&mut self, variable: Variable) -> Self::U8 {
        self.get_field(variable).as_u64_reduced() as u8
    }

    #[inline(always)]
    fn assign_mask(&mut self, variable: Variable, value: &Self::Mask) {
        if variable.is_placeholder() {
            panic!("variable is placeholder");
        }
        let idx = variable.0 as usize;
        if idx >= self.values.len() {
            self.values.resize(idx + 1, F::ZERO);
        }
        self.values[idx] = F::from_boolean(*value);
    }

    #[inline(always)]
    fn assign_field(&mut self, variable: Variable, value: &Self::Field) {
        if variable.is_placeholder() {
            panic!("variable is placeholder");
        }
        let idx = variable.0 as usize;
        if idx >= self.values.len() {
            self.values.resize(idx + 1, F::ZERO);
        }
        self.values[idx] = *value;
    }

    #[inline(always)]
    fn assign_u16(&mut self, variable: Variable, value: &Self::U16) {
        self.assign_field(variable, &F::from_u64_unchecked(*value as u64));
    }

    #[inline(always)]
    fn assign_u8(&mut self, variable: Variable, value: &Self::U8) {
        self.assign_field(variable, &F::from_u64_unchecked(*value as u64));
    }

    #[inline(always)]
    fn conditionally_assign_mask(
        &mut self,
        variable: Variable,
        mask: &Self::Mask,
        value: &Self::Mask,
    ) {
        if *mask {
            self.assign_mask(variable, value);
        }
    }

    #[inline(always)]
    fn conditionally_assign_field(
        &mut self,
        variable: Variable,
        mask: &Self::Mask,
        value: &Self::Field,
    ) {
        if *mask {
            self.assign_field(variable, value);
        }
    }

    #[inline(always)]
    fn conditionally_assign_u16(
        &mut self,
        variable: Variable,
        mask: &Self::Mask,
        value: &Self::U16,
    ) {
        if *mask {
            self.assign_u16(variable, value);
        }
    }

    #[inline(always)]
    fn conditionally_assign_u8(&mut self, variable: Variable, mask: &Self::Mask, value: &Self::U8) {
        if *mask {
            self.assign_u8(variable, value);
        }
    }

    #[inline(always)]
    fn lookup<const M: usize, const N: usize>(
        &mut self,
        inputs: &[Self::Field; M],
        table_id: &Self::U16,
    ) -> [Self::Field; N] {
        self.table_driver
            .lookup_values::<N>(inputs, *table_id as u32)
    }

    #[inline(always)]
    fn maybe_lookup<const M: usize, const N: usize>(
        &mut self,
        inputs: &[Self::Field; M],
        table_id: &Self::U16,
        mask: &Self::Mask,
    ) -> [Self::Field; N] {
        if *mask {
            self.lookup(inputs, table_id)
        } else {
            [F::ZERO; N]
        }
    }

    #[inline(always)]
    fn lookup_enforce<const M: usize>(&mut self, inputs: &[Self::Field; M], table_id: &Self::U16) {
        let _ = self
            .table_driver
            .enforce_values_and_get_absolute_index(inputs, *table_id as u32);
    }

    fn assume_assigned(&mut self, _variable: Variable) {
        // nothing
    }

    fn spec_decoder_relation(&mut self, pc: [Variable; 2], decoder_data: &DecoderData<F>) {
        let pc = self.get_u32_from_u16_parts(pc);
        let Some(table) = self.preprocessed_decoder_table.as_ref() else {
            panic!("Decoder table is not specified");
        };

        assert!(pc % 4 == 0);
        let idx = (pc / 4) as usize;
        let entry = table[idx];

        self.assign_u8(decoder_data.rs1_index, &entry.rs1_index);
        self.assign_u8(decoder_data.rs2_index, &entry.rs2_index);
        self.assign_u8(decoder_data.rd_index, &entry.rd_index);
        self.assign_mask(decoder_data.rd_is_zero, &entry.rd_is_zero);
        self.assign_u32_from_u16_parts(decoder_data.imm, &entry.imm);
        self.assign_u8(decoder_data.funct3, &entry.funct3);
        if let Some(funct7) = decoder_data.funct7 {
            self.assign_u8(funct7, &entry.funct7.unwrap());
        }
        assert!(entry.opcode_family_bits <= 1 << (F::CHAR_BITS - 1));
        self.assign_field(
            decoder_data.circuit_family_extra_mask,
            &F::from_u64_unchecked(entry.opcode_family_bits as u64),
        );
    }
}
