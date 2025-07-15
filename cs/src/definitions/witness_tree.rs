use super::*;

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct WitnessSubtree<F: PrimeField> {
    // we use separate multiplicities columns for tables of width 1 for an optimization
    // in the prover
    pub multiplicities_columns_for_range_check_16: ColumnSet<1>,
    pub multiplicities_columns_for_timestamp_range_check: ColumnSet<1>,
    pub multiplicities_columns_for_decoder_in_executor_families: ColumnSet<1>,
    pub multiplicities_columns_for_generic_lookup: ColumnSet<1>,
    pub range_check_8_columns: ColumnSet<1>,
    pub range_check_16_columns: ColumnSet<1>,
    // #[serde(bound(
    //     deserialize = "LookupSetDescription<F, COMMON_TABLE_WIDTH>: serde::Deserialize<'de>"
    // ))]
    // #[serde(bound(serialize = "LookupSetDescription<F, COMMON_TABLE_WIDTH>: serde::Serialize"))]
    pub width_3_lookups: Vec<LookupSetDescription<F, COMMON_TABLE_WIDTH>>,
    pub range_check_16_lookup_expressions: Vec<LookupExpression<F>>,
    pub timestamp_range_check_lookup_expressions: Vec<LookupExpression<F>>,
    pub offset_for_special_shuffle_ram_timestamps_range_check_expressions: usize,
    pub boolean_vars_columns_range: ColumnSet<1>,
    pub scratch_space_columns_range: ColumnSet<1>,
    pub total_width: usize,
}

impl<F: PrimeField> WitnessSubtree<F> {
    pub fn as_compiled<'a>(
        &'a self,
        buffer: &'a mut Vec<VerifierCompiledLookupSetDescription<'a, F, COMMON_TABLE_WIDTH>>,
        single_lookup_expressions_buffer: &'a mut Vec<VerifierCompiledLookupExpression<'a, F>>,
    ) -> CompiledWitnessSubtree<'a, F> {
        assert!(buffer.is_empty());
        for el in self.width_3_lookups.iter() {
            buffer.push(el.as_compiled());
        }

        for el in self.range_check_16_lookup_expressions.iter() {
            single_lookup_expressions_buffer.push(el.as_compiled());
        }
        let offset = single_lookup_expressions_buffer.len();
        for el in self.timestamp_range_check_lookup_expressions.iter() {
            single_lookup_expressions_buffer.push(el.as_compiled());
        }

        let range_check_16_lookup_expressions = &single_lookup_expressions_buffer[..offset];
        let timestamp_range_check_lookup_expressions = &single_lookup_expressions_buffer[offset..];

        CompiledWitnessSubtree {
            multiplicities_columns_for_range_check_16: self
                .multiplicities_columns_for_range_check_16,
            multiplicities_columns_for_timestamp_range_check: self
                .multiplicities_columns_for_timestamp_range_check,
            multiplicities_columns_for_generic_lookup: self
                .multiplicities_columns_for_generic_lookup,
            range_check_16_columns: self.range_check_16_columns,
            width_3_lookups: &buffer[..],
            range_check_16_lookup_expressions,
            timestamp_range_check_lookup_expressions,
            offset_for_special_shuffle_ram_timestamps_range_check_expressions: self
                .offset_for_special_shuffle_ram_timestamps_range_check_expressions,
            boolean_vars_columns_range: self.boolean_vars_columns_range,
            scratch_space_columns_range: self.scratch_space_columns_range,
            total_width: self.total_width,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct CompiledWitnessSubtree<'a, F: PrimeField> {
    pub multiplicities_columns_for_range_check_16: ColumnSet<1>,
    pub multiplicities_columns_for_timestamp_range_check: ColumnSet<1>,
    pub multiplicities_columns_for_generic_lookup: ColumnSet<1>,
    pub range_check_16_columns: ColumnSet<1>,
    pub width_3_lookups: &'a [VerifierCompiledLookupSetDescription<'a, F, COMMON_TABLE_WIDTH>],
    pub range_check_16_lookup_expressions: &'a [VerifierCompiledLookupExpression<'a, F>],
    pub timestamp_range_check_lookup_expressions: &'a [VerifierCompiledLookupExpression<'a, F>],
    pub offset_for_special_shuffle_ram_timestamps_range_check_expressions: usize,
    pub boolean_vars_columns_range: ColumnSet<1>,
    pub scratch_space_columns_range: ColumnSet<1>,
    pub total_width: usize,
}
