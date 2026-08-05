use super::*;

pub(crate) mod batched;
pub(crate) mod boolean_constraint;
pub(crate) mod fixed_kernels;
pub(crate) mod layer_oracle;
pub(crate) mod logup_variants;
pub(crate) mod quadratic_constraint_with_constant;
pub(crate) mod quadratic_constraint_with_diverse_witness;
pub(crate) mod simple_product;
pub(crate) mod sumcheck_loop;
mod utils;

/// A real (deserialized) but empty `GKRCircuitArtifact` for micro tests whose
/// sumcheck path never reads the artifact (the non-evaluator route only
/// forwards it). Replaces the former `MaybeUninit::uninit().assume_init_ref()`
/// placeholders, which manufactured an invalid `&GKRCircuitArtifact` (UB even
/// when never dereferenced). Every `F`-valued collection is empty, so this
/// works for any field.
pub(crate) fn empty_circuit_artifact<F: ::field::PrimeField + serde::de::DeserializeOwned>(
) -> cs::gkr_compiler::GKRCircuitArtifact<F> {
    serde_json::from_value(serde_json::json!({
        "trace_len": 0,
        "table_offsets": [],
        "total_tables_size": 0,
        "offset_for_decoder_table": 0,
        "has_decoder_lookup": false,
        "layers": [],
        "global_output_map": {},
        "memory_layout": {
            "ram_access_sets": [],
            "machine_state": null,
            "delegation_state": null,
            "decoder_input": null,
            "indirect_access_variable_offsets": [],
            "teardown_sets": [],
            "total_width": 0,
            "inits_and_teardowns_word_bits": null,
        },
        "witness_layout": {
            "multiplicities_columns_for_range_check_16": {"start": 0, "end": 0},
            "multiplicities_columns_for_timestamp_range_check": {"start": 0, "end": 0},
            "multiplicities_columns_for_generic_lookup": {"start": 0, "end": 0},
            "total_width": 0,
        },
        "scratch_space_size": 0,
        "num_generic_lookups": 0,
        "placement_data": {},
        "generic_lookup_tables_width": 0,
        "decode_table_columns_mask": [],
        "tables_ids_in_generic_lookups": false,
        "degree_2_constraints": [],
        "degree_1_constraints": [],
        "structured_statements": [],
        "generic_lookups": [],
        "range_check_16_lookup_expressions": [],
        "timestamp_range_check_lookup_expressions": [],
        "variable_names": {},
        "scratch_space_mapping": [],
        "scratch_space_mapping_rev": {},
        "aux_layout_data": {"shuffle_ram_timestamp_comparison_aux_vars": []},
        "_marker": null,
    }))
    .expect("empty GKRCircuitArtifact must deserialize")
}
