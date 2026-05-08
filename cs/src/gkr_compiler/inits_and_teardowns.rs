use super::*;
use crate::gkr_compiler::memory_like_grand_product::GrandProductAccumulationStep;
use crate::{definitions::VirtualSetupPoly, gkr_compiler::graph::GKRGraph, tables::TableDriver};

pub fn compile_inits_and_teardowns_circuit<F: PrimeField, const WORD_BITS: u32>(
    num_sets: usize,
    trace_len_log2: usize,
) -> GKRCircuitArtifact<F> {
    assert!(
        num_sets.is_power_of_two(),
        "only powers of two are supported for simplicity"
    );
    // NOTE: we have no range checks of any kind or generic lookups

    let num_bytes_per_set: u64 = (1u64 << trace_len_log2) << WORD_BITS;
    assert!(num_bytes_per_set * (num_sets as u64) <= 1u64 << 32);
    println!("Compiling inits and teardowns circuit for {} sets, 2^{} bytes each, {} bytes init in total", num_sets, num_bytes_per_set.trailing_zeros(), num_bytes_per_set * (num_sets as u64));

    let mut variable_names = HashMap::new();

    let mut teardown_sets = Vec::with_capacity(num_sets);
    let mut num_variables = 0u64;
    let mut all_variables_to_place = BTreeSet::new();
    let mut layers_mapping = HashMap::new();

    let mut graph = GKRGraph::new(0, false);
    for set_idx in 0..num_sets {
        let values: [Variable; 2] = std::array::from_fn(|i| {
            let var = add_compiler_defined_base_layer_variable(
                &mut num_variables,
                &mut all_variables_to_place,
                &mut layers_mapping,
            );
            variable_names.insert(
                var,
                format!("Inits and teardowns set {}: teardown value[{}]", set_idx, i),
            );
            var
        });
        let values = graph.layout_memory_subtree_multiple_variables(
            values,
            &mut all_variables_to_place,
            &mut layers_mapping,
        );
        let timestamps: [Variable; 2] = std::array::from_fn(|i| {
            let var = add_compiler_defined_base_layer_variable(
                &mut num_variables,
                &mut all_variables_to_place,
                &mut layers_mapping,
            );
            variable_names.insert(
                var,
                format!(
                    "Inits and teardowns set {}: teardown timestamp[{}]",
                    set_idx, i
                ),
            );
            var
        });
        let timestamps = graph.layout_memory_subtree_multiple_variables(
            timestamps,
            &mut all_variables_to_place,
            &mut layers_mapping,
        );
        teardown_sets.push((timestamps, values));
    }

    let mut read_set = vec![];
    let mut write_set = vec![];

    let mut set_idx = 0;
    for [lhs, rhs] in teardown_sets.as_chunks::<2>().0.iter() {
        let (read_set_el, write_set_el) =
            create_inits_and_teardowns_set(&mut graph, [set_idx, set_idx + 1], [*lhs, *rhs]);

        set_idx += 2;

        read_set.push(read_set_el);
        write_set.push(write_set_el);
    }

    // manually place grand_products
    let mut expected_output_layer = 1;
    while read_set.len() > 1 {
        expected_output_layer += 1;
        assert_eq!(read_set.len(), write_set.len());

        let mut next_read_set = vec![];
        let mut next_write_set = vec![];

        for (src, dst, is_write) in [
            (&read_set, &mut next_read_set, false),
            (&write_set, &mut next_write_set, true),
        ] {
            assert_eq!(src.len() % 2, 0);
            for [a, b] in src.as_chunks::<2>().0.iter() {
                let node = GrandProductAccumulationStep::AggregationPair {
                    lhs: a.0,
                    rhs: b.0,
                    is_write,
                };
                let t = node.add_at_layer(&mut graph, expected_output_layer);
                dst.push(t);
            }
        }

        read_set = next_read_set;
        write_set = next_write_set;
    }

    assert_eq!(read_set.len(), 1);
    assert_eq!(write_set.len(), 1);

    let (layers, global_output_map) =
        graph.layout_layers([read_set[0].clone(), write_set[0].clone()], BTreeMap::new());

    let mut placement_data = BTreeMap::new();
    placement_data.extend(graph.base_layer_memory.iter().map(|(k, v)| (*k, *v)));
    placement_data.extend(graph.base_layer_witness.iter().map(|(k, v)| (*k, *v)));
    placement_data.extend(graph.intermediate_layers.iter().map(|(k, v)| (*k, *v)));

    GKRCircuitArtifact {
        trace_len: 1 << trace_len_log2,
        table_offsets: TableDriver::<F>::new()
            .table_starts_offsets()
            .iter()
            .map(|el| *el as u32)
            .collect(),
        total_tables_size: 0,
        offset_for_decoder_table: 0,
        has_decoder_lookup: false,
        layers,
        global_output_map,
        memory_layout: GKRMemoryLayout {
            ram_access_sets: Vec::new(),
            machine_state: None,
            delegation_state: None,
            decoder_input: None,
            indirect_access_variable_offsets: Vec::new(),
            teardown_sets,
            total_width: graph.base_layer_memory.len(),
        },
        witness_layout: GKRWitnessLayout {
            multiplicities_columns_for_range_check_16: 0..0,
            multiplicities_columns_for_timestamp_range_check: 0..0,
            multiplicities_columns_for_generic_lookup: 0..0,
            total_width: 0,
        },
        scratch_space_size: 0,
        num_generic_lookups: 0,
        placement_data,
        generic_lookup_tables_width: 0,
        decode_table_columns_mask: Vec::new(),
        tables_ids_in_generic_lookups: false,
        degree_2_constraints: Vec::new(),
        degree_1_constraints: Vec::new(),
        generic_lookups: Vec::new(),
        range_check_16_lookup_expressions: Vec::new(),
        timestamp_range_check_lookup_expressions: Vec::new(),
        variable_names: BTreeMap::from_iter(variable_names.into_iter()),
        scratch_space_mapping: BTreeMap::new(),
        scratch_space_mapping_rev: BTreeMap::new(),
        aux_layout_data: GKRAuxLayoutData {
            shuffle_ram_timestamp_comparison_aux_vars: Vec::new(),
        },
        _marker: core::marker::PhantomData,
    }
}

fn create_inits_and_teardowns_set(
    graph: &mut impl GraphHolder,
    set_idxes: [usize; 2],
    allocated_teardown_ts_and_values: [([GKRAddress; 2], [GKRAddress; 2]); 2],
) -> (
    (GKRAddress, NoFieldGKRRelation),
    (GKRAddress, NoFieldGKRRelation),
) {
    let output = [(); 2].map(|_| graph.add_intermediate_variable_at_layer(1));
    // inits and teardowns are almost the same, so we just use enum to indicate
    // what is an timestamp + value

    let inits = NoFieldGKRRelation::InitsOrTeardownsInitialPair {
        timestamp_and_value: InitsOrTeardownsTimestampAndValue::Init,
        setup: [
            GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
            GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
        ],
        output: output[0],
        set_idxes,
    };
    graph.add_enforced_relation(inits.clone(), 1);

    let [(lhs_timestamp, lhs_value), (rhs_timestamp, rhs_value)] = allocated_teardown_ts_and_values;

    let teardowns = NoFieldGKRRelation::InitsOrTeardownsInitialPair {
        timestamp_and_value: InitsOrTeardownsTimestampAndValue::Teardown {
            lhs_timestamp: lhs_timestamp.map(|el| {
                let GKRAddress::BaseLayerMemory(el) = el else {
                    unreachable!()
                };

                el
            }),
            lhs_value: lhs_value.map(|el| {
                let GKRAddress::BaseLayerMemory(el) = el else {
                    unreachable!()
                };

                el
            }),
            rhs_timestamp: rhs_timestamp.map(|el| {
                let GKRAddress::BaseLayerMemory(el) = el else {
                    unreachable!()
                };

                el
            }),
            rhs_value: rhs_value.map(|el| {
                let GKRAddress::BaseLayerMemory(el) = el else {
                    unreachable!()
                };

                el
            }),
        },
        setup: [
            GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
            GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
        ],
        output: output[1],
        set_idxes,
    };
    graph.add_enforced_relation(teardowns.clone(), 1);

    // read set, write set
    ((output[1], inits), (output[0], teardowns))
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use crate::utils::serialize_to_file;

    #[test]
    fn compile_inits_and_teardowns_into_no_caches_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let gkr_compiled = compile_inits_and_teardowns_circuit::<BabyBearField, 2>(16, 24);

        serialize_to_file(
            &gkr_compiled,
            "compiled_circuits/inits_and_teardowns_layout_no_caches_gkr.json",
        );
    }
}
