use super::*;
use crate::definitions::Variable;
use crate::gkr_compiler::graph::GKRGraph;
use crate::gkr_compiler::inits_and_teardowns::create_inits_and_teardowns_set;
use crate::gkr_compiler::memory_like_grand_product::GrandProductAccumulationStep;
use crate::gkr_compiler::utils::add_compiler_defined_base_layer_variable;

pub(crate) fn allocate_inline_inits_and_teardowns_sets(
    graph: &mut GKRGraph,
    num_inits_and_teardowns_pairs: usize,
    num_variables: &mut u64,
    all_variables_to_place: &mut BTreeSet<Variable>,
    layers_mapping: &mut HashMap<Variable, usize>,
    variable_names: &mut HashMap<Variable, String>,
) -> Vec<([GKRAddress; 2], [GKRAddress; 2])> {
    assert!(
        num_inits_and_teardowns_pairs >= 1,
        "inline i/t requires at least 1 pair (= 2 sets); use compile_family_circuit \
         without inline-i/t for num=0"
    );
    assert!(
        num_inits_and_teardowns_pairs.is_power_of_two(),
        "inline i/t pair count must be a power of two; pairwise aggregation needs balanced halves"
    );
    let num_sets = num_inits_and_teardowns_pairs * 2;
    let mut teardown_sets = Vec::with_capacity(num_sets);

    for set_idx in 0..num_sets {
        let values: [Variable; 2] = std::array::from_fn(|i| {
            let var = add_compiler_defined_base_layer_variable(
                num_variables,
                all_variables_to_place,
                layers_mapping,
            );
            variable_names.insert(
                var,
                format!("inline i/t set {}: teardown value[{}]", set_idx, i),
            );
            var
        });
        let values = graph.layout_memory_subtree_multiple_variables(
            values,
            all_variables_to_place,
            layers_mapping,
        );

        let timestamps: [Variable; 2] = std::array::from_fn(|i| {
            let var = add_compiler_defined_base_layer_variable(
                num_variables,
                all_variables_to_place,
                layers_mapping,
            );
            variable_names.insert(
                var,
                format!("inline i/t set {}: teardown timestamp[{}]", set_idx, i),
            );
            var
        });
        let timestamps = graph.layout_memory_subtree_multiple_variables(
            timestamps,
            all_variables_to_place,
            layers_mapping,
        );

        teardown_sets.push((timestamps, values));
    }

    teardown_sets
}

/// Build the inline i/t grand product. Returns the (read, write) output pair for the
/// `OutputType::InitsAndTeardownsProduct` channel. Mirrors the structure of
/// `compile_inits_and_teardowns_circuit` but operates on pre-allocated per-row teardown
/// columns and is integrated into the family circuit's graph rather than a standalone one.
pub(crate) fn build_inline_inits_and_teardowns_grand_product(
    graph: &mut GKRGraph,
    teardown_sets: &[([GKRAddress; 2], [GKRAddress; 2])],
) -> (
    (GKRAddress, NoFieldGKRRelation),
    (GKRAddress, NoFieldGKRRelation),
) {
    assert!(teardown_sets.len() >= 2);
    assert_eq!(teardown_sets.len() % 2, 0);

    let mut read_set: Vec<(GKRAddress, NoFieldGKRRelation)> = vec![];
    let mut write_set: Vec<(GKRAddress, NoFieldGKRRelation)> = vec![];

    let mut set_idx = 0;
    for [lhs, rhs] in teardown_sets.as_chunks::<2>().0.iter() {
        let (read_el, write_el) =
            create_inits_and_teardowns_set(graph, [set_idx, set_idx + 1], [*lhs, *rhs]);
        set_idx += 2;
        read_set.push(read_el);
        write_set.push(write_el);
    }

    // Pairwise aggregate when we have multiple pairs of sets. For a single pair
    // (num_inits_and_teardowns_pairs = 1, num_sets = 2) this loop is skipped and we return the single
    // (read, write) pair from create_inits_and_teardowns_set directly.
    let mut expected_output_layer = 1;
    while read_set.len() > 1 {
        expected_output_layer += 1;
        assert_eq!(read_set.len(), write_set.len());

        let mut next_read: Vec<(GKRAddress, NoFieldGKRRelation)> = vec![];
        let mut next_write: Vec<(GKRAddress, NoFieldGKRRelation)> = vec![];

        for (src, dst, is_write) in [
            (&read_set, &mut next_read, false),
            (&write_set, &mut next_write, true),
        ] {
            assert_eq!(src.len() % 2, 0);
            for [a, b] in src.as_chunks::<2>().0.iter() {
                let node = GrandProductAccumulationStep::AggregationPair {
                    lhs: a.0,
                    rhs: b.0,
                    is_write,
                };
                let t = node.add_at_layer(graph, expected_output_layer);
                dst.push(t);
            }
        }

        read_set = next_read;
        write_set = next_write;
    }

    assert_eq!(read_set.len(), 1);
    assert_eq!(write_set.len(), 1);

    (read_set.pop().unwrap(), write_set.pop().unwrap())
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use crate::cs::circuit_impl::BasicAssembly;
    use crate::cs::circuit_trait::Circuit;
    use crate::definitions::OutputType;
    use crate::gkr_circuits::add_sub_family::{
        add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr,
        add_sub_lui_auipc_mop_table_addition_fn,
    };
    use crate::gkr_compiler::GKRCompiler;

    #[test]
    fn compile_family_circuit_with_inline_inits_and_teardowns_smoke() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let mut cs = BasicAssembly::<BabyBearField>::new();
        add_sub_lui_auipc_mop_table_addition_fn(&mut cs);
        add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr(&mut cs);
        let (cs_output, _) = cs.finalize();

        let compiler = GKRCompiler::<BabyBearField>::default();
        let artifact = compiler.compile_family_circuit_with_inline_inits_and_teardowns(
            cs_output,
            common_constants::ROM_WORD_SIZE,
            1,
            22,
            true,
        );

        assert!(artifact
            .global_output_map
            .contains_key(&OutputType::PermutationProduct));
        assert!(artifact
            .global_output_map
            .contains_key(&OutputType::InitsAndTeardownsProduct));
        assert_eq!(
            artifact.global_output_map[&OutputType::PermutationProduct].len(),
            2
        );
        assert_eq!(
            artifact.global_output_map[&OutputType::InitsAndTeardownsProduct].len(),
            2
        );
    }
}
