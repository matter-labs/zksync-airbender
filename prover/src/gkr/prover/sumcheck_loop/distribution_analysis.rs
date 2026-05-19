use std::{cmp::Ordering, collections::BTreeSet, ops::Range};

use super::*;
use cs::{definitions::NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES, gkr_compiler::GKRCircuitArtifact};

impl<F: PrimeField, E: FieldExtension<F> + Field> KernelCollector<F, E> {
    pub(crate) fn analyze_terms(&self) {
        let challenge_constants = BatchedGKRTermDescriptionConstants {
            external_challenges: GKRExternalChallenges {
                permutation_argument_linearization_challenges: [E::ONE;
                    NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES],
                permutation_argument_additive_part: E::ONE,
                _marker: core::marker::PhantomData,
            },
            lookup_challenges_additive_part: E::ONE,
            lookup_challenges_multiplicative_part: E::ONE,
            _marker: core::marker::PhantomData,
        };
        let batched_description = self.make_batched_description(&challenge_constants, self.layer);

        #[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
        struct Occurances {
            quad_terms_with_base: BTreeSet<GKRAddress>,
            quad_terms_with_ext: BTreeSet<GKRAddress>,
            linear_terms: bool,
        }

        let mut occurances_of_base = BTreeMap::<_, Occurances>::new();
        let mut occurances_of_ext = BTreeMap::<_, Occurances>::new();
        for (a, other) in batched_description.quadratic_part_base_by_base.iter() {
            let e = occurances_of_base.entry(*a).or_default();
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                e.quad_terms_with_base.insert(*b);
            }
            // symmetric
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                let e = occurances_of_base.entry(*b).or_default();
                e.quad_terms_with_base.insert(*a);
            }
        }
        for (a, other) in batched_description.quadratic_part_base_by_ext.iter() {
            let e = occurances_of_base.entry(*a).or_default();
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                e.quad_terms_with_ext.insert(*b);
            }
            // symmetric
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                let e = occurances_of_ext.entry(*b).or_default();
                e.quad_terms_with_base.insert(*a);
            }
        }
        for (a, other) in batched_description.quadratic_part_base_by_ext.iter() {
            let e = occurances_of_ext.entry(*a).or_default();
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                e.quad_terms_with_ext.insert(*b);
            }
            // symmetric
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                let e = occurances_of_ext.entry(*b).or_default();
                e.quad_terms_with_ext.insert(*a);
            }
        }
        for (a, _) in batched_description.linear_part_base_by_everything.iter() {
            let e = occurances_of_base.entry(*a).or_default();
            e.linear_terms = true;
        }
        for (a, _) in batched_description.linear_part_ext_by_everything.iter() {
            let e = occurances_of_ext.entry(*a).or_default();
            e.linear_terms = true;
        }

        for (a, o) in occurances_of_base.iter() {
            let with_base = o.quad_terms_with_base.len();
            let with_ext = o.quad_terms_with_ext.len();
            let in_linear = o.linear_terms as usize;
            println!("Base variable {:?} happens in {} quad terms with base, {} quad terms with ext and {} linear terms", a, with_base, with_ext, in_linear);
        }

        for (a, o) in occurances_of_ext.iter() {
            let with_base = o.quad_terms_with_base.len();
            let with_ext = o.quad_terms_with_ext.len();
            let in_linear = o.linear_terms as usize;
            println!("Ext variable {:?} happens in {} quad terms with base, {} quad terms with ext and {} linear terms", a, with_base, with_ext, in_linear);
        }
    }
}

pub fn liveness_analysis<F: PrimeField>(
    circuit: &GKRCircuitArtifact<F>,
    layer_idx: usize,
) {
    let layer = &circuit.layers[layer_idx];
    if layer.gates_with_external_connections.len() > 0 {
        panic!("Last layer is usually not interesting");
    }

    let mut occurance_matrix: BTreeMap<usize, BTreeSet<GKRAddress>> = BTreeMap::new();
    let mut inv_occurance_matrix: BTreeMap<GKRAddress, BTreeSet<usize>> = BTreeMap::new();

    for (idx, gate) in layer.gates.iter().enumerate() {
        let mut set = BTreeSet::new();
        gate.enforced_relation.dump_inputs(&mut set);
        for el in set.iter() {
            inv_occurance_matrix.entry(*el).or_insert(BTreeSet::new()).insert(idx);
        }

        occurance_matrix.insert(idx, set);
    }

    let mut matrix = vec![];
    for (a, inputs) in occurance_matrix.iter() {
        for (b, other_inputs) in occurance_matrix.iter() {
            if *a >= *b {
                continue;
            }
            let common = inputs.intersection(&other_inputs);
            let num_common = common.count();
            matrix.push((*a, *b, num_common));
        }
    }

    matrix.sort_by(|a, b| a.2.cmp(&b.2).reverse());

    for (a, b, common_els) in matrix.iter() {
        if *common_els == 0 {
            continue;
        }
        println!("{} / {}: {} common inputs", a, b, common_els);
    }

    // In general we need to reduce the scope of initial search branches, so let's do it by ones
    // that have at least N inputs

    let max_reuses = matrix.iter().map(|(_, _, t)| *t).max().unwrap_or(1);
    if max_reuses == 0 {
        println!("Order is not important, there are no reuses");
        return;
    }
    let min_common_inputs = 4;
    let cutoff = std::cmp::min(max_reuses, min_common_inputs);

    dbg!(cutoff);

    let mut starting_points = BTreeSet::new();
    for (a, b, common_els) in matrix.iter() {
        if *common_els >= cutoff {
            starting_points.insert(*a);
            starting_points.insert(*b);
        }
    }
    assert!(starting_points.len() > 0);

    // now we should do greedy search (speed is not an issue) to find a sequence of gate evaluations
    // that would use as much cache as possible. For that we will want liveness analysis, and we will use a simple one
    // for a start - basically assuming that value is "life" until there are no other expressions that may use it

    let mut reports = BTreeMap::new();
    let all_gates: BTreeSet<usize> = (0..layer.gates.len()).collect();

    println!("Starting points are {:?}", &starting_points);

    for gate_idx in starting_points.into_iter().skip(10) {
        println!("Starting from {}", gate_idx);

            let mut remaining_gates = all_gates.clone();
        remaining_gates.remove(&gate_idx);

        let mut alive_set = BTreeMap::new();
        let mut t = BTreeSet::new();
        layer.gates[gate_idx].enforced_relation.dump_inputs(&mut t);
        for t in t.into_iter() {
            alive_set.insert(t, 0);
        }

        alive_set.retain(|k, _| {
            let occurance_in_gates = inv_occurance_matrix.get(k).expect("exists in occurance matrix");
            let mut still_alive = false;
            for gate_idx in remaining_gates.iter() {
                if occurance_in_gates.contains(gate_idx) {
                    still_alive = true;
                    break;
                }
            }
            still_alive
        });

        search_step::<8>(
            layer,
            0,
            vec![gate_idx],
            alive_set,
            remaining_gates,
            0,
            &mut reports,
            &inv_occurance_matrix,
        );
    }

    dbg!(&reports);
}

fn search_step<const MAX_CANDIDATES: usize>(
    layer: &GKRLayerDescription,
    epoch: usize,
    chain: Vec<usize>, // chain of gates
    all_live_variables: BTreeMap<GKRAddress, usize>,
    remaining_gates: BTreeSet<usize>,
    max_cache_size: usize,
    reports: &mut BTreeMap<Vec<usize>, usize>,
    // reports: &mut BTreeMap<Vec<usize>, BTreeMap<GKRAddress, Range<usize>>>,
    // mut stats: BTreeMap<GKRAddress, Range<usize>>,
    // occurange_matrix: &BTreeMap<usize, BTreeSet<GKRAddress>>,
    inv_occurance_matrix: &BTreeMap<GKRAddress, BTreeSet<usize>>,
) {
    let epoch = epoch + 1;

    let worst_case = reports.values().max().copied().unwrap_or(usize::MAX);
    if max_cache_size >= worst_case {
        // do not try to update
        return;
    }

    if remaining_gates.is_empty() {
        let num_alive = all_live_variables.len();
        let final_report = std::cmp::max(num_alive, max_cache_size);
        if final_report < worst_case {
            println!("Inserting chain {:?} with {} max live variables", &chain, final_report);
            reports.insert(chain, final_report);
            if reports.len() > 10 {
                reports.retain(|_, v| {
                    *v < worst_case
                });
            }
        }

        return;
    }

    // // cleanup dead variables
    // let mut remaining_live_variables = BTreeMap::new();
    // for (variable, life_at_epoch) in all_live_variables.into_iter() {
    //     let mut alive = false;
    //     for &gate_idx in remaining_gates.iter() {
    //         let mut set = BTreeSet::new();
    //         layer.gates[gate_idx].enforced_relation.dump_inputs(&mut set);
    //         if set.contains(&variable) {
    //             alive = true;
    //             break;
    //         }
    //     }
    //     if alive {
    //         remaining_live_variables.insert(variable, life_at_epoch);
    //     }
    //     //  else {
    //     //     stats.insert(variable, life_at_epoch..epoch);
    //     // }
    // }

    // try to find a gates with max overlaps with max alive variables
    let mut reuse_stats = BTreeMap::new();
    for &gate_idx in remaining_gates.iter() {
        let mut num_reuses = 0;
        let mut set = BTreeSet::new();
        layer.gates[gate_idx].enforced_relation.dump_inputs(&mut set);
        for var in set.into_iter() {
            if all_live_variables.contains_key(&var) {
                num_reuses += 1usize;
            }
        }
        if num_reuses > 0 {
            reuse_stats.insert(gate_idx, num_reuses);
        }
    }
    assert!(reuse_stats.is_empty() == false, "disjoint set if we do {:?} chain", &chain); // we do not consider disjoint sequences yet

    let mut candidates_via_reuse: Vec<_> = reuse_stats.into_iter().collect();
    candidates_via_reuse.sort_by(|(a_gate, a_reuses), (b_gate, b_reuses)| {
        let t = a_reuses.cmp(b_reuses).reverse();
        if t == Ordering::Equal {
            a_gate.cmp(b_gate)
        } else {
            t
        }
    });
    candidates_via_reuse.truncate(MAX_CANDIDATES);

    // we also consider some gates that immediately reduce the number of alive variables in the most aggressive manner
    let mut elimination_stats = BTreeMap::new();
    for &gate_idx in remaining_gates.iter() {
        assert!(remaining_gates.contains(&gate_idx), "gates set is {:?}, but gate {} is missing", &remaining_gates, gate_idx);

        let mut alive_set = all_live_variables.clone();
        let mut t = BTreeSet::new();
        layer.gates[gate_idx].enforced_relation.dump_inputs(&mut t);
        for el in t.into_iter() {
            alive_set.insert(el, epoch);
        }
        // maybe some variables die after we do this gate
        alive_set.retain(|k, _| {
            let occurance_in_gates = inv_occurance_matrix.get(k).expect("exists in occurance matrix");
            let mut still_alive = false;
            for other_gate_idx in remaining_gates.iter() {
                if gate_idx == *other_gate_idx {
                    continue;
                }
                if occurance_in_gates.contains(other_gate_idx) {
                    still_alive = true;
                    break;
                }
            }
            still_alive
        });
        let num_alive = alive_set.len();
        if num_alive < all_live_variables.len() {
            // only consider paths that immediatelly eliminate live set
            elimination_stats.insert(gate_idx, num_alive);
        }
    }

    let mut candidates_from_elimination: Vec<_> = elimination_stats.into_iter().collect();
    candidates_from_elimination.sort_by(|(a_gate, a_left_alive), (b_gate, b_left_alive)| {
        let t = a_left_alive.cmp(b_left_alive);
        if t == Ordering::Equal {
            a_gate.cmp(b_gate)
        } else {
            t
        }
    });
    candidates_from_elimination.truncate(MAX_CANDIDATES);

    let mut all_candidates = BTreeSet::new();
    all_candidates.extend(candidates_via_reuse.into_iter().map(|(a, _)| a));
    all_candidates.extend(candidates_from_elimination.into_iter().map(|(a, _)| a));

    // now we descend
    for gate_idx in all_candidates.into_iter() {
        assert!(remaining_gates.contains(&gate_idx), "gates set is {:?}, but gate {} is missing", &remaining_gates, gate_idx);

        let mut new_chain = chain.clone();
        new_chain.push(gate_idx);

        let mut new_remaining_gates = remaining_gates.clone();
        new_remaining_gates.remove(&gate_idx);
        assert!(new_remaining_gates.len() < remaining_gates.len());

        let mut alive_set = all_live_variables.clone();
        let mut t = BTreeSet::new();
        layer.gates[gate_idx].enforced_relation.dump_inputs(&mut t);
        for el in t.into_iter() {
            alive_set.insert(el, epoch);
        }
        // maybe some variables die after we do this gate
        alive_set.retain(|k, _| {
            let occurance_in_gates = inv_occurance_matrix.get(k).expect("exists in occurance matrix");
            let mut still_alive = false;
            for gate_idx in new_remaining_gates.iter() {
                if occurance_in_gates.contains(gate_idx) {
                    still_alive = true;
                    break;
                }
            }
            still_alive
        });
        let num_alive = alive_set.len();
        let new_max_cache_size = std::cmp::max(num_alive, max_cache_size);
        if new_max_cache_size >= worst_case {
            continue;
        }

        search_step::<MAX_CANDIDATES>(
            layer,
            epoch,
            new_chain,
            alive_set,
            new_remaining_gates,
            new_max_cache_size,
            reports,
            inv_occurance_matrix,
        );
    }
}

#[cfg(test)]
mod test {
    use super::*;

    const USE_GKR_WITH_CACHES: bool = true;
    use crate::tests::gkr::deserialize_from_file;
    use cs::gkr_compiler::GKRCircuitArtifact;
    use field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};

    type F = BabyBearField;
    type E = BabyBearExt4;

    #[test]
    fn analyze_terms_in_circuit() {
        let circuit: GKRCircuitArtifact<BabyBearField> = if USE_GKR_WITH_CACHES {
            deserialize_from_file(
                "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json",
            )
        } else {
            deserialize_from_file(
                "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
            )
        };

        let circuit: GKRCircuitArtifact<BabyBearField> = 
            deserialize_from_file(
                "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
            );

        let layer_idx = 0;
        let layer = &circuit.layers[layer_idx];

        liveness_analysis(&circuit, layer_idx);
        panic!();

        let collector =
            KernelCollector::<F, E>::from_layer(layer, layer_idx, E::ONE, E::ONE, E::ONE, &[], 0);

        collector.analyze_terms();
    }
}
