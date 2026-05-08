use std::collections::BTreeMap;

use crate::gkr::{prover::WhirSchedule, whir::proximity_testing_modes::ProximityTestingMode};

pub mod example_configs;

#[derive(Clone, Debug)]
pub struct ProverConfig {
    pub lde_factor: usize,
    pub cap_size: usize,
    pub base_oracles_values_per_leaf: usize,
    pub lookup_challenges_pow_bits: u32,
    // we do not expect any challenges for sumcheck, as it's soundness
    // error is very small
    pub sumcheck_explicit_output_size_log_2: usize,
    pub batched_proximity_check_challenge_pow_bits: u32,
    pub whir_schedule: WhirSchedule,
}

impl WhirSchedule {
    pub fn current_cost(&self, trace_len_log_2: usize, cost_model: &impl CostModel) -> usize {
        let mut total_cost = 0;
        let cap_depth_cut = self.cap_size.trailing_zeros() as usize;
        let mut whir_sumcheck_terms = 0;

        {
            // base oracle queries
            let depth =
                trace_len_log_2 + (self.base_lde_factor.trailing_zeros() as usize) - cap_depth_cut;
            let num_queries = self.whir_queries_schedule[0];
            whir_sumcheck_terms += num_queries;
            let cost = cost_model.single_merkle_tree_depth_cost() * depth * num_queries;
            total_cost += cost;
        }

        let mut poly_size = trace_len_log_2 - self.whir_steps_schedule[0];

        if self.whir_steps_lde_factors.len() > 0 {
            for i in 0..self.whir_steps_lde_factors.len() {
                let num_queries = self.whir_queries_schedule[i + 1];
                whir_sumcheck_terms += num_queries;
                let rate = self.whir_steps_lde_factors[i].trailing_zeros();
                if poly_size + (rate as usize) < cap_depth_cut {
                    return usize::MAX;
                }
                let depth = poly_size + (rate as usize) - cap_depth_cut;
                let cost = cost_model.single_merkle_tree_depth_cost() * depth * num_queries;
                total_cost = total_cost.saturating_add(cost);
                // and folding
                let fold_by = self.whir_steps_schedule[i + 1];
                let cost = num_queries
                    .saturating_mul(cost_model.whir_leaf_hashing_and_folding_cost(fold_by as u32));
                total_cost = total_cost.saturating_add(cost);
                poly_size -= fold_by as usize;
            }
        }
        // final sumcheck
        let cost = cost_model.whir_sumcheck_terms_cost(poly_size) * whir_sumcheck_terms;
        total_cost = total_cost.saturating_add(cost);

        total_cost
    }
}

// NOTE: consider adding PoW cost
pub trait CostModel: 'static + Send + Sync {
    fn single_merkle_tree_depth_cost(&self) -> usize;
    fn whir_leaf_hashing_and_folding_cost(&self, folding_rate: u32) -> usize;
    fn whir_sumcheck_terms_cost(&self, final_degree_log_2: usize) -> usize;
}

pub struct BlakeHashBabyBearExt4CostModel;

impl CostModel for BlakeHashBabyBearExt4CostModel {
    fn single_merkle_tree_depth_cost(&self) -> usize {
        128
    }
    fn whir_leaf_hashing_and_folding_cost(&self, folding_rate: u32) -> usize {
        match folding_rate {
            0 => {
                unreachable!()
            }
            rate @ 1..=4 => 128 + (1 << rate) * 32,
            rate @ 5 => 128 * 2 + (1 << rate) * 32,
            _ => usize::MAX,
        }
    }
    fn whir_sumcheck_terms_cost(&self, final_degree_log_2: usize) -> usize {
        128 * (1 << final_degree_log_2)
    }
}

pub fn compute_best_prover_config_guess(
    trace_len_log_2: usize,
    lde_factor: usize,
    cap_size: usize,
    base_oracles_values_per_leaf: usize,
    lookup_challenges_pow_bits: u32, // we use these as inputs for now
    sumcheck_explicit_output_size_log_2: usize,
    batched_proximity_check_challenge_pow_bits: u32,
    first_round_pow_bits: u32,
    other_rounds_pow_bits: u32,
    min_pow_bits: u32,
    max_lde_factor: usize,
    max_lde_size_log_2: usize,
    whir_target_security_bits: u32,
    max_whir_explicit_output_size_log_2: usize,
    proximity_testing_mode: &impl ProximityTestingMode,
    cost_model: &impl CostModel,
) -> ProverConfig {
    assert!(lde_factor.is_power_of_two());
    assert!(cap_size.is_power_of_two());
    assert!(base_oracles_values_per_leaf.is_power_of_two());
    assert_eq!(
        base_oracles_values_per_leaf, 2,
        "placing 2 values per poly into base oracle leafs is considered optimal for now"
    );

    // NOTE: we do not implement any complex WHIR parameters search strategy, but try to keep all WHIR commits to be
    // roughly the same complexity.

    let mut whir_schedule = WhirSchedule {
        base_lde_factor: lde_factor,
        cap_size,
        whir_steps_schedule: vec![1], // in all our circuits base oracles are relatively large, and packing multiple leafs
        // in them is not obviously beneficial. So one can quickly fold by 2 and move from individual proximity checks
        // to batched one, and then try to using `1 << whir_average_folding_rate_log_2` elements per leaf
        whir_pow_schedule: vec![first_round_pow_bits],
        whir_steps_lde_factors: vec![],
        whir_queries_schedule: vec![],
    };

    let base_rate = lde_factor.trailing_zeros();
    {
        let proximity_testing_bits = whir_target_security_bits - first_round_pow_bits;
        let num_queries = proximity_testing_mode
            .num_queries_for_rate_and_bits_of_security(proximity_testing_bits, base_rate);
        whir_schedule
            .whir_queries_schedule
            .push(num_queries as usize);
    }

    let mut candidates = BTreeMap::new();

    assert!(max_lde_size_log_2 >= trace_len_log_2 + base_rate as usize);
    whir_folding_step(
        &mut candidates,
        trace_len_log_2,
        max_lde_size_log_2,
        other_rounds_pow_bits,
        min_pow_bits,
        max_lde_factor.trailing_zeros() as usize,
        whir_target_security_bits,
        max_whir_explicit_output_size_log_2,
        proximity_testing_mode,
        cost_model,
        &whir_schedule,
    );

    dbg!(&candidates);

    todo!();

    // ProverConfig {
    //     lde_factor,
    //     cap_size,
    //     base_oracles_values_per_leaf,
    //     lookup_challenges_pow_bits,
    //     sumcheck_explicit_output_size_log_2,
    //     batched_proximity_check_challenge_pow_bits,
    //     whir_schedule,
    // }
}

fn whir_folding_step(
    candidates: &mut BTreeMap<usize, WhirSchedule>,
    trace_len_log_2: usize,
    max_lde_size_log_2: usize,
    max_pow_bits: u32,
    min_pow_bits: u32,
    min_rate_log_2: usize,
    whir_target_security_bits: u32,
    max_whir_explicit_output_size_log_2: usize,
    proximity_testing_mode: &impl ProximityTestingMode,
    cost_model: &impl CostModel,
    path: &WhirSchedule,
) {
    // trim candidates

    // TODO: make it better logic, not just lowest 10, but a cost range
    if let Some((&min_cost, _)) = candidates.iter().next() {
        let max_cost = (min_cost * 110) / 100;
        candidates.retain(|cost, _v| *cost <= max_cost);
    }

    assert!(path.total_poly_size_reduction() <= trace_len_log_2);

    let whir_poly_size_log_2 = trace_len_log_2 - path.total_poly_size_reduction();

    if whir_poly_size_log_2 == 0 {
        return;
    }

    // assert!(whir_poly_size_log_2 > 0);
    if whir_poly_size_log_2 <= max_whir_explicit_output_size_log_2 {
        let total_cost = path.current_cost(trace_len_log_2, cost_model);
        let min_cost = candidates
            .iter()
            .next()
            .map(|(k, _v)| *k)
            .unwrap_or(usize::MAX);
        if total_cost < min_cost {
            println!("Inserting {:?} with the cost {}", path, total_cost);
            candidates.insert(total_cost, path.clone());
        }
    }

    if whir_poly_size_log_2 > 1 {
        // we can try to fold more, but we pay for it by queries and LDE
        for fold_by in (1..whir_poly_size_log_2).rev() {
            if fold_by > 5 {
                continue;
            }
            if fold_by >= whir_poly_size_log_2 {
                continue;
            }
            let bound = max_lde_size_log_2 - whir_poly_size_log_2;
            for rate in (1..=bound).rev() {
                let mut pow_bits = max_pow_bits;
                let proximity_testing_bits = whir_target_security_bits - pow_bits;
                let min_queries = proximity_testing_mode
                    .num_queries_for_rate_and_bits_of_security(proximity_testing_bits, rate as u32);

                let mut pow_is_free = true;
                for bits in (min_pow_bits..pow_bits).rev() {
                    let proximity_testing_bits = whir_target_security_bits - pow_bits;
                    let queries = proximity_testing_mode.num_queries_for_rate_and_bits_of_security(
                        proximity_testing_bits,
                        rate as u32,
                    );
                    if queries == min_queries {
                        pow_bits = bits;
                    } else {
                        pow_is_free = false;
                        break;
                    }
                }
                let mut rate_to_use = rate;
                if pow_is_free {
                    // we can try to reduce the rate for this round
                    for better_rate in 1..rate {
                        let proximity_testing_bits = whir_target_security_bits - min_pow_bits;
                        let queries = proximity_testing_mode
                            .num_queries_for_rate_and_bits_of_security(
                                proximity_testing_bits,
                                better_rate as u32,
                            );
                        if queries == min_queries {
                            rate_to_use = better_rate;
                        } else {
                            break;
                        }
                    }
                }
                let current_rate = path
                    .whir_steps_lde_factors
                    .last()
                    .copied()
                    .unwrap_or(path.base_lde_factor.trailing_zeros() as usize);
                if current_rate + whir_poly_size_log_2 < path.cap_size.trailing_zeros() as usize {
                    continue;
                }

                let mut new_path = path.clone();
                new_path.whir_pow_schedule.push(pow_bits);
                new_path.whir_queries_schedule.push(min_queries as usize);
                new_path.whir_steps_schedule.push(fold_by);
                new_path.whir_steps_lde_factors.push(1usize << rate_to_use);

                whir_folding_step(
                    candidates,
                    trace_len_log_2,
                    max_lde_size_log_2,
                    max_pow_bits,
                    min_pow_bits,
                    min_rate_log_2,
                    whir_target_security_bits,
                    max_whir_explicit_output_size_log_2,
                    proximity_testing_mode,
                    cost_model,
                    &new_path,
                );
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{definitions::*, gkr::whir::proximity_testing_modes::PessimisticConjectureMode};

    use super::*;

    #[test]
    fn test_try_compute_some_config() {
        let prover_config = compute_best_prover_config_guess(
            20,
            DEFAULT_LDE_FACTOR,
            DEFAULT_CAP_SIZE,
            2,
            0,
            DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
            0,
            28,
            24,
            // 20,
            0,
            1 << 22,
            27,
            // 100,
            80,
            DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
            &PessimisticConjectureMode,
            &BlakeHashBabyBearExt4CostModel,
        );
        dbg!(prover_config);
    }
}
