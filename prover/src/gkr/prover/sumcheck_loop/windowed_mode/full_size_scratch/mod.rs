use std::collections::BTreeSet;

use super::*;
use crate::gkr::prover::sumcheck_loop::batch_evaluation::BatchedGKRDescription;

pub mod extension_only_round;
pub mod initial_round;
pub mod transition_round;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvaluationStep {
    QuadraticBaseByBase {
        scratch_idx_a: u8,
        scratch_idx_b: u8,
        coeff_idx: u32,
    },
    QuadraticBaseByExt {
        scratch_idx_base: u8,
        scratch_idx_ext: u8,
        coeff_idx: u32,
    },
    QuadraticExtByExt {
        scratch_idx_a: u8,
        scratch_idx_b: u8,
        coeff_idx: u32,
    },
    LinearWithBase {
        scratch_idx: u8,
        coeff_idx: u32,
    },
    LinearWithExt {
        scratch_idx: u8,
        coeff_idx: u32,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FoldedEvaluationStep {
    Quadratic {
        scratch_idx_a: u8,
        scratch_idx_b: u8,
        coeff_idx: u32,
    },
    Linear {
        scratch_idx: u8,
        coeff_idx: u32,
    },
}

#[derive(Clone, Debug)]
pub struct BatchEvaluationCompactDescription<F: PrimeField, E: FieldExtension<F> + Field> {
    initial_evaluation_steps: Vec<EvaluationStep>,
    folded_evaluation_steps: Vec<FoldedEvaluationStep>,
    constants: Vec<E>,
    total_additive_constant: E,
    base_read_with_interpolation: Vec<bool>,
    ext_read_with_interpolation: Vec<bool>,
    _marker: core::marker::PhantomData<F>,
}

pub fn produce_descriptions_from_batched_description<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    description: &BatchedGKRDescription<F, E>,
) -> (
    BatchEvaluationCompactDescription<F, E>,
    Vec<GKRAddress>,
    Vec<GKRAddress>,
) {
    let mut all_base_sources = BTreeSet::new();
    let mut all_ext_sources = BTreeSet::new();
    let mut base_sources_in_quadratic_evals = BTreeSet::new();
    let mut ext_sources_in_quadratic_evals = BTreeSet::new();

    for (a, other) in description.quadratic_part_base_by_base.iter() {
        all_base_sources.insert(*a);
        base_sources_in_quadratic_evals.insert(*a);
        for (b, _) in other.iter() {
            all_base_sources.insert(*b);
            base_sources_in_quadratic_evals.insert(*b);
        }
    }

    for (a, other) in description.quadratic_part_base_by_ext.iter() {
        all_base_sources.insert(*a);
        base_sources_in_quadratic_evals.insert(*a);
        for (b, _) in other.iter() {
            all_ext_sources.insert(*b);
            ext_sources_in_quadratic_evals.insert(*b);
        }
    }

    for (a, other) in description.quadratic_part_ext_by_ext.iter() {
        all_ext_sources.insert(*a);
        ext_sources_in_quadratic_evals.insert(*a);
        for (b, _) in other.iter() {
            all_ext_sources.insert(*b);
            ext_sources_in_quadratic_evals.insert(*b);
        }
    }

    for (a, _) in description.linear_part_base_by_everything.iter() {
        all_base_sources.insert(*a);
    }
    for (a, _) in description.linear_part_ext_by_everything.iter() {
        all_ext_sources.insert(*a);
    }

    let base_sources: Vec<_> = all_base_sources.iter().copied().collect();
    let ext_sources: Vec<_> = all_ext_sources.iter().copied().collect();

    assert!(base_sources.len() + ext_sources.len() < 256); // so we do not overflow u8

    let ext_offset_for_folded_stages = base_sources.len();

    let mut base_mapping = BTreeMap::new();
    for src in all_base_sources.iter() {
        let idx = base_sources
            .iter()
            .position(|el| *el == *src)
            .expect("position");
        base_mapping.insert(*src, idx);
    }
    let mut ext_mapping = BTreeMap::new();
    for src in all_ext_sources.iter() {
        let idx = ext_sources
            .iter()
            .position(|el| *el == *src)
            .expect("position");
        ext_mapping.insert(*src, idx);
    }

    // now we can try to use different optimization strategies how to transform a flat relation into evaluation FSM, but
    // we will try to do a naive one with merging linear and quadratic via single read, and first evaluating longest chains for products

    let mut constants = vec![];

    let base_read_with_interpolation: Vec<_> = base_sources
        .iter()
        .map(|el| base_sources_in_quadratic_evals.contains(el))
        .collect();
    let ext_read_with_interpolation: Vec<_> = ext_sources
        .iter()
        .map(|el| ext_sources_in_quadratic_evals.contains(el))
        .collect();

    let mut linear_term_issued_for_base = BTreeSet::new();
    let mut linear_term_issued_for_ext = BTreeSet::new();

    let mut initial_evaluation_steps = vec![];
    let mut folded_evaluation_steps = vec![];

    let mut add_linear_for_base =
        |addr: GKRAddress,
         constants: &mut Vec<E>,
         initial_evaluation_steps: &mut Vec<EvaluationStep>,
         folded_evaluation_steps: &mut Vec<FoldedEvaluationStep>| {
            if linear_term_issued_for_base.contains(&addr) == false {
                let idx = base_mapping.get(&addr).copied().expect("index");
                for (el, coeff) in description.linear_part_base_by_everything.iter() {
                    if *el != addr {
                        continue;
                    }
                    let coeff_idx = constants.len();
                    constants.push(*coeff);
                    initial_evaluation_steps.push(EvaluationStep::LinearWithBase {
                        scratch_idx: idx as u8,
                        coeff_idx: coeff_idx as u32,
                    });
                    folded_evaluation_steps.push(FoldedEvaluationStep::Linear {
                        scratch_idx: idx as u8,
                        coeff_idx: coeff_idx as u32,
                    });
                    linear_term_issued_for_base.insert(addr);
                }
            }
        };

    let mut add_linear_for_ext =
        |addr: GKRAddress,
         constants: &mut Vec<E>,
         initial_evaluation_steps: &mut Vec<EvaluationStep>,
         folded_evaluation_steps: &mut Vec<FoldedEvaluationStep>| {
            if linear_term_issued_for_ext.contains(&addr) == false {
                let idx = ext_mapping.get(&addr).copied().expect("index");
                for (el, coeff) in description.linear_part_ext_by_everything.iter() {
                    if *el != addr {
                        continue;
                    }
                    let coeff_idx = constants.len();
                    constants.push(*coeff);
                    initial_evaluation_steps.push(EvaluationStep::LinearWithExt {
                        scratch_idx: idx as u8,
                        coeff_idx: coeff_idx as u32,
                    });
                    folded_evaluation_steps.push(FoldedEvaluationStep::Linear {
                        scratch_idx: (idx + ext_offset_for_folded_stages) as u8,
                        coeff_idx: coeff_idx as u32,
                    });
                    linear_term_issued_for_ext.insert(addr);
                }
            }
        };

    for (a, other) in description.quadratic_part_base_by_base.iter() {
        let a_idx = base_mapping.get(a).copied().expect("index");
        for (b, coeff) in other.iter() {
            let b_idx = base_mapping.get(b).copied().expect("index");
            let coeff_idx = constants.len();
            constants.push(*coeff);

            initial_evaluation_steps.push(EvaluationStep::QuadraticBaseByBase {
                scratch_idx_a: a_idx as u8,
                scratch_idx_b: b_idx as u8,
                coeff_idx: coeff_idx as u32,
            });
            folded_evaluation_steps.push(FoldedEvaluationStep::Quadratic {
                scratch_idx_a: a_idx as u8,
                scratch_idx_b: b_idx as u8,
                coeff_idx: coeff_idx as u32,
            });

            (add_linear_for_base)(
                *b,
                &mut constants,
                &mut initial_evaluation_steps,
                &mut folded_evaluation_steps,
            );
        }

        (add_linear_for_base)(
            *a,
            &mut constants,
            &mut initial_evaluation_steps,
            &mut folded_evaluation_steps,
        );
    }

    for (a, other) in description.quadratic_part_base_by_ext.iter() {
        let a_idx = base_mapping.get(a).copied().expect("index");
        for (b, coeff) in other.iter() {
            let b_idx = ext_mapping.get(b).copied().expect("index");
            let coeff_idx = constants.len();
            constants.push(*coeff);

            initial_evaluation_steps.push(EvaluationStep::QuadraticBaseByExt {
                scratch_idx_base: a_idx as u8,
                scratch_idx_ext: b_idx as u8,
                coeff_idx: coeff_idx as u32,
            });
            folded_evaluation_steps.push(FoldedEvaluationStep::Quadratic {
                scratch_idx_a: a_idx as u8,
                scratch_idx_b: (b_idx + ext_offset_for_folded_stages) as u8,
                coeff_idx: coeff_idx as u32,
            });

            (add_linear_for_ext)(
                *b,
                &mut constants,
                &mut initial_evaluation_steps,
                &mut folded_evaluation_steps,
            );
        }

        (add_linear_for_base)(
            *a,
            &mut constants,
            &mut initial_evaluation_steps,
            &mut folded_evaluation_steps,
        );
    }

    for (a, other) in description.quadratic_part_ext_by_ext.iter() {
        let a_idx = ext_mapping.get(a).copied().expect("index");
        for (b, coeff) in other.iter() {
            let b_idx = ext_mapping.get(b).copied().expect("index");
            let coeff_idx = constants.len();
            constants.push(*coeff);

            initial_evaluation_steps.push(EvaluationStep::QuadraticExtByExt {
                scratch_idx_a: a_idx as u8,
                scratch_idx_b: b_idx as u8,
                coeff_idx: coeff_idx as u32,
            });
            folded_evaluation_steps.push(FoldedEvaluationStep::Quadratic {
                scratch_idx_a: a_idx as u8,
                scratch_idx_b: (b_idx + ext_offset_for_folded_stages) as u8,
                coeff_idx: coeff_idx as u32,
            });

            (add_linear_for_ext)(
                *b,
                &mut constants,
                &mut initial_evaluation_steps,
                &mut folded_evaluation_steps,
            );
        }

        (add_linear_for_ext)(
            *a,
            &mut constants,
            &mut initial_evaluation_steps,
            &mut folded_evaluation_steps,
        );
    }

    for (a, coeff) in description.linear_part_base_by_everything.iter() {
        if linear_term_issued_for_base.contains(a) {
            continue;
        }

        let idx = base_mapping.get(a).copied().expect("index");
        let coeff_idx = constants.len();
        constants.push(*coeff);

        initial_evaluation_steps.push(EvaluationStep::LinearWithBase {
            scratch_idx: idx as u8,
            coeff_idx: coeff_idx as u32,
        });
        folded_evaluation_steps.push(FoldedEvaluationStep::Linear {
            scratch_idx: idx as u8,
            coeff_idx: coeff_idx as u32,
        });
    }

    for (a, coeff) in description.linear_part_ext_by_everything.iter() {
        if linear_term_issued_for_ext.contains(a) {
            continue;
        }

        let idx = ext_mapping.get(a).copied().expect("index");
        let coeff_idx = constants.len();
        constants.push(*coeff);

        initial_evaluation_steps.push(EvaluationStep::LinearWithExt {
            scratch_idx: idx as u8,
            coeff_idx: coeff_idx as u32,
        });
        folded_evaluation_steps.push(FoldedEvaluationStep::Linear {
            scratch_idx: (idx + ext_offset_for_folded_stages) as u8,
            coeff_idx: coeff_idx as u32,
        });
    }

    let descr = BatchEvaluationCompactDescription {
        initial_evaluation_steps,
        folded_evaluation_steps,
        constants,
        total_additive_constant: description.constant_term,
        base_read_with_interpolation,
        ext_read_with_interpolation,
        _marker: core::marker::PhantomData,
    };

    (descr, base_sources, ext_sources)
}
