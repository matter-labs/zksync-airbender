use super::*;
use crate::definitions::sumcheck_kernel::*;
use crate::gkr::sumcheck::access_and_fold::ExtensionFieldPolyContinuingSource;
use crate::gkr::sumcheck::evaluation_kernels::BatchedGKRTermDescriptionConstants;

#[derive(Clone, Debug, Default)]
struct BatchedGKRDescriptionDraft<F: PrimeField, E: FieldExtension<F> + Field> {
    quadratic_part_base_by_base: BTreeMap<GKRAddress, BTreeMap<GKRAddress, E>>,
    quadratic_part_base_by_ext: BTreeMap<GKRAddress, BTreeMap<GKRAddress, E>>,
    quadratic_part_ext_by_ext: BTreeMap<GKRAddress, BTreeMap<GKRAddress, E>>,
    linear_part_base_by_everything: BTreeMap<GKRAddress, E>,
    linear_part_ext_by_everything: BTreeMap<GKRAddress, E>,
    outputs_in_base: BTreeMap<GKRAddress, E>,
    outputs_in_ext: BTreeMap<GKRAddress, E>,
    constant_term: E,
    _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRDescriptionDraft<F, E> {
    fn flatten(self) -> BatchedGKRDescription<F, E> {
        BatchedGKRDescription {
            quadratic_part_base_by_base: self
                .quadratic_part_base_by_base
                .into_iter()
                .map(|(k, v)| (k, v.into_iter().collect()))
                .collect(),
            quadratic_part_base_by_ext: self
                .quadratic_part_base_by_ext
                .into_iter()
                .map(|(k, v)| (k, v.into_iter().collect()))
                .collect(),
            quadratic_part_ext_by_ext: self
                .quadratic_part_ext_by_ext
                .into_iter()
                .map(|(k, v)| (k, v.into_iter().collect()))
                .collect(),
            linear_part_base_by_everything: self
                .linear_part_base_by_everything
                .into_iter()
                .collect(),
            linear_part_ext_by_everything: self.linear_part_ext_by_everything.into_iter().collect(),
            outputs_in_base: self.outputs_in_base.into_iter().collect(),
            outputs_in_ext: self.outputs_in_ext.into_iter().collect(),
            constant_term: self.constant_term,
            _marker: core::marker::PhantomData,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct BatchedGKRDescription<F: PrimeField, E: FieldExtension<F> + Field> {
    pub(crate) quadratic_part_base_by_base: Vec<(GKRAddress, Vec<(GKRAddress, E)>)>,
    pub(crate) quadratic_part_base_by_ext: Vec<(GKRAddress, Vec<(GKRAddress, E)>)>,
    pub(crate) quadratic_part_ext_by_ext: Vec<(GKRAddress, Vec<(GKRAddress, E)>)>,
    pub(crate) linear_part_base_by_everything: Vec<(GKRAddress, E)>,
    pub(crate) linear_part_ext_by_everything: Vec<(GKRAddress, E)>,
    pub(crate) outputs_in_base: Vec<(GKRAddress, E)>,
    pub(crate) outputs_in_ext: Vec<(GKRAddress, E)>,
    pub(crate) constant_term: E,
    pub(crate) _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> KernelCollector<F, E> {
    pub(crate) fn make_batched_description(
        &self,
        challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
        _layer: usize,
    ) -> BatchedGKRDescription<F, E> {
        let mut draft = BatchedGKRDescriptionDraft::<F, E>::default();
        for kernel in self.kernels.iter() {
            let terms = kernel.get_terms(challenge_constants);
            let challenges = kernel.batch_challenges();
            assert_eq!(
                terms.len(),
                challenges.len(),
                "number of challenges diverged for kernel {:?}",
                kernel
            );

            // use crate::gkr::prover::sumcheck_loop::kernel_collector::KernelVariant;
            // if let KernelVariant::MaxQuadratic(..) = kernel {
            //     dbg!(&terms);
            // }

            for (batch_challege, term) in challenges.iter().zip(terms.iter()) {
                for (a, other_terms) in term.quadratic_part_base_by_base.iter() {
                    for (b, c) in other_terms.iter() {
                        assert!(
                            b >= a,
                            "multiplication loop must be ordered, but `a` = {:?}, `b` = {:?}",
                            a,
                            b
                        );
                        let mut c = *c;
                        c.mul_assign(batch_challege);
                        let existing_coeff = draft
                            .quadratic_part_base_by_base
                            .entry(*a)
                            .or_default()
                            .entry(*b)
                            .or_insert(E::ZERO);
                        existing_coeff.add_assign(&c);
                    }
                }

                for (a, other_terms) in term.quadratic_part_base_by_ext.iter() {
                    for (b, c) in other_terms.iter() {
                        let mut c = *c;
                        c.mul_assign(batch_challege);
                        let existing_coeff = draft
                            .quadratic_part_base_by_ext
                            .entry(*a)
                            .or_default()
                            .entry(*b)
                            .or_insert(E::ZERO);
                        existing_coeff.add_assign(&c);
                    }
                }

                for (a, other_terms) in term.quadratic_part_ext_by_ext.iter() {
                    for (b, c) in other_terms.iter() {
                        assert!(
                            b >= a,
                            "multiplication loop must be ordered, but `a` = {:?}, `b` = {:?}",
                            a,
                            b
                        );
                        let mut c = *c;
                        c.mul_assign(batch_challege);
                        let existing_coeff = draft
                            .quadratic_part_ext_by_ext
                            .entry(*a)
                            .or_default()
                            .entry(*b)
                            .or_insert(E::ZERO);
                        existing_coeff.add_assign(&c);
                    }
                }

                for (b, c) in term.linear_part_base.iter() {
                    let mut c = *c;
                    c.mul_assign(batch_challege);
                    let existing_coeff = draft
                        .linear_part_base_by_everything
                        .entry(*b)
                        .or_insert(E::ZERO);
                    existing_coeff.add_assign(&c);
                }

                for (b, c) in term.linear_part_ext.iter() {
                    let mut c = *c;
                    c.mul_assign(batch_challege);
                    let existing_coeff = draft
                        .linear_part_ext_by_everything
                        .entry(*b)
                        .or_insert(E::ZERO);
                    existing_coeff.add_assign(&c);
                }

                if let Some(b) = term.output_in_base {
                    let mut c = E::ONE;
                    c.mul_assign(batch_challege);
                    let existing_coeff = draft.outputs_in_base.entry(b).or_insert(E::ZERO);
                    existing_coeff.add_assign(&c);
                }

                if let Some(b) = term.output_in_extension {
                    let mut c = E::ONE;
                    c.mul_assign(batch_challege);
                    let existing_coeff = draft.outputs_in_ext.entry(b).or_insert(E::ZERO);
                    existing_coeff.add_assign(&c);
                }

                let mut c = term.constant_term;
                c.mul_assign(batch_challege);
                draft.constant_term.add_assign(&c);
            }
        }

        draft.flatten()
    }
}

pub(crate) fn evaluate_batched_gkr_description<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const N: usize,
>(
    description: &BatchedGKRDescription<F, E>,
    storage: &mut GKRStorage<F, E>,
    step: usize,
    folding_challenges: &[E],
    accumulator: &mut [[E; 2]],
    total_sumcheck_rounds: usize,
    last_evaluations: &mut BTreeMap<GKRAddress, [E; N]>,
    worker: &Worker,
) {
    // println!("Evaluating {:?}", description);

    // This is column-wise computation. Can be much more efficient row-wise.

    // TODO: restructure to batch [(b, c)] and then multiply by a

    let work_size = accumulator.len();
    assert!(work_size.is_power_of_two());

    match step {
        0 => {
            for (a, other_terms) in description.quadratic_part_base_by_base.iter() {
                for (b, c) in other_terms {
                    let a_s = storage.get_base_field_initial_source(a);
                    let b_s = storage.get_base_field_initial_source(b);
                    evaluate_quadratic_term::<F, E, _, _, _, _, true, false>(
                        &a_s,
                        &b_s,
                        *c,
                        accumulator,
                        worker,
                    );
                }
            }
            for (a, other_terms) in description.quadratic_part_base_by_ext.iter() {
                for (b, c) in other_terms {
                    let a_s = storage.get_base_field_initial_source(a);
                    let b_s = storage.get_extension_field_initial_source(b);
                    evaluate_quadratic_term::<F, E, _, _, _, _, true, false>(
                        &a_s,
                        &b_s,
                        *c,
                        accumulator,
                        worker,
                    );
                }
            }
            for (a, other_terms) in description.quadratic_part_ext_by_ext.iter() {
                for (b, c) in other_terms {
                    let a_s = storage.get_extension_field_initial_source(a);
                    let b_s = storage.get_extension_field_initial_source(b);
                    evaluate_quadratic_term::<F, E, _, _, _, _, true, false>(
                        &a_s,
                        &b_s,
                        *c,
                        accumulator,
                        worker,
                    );
                }
            }
            for (a, c) in description.linear_part_base_by_everything.iter() {
                let a_s = storage.get_base_field_initial_source(a);
                evaluate_linear_term::<F, E, _, _, true, false>(&a_s, *c, accumulator, worker);
            }
            for (a, c) in description.linear_part_ext_by_everything.iter() {
                let a_s = storage.get_extension_field_initial_source(a);
                evaluate_linear_term::<F, E, _, _, true, false>(&a_s, *c, accumulator, worker);
            }
            for (a, c) in description.outputs_in_base.iter() {
                let a_s = storage.get_base_field_initial_source(a);
                add_output_term::<F, E, _, _>(&a_s, *c, accumulator, worker);
            }
            for (a, c) in description.outputs_in_ext.iter() {
                let a_s = storage.get_extension_field_initial_source(a);
                add_output_term::<F, E, _, _>(&a_s, *c, accumulator, worker);
            }
        }
        // for all other rounds we care bound constant term as we do not have outputs
        1 => {
            fill_constant_term::<_, _, false>(description.constant_term, accumulator, worker);

            for (a, other_terms) in description.quadratic_part_base_by_base.iter() {
                for (b, c) in other_terms {
                    let a_s = storage.make_base_source_for_round_1(*a, folding_challenges);
                    let b_s = storage.make_base_source_for_round_1(*b, folding_challenges);
                    evaluate_quadratic_term::<F, E, _, _, _, _, false, false>(
                        &a_s,
                        &b_s,
                        *c,
                        accumulator,
                        worker,
                    );
                }
            }
            for (a, other_terms) in description.quadratic_part_base_by_ext.iter() {
                for (b, c) in other_terms {
                    let a_s = storage.make_base_source_for_round_1(*a, folding_challenges);
                    let b_s =
                        storage.make_ext_source_for_rounds_1_and_beyond(*b, folding_challenges);
                    evaluate_quadratic_term::<F, E, _, _, _, _, false, false>(
                        &a_s,
                        &b_s,
                        *c,
                        accumulator,
                        worker,
                    );
                }
            }
            for (a, other_terms) in description.quadratic_part_ext_by_ext.iter() {
                for (b, c) in other_terms {
                    let a_s =
                        storage.make_ext_source_for_rounds_1_and_beyond(*a, folding_challenges);
                    let b_s =
                        storage.make_ext_source_for_rounds_1_and_beyond(*b, folding_challenges);
                    evaluate_quadratic_term::<F, E, _, _, _, _, false, false>(
                        &a_s,
                        &b_s,
                        *c,
                        accumulator,
                        worker,
                    );
                }
            }
            for (a, c) in description.linear_part_base_by_everything.iter() {
                let a_s = storage.make_base_source_for_round_1(*a, folding_challenges);
                evaluate_linear_term::<F, E, _, _, false, false>(&a_s, *c, accumulator, worker);
            }
            for (a, c) in description.linear_part_ext_by_everything.iter() {
                let a_s = storage.make_ext_source_for_rounds_1_and_beyond(*a, folding_challenges);
                evaluate_linear_term::<F, E, _, _, false, false>(&a_s, *c, accumulator, worker);
            }
        }
        2 => {
            fill_constant_term::<_, _, false>(description.constant_term, accumulator, worker);

            for (a, other_terms) in description.quadratic_part_base_by_base.iter() {
                for (b, c) in other_terms {
                    let a_s = storage.make_base_source_for_round_2(*a, folding_challenges);
                    let b_s = storage.make_base_source_for_round_2(*b, folding_challenges);
                    evaluate_quadratic_term::<F, E, _, _, _, _, false, false>(
                        &a_s,
                        &b_s,
                        *c,
                        accumulator,
                        worker,
                    );
                }
            }
            for (a, other_terms) in description.quadratic_part_base_by_ext.iter() {
                for (b, c) in other_terms {
                    let a_s = storage.make_base_source_for_round_2(*a, folding_challenges);
                    let b_s =
                        storage.make_ext_source_for_rounds_1_and_beyond(*b, folding_challenges);
                    evaluate_quadratic_term::<F, E, _, _, _, _, false, false>(
                        &a_s,
                        &b_s,
                        *c,
                        accumulator,
                        worker,
                    );
                }
            }
            for (a, other_terms) in description.quadratic_part_ext_by_ext.iter() {
                for (b, c) in other_terms {
                    let a_s =
                        storage.make_ext_source_for_rounds_1_and_beyond(*a, folding_challenges);
                    let b_s =
                        storage.make_ext_source_for_rounds_1_and_beyond(*b, folding_challenges);
                    evaluate_quadratic_term::<F, E, _, _, _, _, false, false>(
                        &a_s,
                        &b_s,
                        *c,
                        accumulator,
                        worker,
                    );
                }
            }
            for (a, c) in description.linear_part_base_by_everything.iter() {
                let a_s = storage.make_base_source_for_round_2(*a, folding_challenges);
                evaluate_linear_term::<F, E, _, _, false, false>(&a_s, *c, accumulator, worker);
            }
            for (a, c) in description.linear_part_ext_by_everything.iter() {
                let a_s = storage.make_ext_source_for_rounds_1_and_beyond(*a, folding_challenges);
                evaluate_linear_term::<F, E, _, _, false, false>(&a_s, *c, accumulator, worker);
            }
        }
        i if i + 1 == total_sumcheck_rounds => {
            assert!(i >= 3);
            // New last-round form: produce the univariate monomial (point 0 + point at
            // infinity = quadratic-only coeff) exactly like an internal round
            // (`EXPLICIT_FORM == false`), instead of the old explicit endpoint values
            // `[G(0), G(1)]`. `dump_last_evals` still folds every input poly down to its
            // line (`get_f0_only` routes through `get_f0_and_f1`, so both halves are
            // materialized) and records `last_evaluations` for the post-loop fixing of the
            // last coordinate.
            fill_constant_term::<_, _, false>(description.constant_term, accumulator, worker);

            for (a, other_terms) in description.quadratic_part_base_by_base.iter() {
                for (b, c) in other_terms {
                    let a_s =
                        storage.make_base_source_for_rounds_3_and_beyond(*a, folding_challenges);
                    let b_s =
                        storage.make_base_source_for_rounds_3_and_beyond(*b, folding_challenges);
                    evaluate_quadratic_term::<F, E, _, _, _, _, false, false>(
                        &a_s,
                        &b_s,
                        *c,
                        accumulator,
                        worker,
                    );

                    dump_last_evals(a, a_s, last_evaluations);
                    dump_last_evals(b, b_s, last_evaluations);
                }
            }
            for (a, other_terms) in description.quadratic_part_base_by_ext.iter() {
                for (b, c) in other_terms {
                    let a_s =
                        storage.make_base_source_for_rounds_3_and_beyond(*a, folding_challenges);
                    let b_s =
                        storage.make_ext_source_for_rounds_1_and_beyond(*b, folding_challenges);
                    evaluate_quadratic_term::<F, E, _, _, _, _, false, false>(
                        &a_s,
                        &b_s,
                        *c,
                        accumulator,
                        worker,
                    );

                    dump_last_evals(a, a_s, last_evaluations);
                    dump_last_evals(b, b_s, last_evaluations);
                }
            }
            for (a, other_terms) in description.quadratic_part_ext_by_ext.iter() {
                for (b, c) in other_terms {
                    let a_s =
                        storage.make_ext_source_for_rounds_1_and_beyond(*a, folding_challenges);
                    let b_s =
                        storage.make_ext_source_for_rounds_1_and_beyond(*b, folding_challenges);
                    evaluate_quadratic_term::<F, E, _, _, _, _, false, false>(
                        &a_s,
                        &b_s,
                        *c,
                        accumulator,
                        worker,
                    );

                    dump_last_evals(a, a_s, last_evaluations);
                    dump_last_evals(b, b_s, last_evaluations);
                }
            }
            for (a, c) in description.linear_part_base_by_everything.iter() {
                let a_s = storage.make_base_source_for_rounds_3_and_beyond(*a, folding_challenges);
                evaluate_linear_term::<F, E, _, _, false, false>(&a_s, *c, accumulator, worker);

                dump_last_evals(a, a_s, last_evaluations);
            }
            for (a, c) in description.linear_part_ext_by_everything.iter() {
                let a_s = storage.make_ext_source_for_rounds_1_and_beyond(*a, folding_challenges);
                evaluate_linear_term::<F, E, _, _, false, false>(&a_s, *c, accumulator, worker);

                dump_last_evals(a, a_s, last_evaluations);
            }
        }
        3.. => {
            fill_constant_term::<_, _, false>(description.constant_term, accumulator, worker);

            for (a, other_terms) in description.quadratic_part_base_by_base.iter() {
                for (b, c) in other_terms {
                    let a_s =
                        storage.make_base_source_for_rounds_3_and_beyond(*a, folding_challenges);
                    let b_s =
                        storage.make_base_source_for_rounds_3_and_beyond(*b, folding_challenges);
                    evaluate_quadratic_term::<F, E, _, _, _, _, false, false>(
                        &a_s,
                        &b_s,
                        *c,
                        accumulator,
                        worker,
                    );
                }
            }
            for (a, other_terms) in description.quadratic_part_base_by_ext.iter() {
                for (b, c) in other_terms {
                    let a_s =
                        storage.make_base_source_for_rounds_3_and_beyond(*a, folding_challenges);
                    let b_s =
                        storage.make_ext_source_for_rounds_1_and_beyond(*b, folding_challenges);
                    evaluate_quadratic_term::<F, E, _, _, _, _, false, false>(
                        &a_s,
                        &b_s,
                        *c,
                        accumulator,
                        worker,
                    );
                }
            }
            for (a, other_terms) in description.quadratic_part_ext_by_ext.iter() {
                for (b, c) in other_terms {
                    let a_s =
                        storage.make_ext_source_for_rounds_1_and_beyond(*a, folding_challenges);
                    let b_s =
                        storage.make_ext_source_for_rounds_1_and_beyond(*b, folding_challenges);
                    evaluate_quadratic_term::<F, E, _, _, _, _, false, false>(
                        &a_s,
                        &b_s,
                        *c,
                        accumulator,
                        worker,
                    );
                }
            }
            for (a, c) in description.linear_part_base_by_everything.iter() {
                let a_s = storage.make_base_source_for_rounds_3_and_beyond(*a, folding_challenges);
                evaluate_linear_term::<F, E, _, _, false, false>(&a_s, *c, accumulator, worker);
            }
            for (a, c) in description.linear_part_ext_by_everything.iter() {
                let a_s = storage.make_ext_source_for_rounds_1_and_beyond(*a, folding_challenges);
                evaluate_linear_term::<F, E, _, _, false, false>(&a_s, *c, accumulator, worker);
            }
        }
    }
}

fn evaluate_quadratic_term<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    RA: EvaluationRepresentation<F, E>,
    RB: EvaluationRepresentation<F, E>,
    SA: EvaluationFormStorage<F, E, RA>,
    SB: EvaluationFormStorage<F, E, RB>,
    const FIRST_ROUND: bool,
    const EXPLICIT_FORM: bool,
>(
    a_s: &SA,
    b_s: &SB,
    c: E,
    accumulator: &mut [[E; 2]],
    worker: &Worker,
) {
    use crate::gkr::prover::apply_row_wise;
    let work_size = accumulator.len();
    apply_row_wise::<F, _>(
        vec![],
        vec![accumulator],
        work_size,
        worker,
        |_, mut ext_dest, chunk_start, chunk_size| {
            assert_eq!(ext_dest.len(), 1);
            let accumulator = ext_dest.pop().unwrap();
            let a_ctx = a_s.get_collapse_context();
            let b_ctx = b_s.get_collapse_context();
            for index in 0..chunk_size {
                let absolute_index = chunk_start + index;
                if FIRST_ROUND {
                    // we do not need first half
                    debug_assert!(EXPLICIT_FORM == false);
                    let a1 = a_s.get_f1_minus_f0_only(absolute_index);
                    let b1 = b_s.get_f1_minus_f0_only(absolute_index);

                    let eval_1 = a1.mul_by_ext::<true>(&c, a_ctx);
                    let eval_1 = b1.mul_by_ext::<true>(&eval_1, b_ctx);

                    accumulator[index][1].add_assign(&eval_1);
                } else {
                    let [a0, a1] = a_s.get_two_points::<EXPLICIT_FORM>(absolute_index);
                    let [b0, b1] = b_s.get_two_points::<EXPLICIT_FORM>(absolute_index);
                    let eval_0 = a0.mul_by_ext::<true>(&c, a_ctx);
                    let eval_0 = b0.mul_by_ext::<true>(&eval_0, b_ctx);

                    let eval_1 = a1.mul_by_ext::<true>(&c, a_ctx);
                    let eval_1 = b1.mul_by_ext::<true>(&eval_1, b_ctx);

                    accumulator[index][0].add_assign(&eval_0);
                    accumulator[index][1].add_assign(&eval_1);
                }
            }
        },
    );
}

fn evaluate_linear_term<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    RA: EvaluationRepresentation<F, E>,
    SA: EvaluationFormStorage<F, E, RA>,
    const FIRST_ROUND: bool,
    const EXPLICIT_FORM: bool,
>(
    a_s: &SA,
    c: E,
    accumulator: &mut [[E; 2]],
    worker: &Worker,
) {
    if FIRST_ROUND {
        return;
    }

    use crate::gkr::prover::apply_row_wise;
    let work_size = accumulator.len();
    apply_row_wise::<F, _>(
        vec![],
        vec![accumulator],
        work_size,
        worker,
        |_, mut ext_dest, chunk_start, chunk_size| {
            assert_eq!(ext_dest.len(), 1);
            let accumulator = ext_dest.pop().unwrap();

            let a_ctx = a_s.get_collapse_context();
            for index in 0..chunk_size {
                let absolute_index = chunk_start + index;

                if FIRST_ROUND {
                    // we do not need first half that we get from outputs
                    debug_assert!(EXPLICIT_FORM == false);
                } else {
                    if EXPLICIT_FORM {
                        let [a0, a1] = a_s.get_two_points::<EXPLICIT_FORM>(absolute_index);

                        let eval_0 = a0.mul_by_ext::<true>(&c, a_ctx);

                        let eval_1 = a1.mul_by_ext::<true>(&c, a_ctx);

                        accumulator[index][0].add_assign(&eval_0);
                        accumulator[index][1].add_assign(&eval_1);
                    } else {
                        // only half
                        let a0 = a_s.get_f0_only(absolute_index);

                        let eval_0 = a0.mul_by_ext::<true>(&c, a_ctx);

                        accumulator[index][0].add_assign(&eval_0);
                    }
                }
            }
        },
    );
}

fn add_output_term<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    RA: EvaluationRepresentation<F, E>,
    SA: EvaluationFormStorage<F, E, RA>,
>(
    a_s: &SA,
    c: E,
    accumulator: &mut [[E; 2]],
    worker: &Worker,
) {
    use crate::gkr::prover::apply_row_wise;
    let work_size = accumulator.len();
    apply_row_wise::<F, _>(
        vec![],
        vec![accumulator],
        work_size,
        worker,
        |_, mut ext_dest, chunk_start, chunk_size| {
            assert_eq!(ext_dest.len(), 1);
            let accumulator = ext_dest.pop().unwrap();

            let a_ctx = a_s.get_collapse_context();
            for index in 0..chunk_size {
                let absolute_index = chunk_start + index;

                let a0 = a_s.get_f0_only(absolute_index);

                let eval_0 = a0.mul_by_ext::<true>(&c, a_ctx);

                accumulator[index][0].add_assign(&eval_0);
            }
        },
    );
}

fn fill_constant_term<F: PrimeField, E: FieldExtension<F> + Field, const EXPLICIT_FORM: bool>(
    c: E,
    accumulator: &mut [[E; 2]],
    worker: &Worker,
) {
    use crate::gkr::prover::apply_row_wise;
    let work_size = accumulator.len();
    apply_row_wise::<F, _>(
        vec![],
        vec![accumulator],
        work_size,
        worker,
        |_, mut ext_dest, _chunk_start, chunk_size| {
            assert_eq!(ext_dest.len(), 1);
            let accumulator = ext_dest.pop().unwrap();
            for index in 0..chunk_size {
                accumulator[index][0] = c;
                if EXPLICIT_FORM {
                    accumulator[index][1] = c;
                }
            }
        },
    );
}

fn dump_last_evals<F: PrimeField, E: FieldExtension<F> + Field, const N: usize>(
    input: &GKRAddress,
    source: ExtensionFieldPolyContinuingSource<F, E>,
    last_evaluations: &mut BTreeMap<GKRAddress, [E; N]>,
) {
    // println!("Producing final evals for {:?}", input);

    if let Some(existing_evals) = last_evaluations.get(input).copied() {
        let current_values = source.current_values();
        assert_eq!(current_values.len(), N);
        assert_eq!(existing_evals, current_values);
    } else {
        let current_values = source.current_values();
        assert_eq!(current_values.len(), N);
        // let [f0, f1] = self.extension_field_inputs[idx].get_f0_and_f1(0);
        // println!("Inserting evaluations for {:?}", input);
        last_evaluations.insert(*input, current_values.try_into().unwrap());
    }
}
