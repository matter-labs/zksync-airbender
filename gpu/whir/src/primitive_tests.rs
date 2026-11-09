//! Shared primitive parity cases; each field supplies its production storage and launches.
use crate::upstream::Field;
use gpu_prover_context::ProverContext;

pub(crate) trait PrimitiveField: Field {
    type State;
    fn sample(seed: u32) -> Self;
    fn state(log_n: u32, context: &ProverContext) -> Self::State;
    fn set_forms(
        state: &mut Self::State,
        monomials: &[Self],
        evals: &[Self],
        eq: &[Self],
        context: &ProverContext,
    );
    fn read_forms(
        state: &Self::State,
        context: &ProverContext,
    ) -> (Vec<Self>, Vec<Self>, Vec<Self>);
    fn build_eq(state: &mut Self::State, point: &[Self], context: &ProverContext) -> Vec<Self>;
    fn fold(state: &mut Self::State, challenge: Self, context: &ProverContext);
    fn three_point(state: &mut Self::State, context: &ProverContext) -> [Self; 3];
    fn monomial_eval(state: &mut Self::State, point: Self, context: &ProverContext) -> Self;
}

pub(crate) fn eq_case<F: PrimitiveField>(log_n: u32, context: &ProverContext) {
    let point: Vec<_> = (0..log_n).map(|i| F::sample(1 + 10 * i)).collect();
    let mut state = F::state(log_n, context);
    let actual = F::build_eq(&mut state, &point, context);
    let mut expected = Vec::<F>::with_capacity(1 << log_n);
    prover::gkr::sumcheck::eq_poly::fill_eq_table_lsb_first_uninit(
        &point,
        &mut expected.spare_capacity_mut()[..1 << log_n],
        &worker::Worker::new_with_num_threads(4),
    );
    unsafe {
        expected.set_len(1 << log_n);
    }
    assert_eq!(actual, expected);
}

fn fold_values<F: Field>(values: &[F], challenge: F, evaluations: bool) -> Vec<F> {
    values
        .as_chunks::<2>()
        .0
        .iter()
        .map(|[a, b]| {
            let mut term = *b;
            if evaluations {
                term.sub_assign(a);
            }
            term.mul_assign(&challenge);
            term.add_assign(a);
            term
        })
        .collect()
}

pub(crate) fn fold_case<F: PrimitiveField>(log_n: u32, steps: u32, context: &ProverContext) {
    let count = 1 << log_n;
    let mut monomials: Vec<_> = (0..count).map(|i| F::sample(20_000 + i as u32)).collect();
    let mut evals: Vec<_> = (0..count).map(|i| F::sample(40_000 + i as u32)).collect();
    let mut eq: Vec<_> = (0..count).map(|i| F::sample(60_000 + i as u32)).collect();
    let mut state = F::state(log_n, context);
    F::set_forms(&mut state, &monomials, &evals, &eq, context);
    for step in 0..steps {
        let challenge = F::sample(1777 + 111 * step);
        let wrong = fold_values(&monomials, challenge, true);
        monomials = fold_values(&monomials, challenge, false);
        assert_ne!(wrong, monomials, "fold forms must remain distinct");
        evals = fold_values(&evals, challenge, true);
        eq = fold_values(&eq, challenge, true);
        F::fold(&mut state, challenge, context);
        let (actual_monomials, actual_evals, actual_eq) = F::read_forms(&state, context);
        assert_eq!(actual_monomials, monomials, "monomial fold step {step}");
        assert_eq!(actual_evals, evals, "evaluation fold step {step}");
        assert_eq!(actual_eq, eq, "eq fold step {step}");
    }
}

pub(crate) fn three_point_case<F: PrimitiveField>(log_n: u32, context: &ProverContext) {
    let count = 1 << log_n;
    let evals: Vec<_> = (0..count).map(|i| F::sample(1 + 10 * i as u32)).collect();
    let eq: Vec<_> = (0..count).map(|i| F::sample(100 + 10 * i as u32)).collect();
    let mut expected = [F::ZERO; 3];
    for ([a0, a1], [b0, b1]) in evals.as_chunks::<2>().0.iter().zip(eq.as_chunks::<2>().0) {
        let mut first = *a0;
        first.mul_assign(b0);
        expected[0].add_assign(&first);
        let mut last = *a1;
        last.mul_assign(b1);
        expected[1].add_assign(&last);
        let mut sum_a = *a0;
        sum_a.add_assign(a1);
        let mut sum_b = *b0;
        sum_b.add_assign(b1);
        sum_a.mul_assign(&sum_b);
        expected[2].add_assign(&sum_a);
    }
    let mut state = F::state(log_n, context);
    F::set_forms(&mut state, &vec![F::ZERO; count], &evals, &eq, context);
    assert_eq!(F::three_point(&mut state, context), expected);
}

pub(crate) fn monomial_case<F: PrimitiveField>(log_n: u32, context: &ProverContext) {
    let coeffs: Vec<_> = (0..1 << log_n)
        .map(|i| F::sample(1 + 50 * i as u32))
        .collect();
    let mut state = F::state(log_n, context);
    F::set_forms(
        &mut state,
        &coeffs,
        &vec![F::ZERO; coeffs.len()],
        &vec![F::ZERO; coeffs.len()],
        context,
    );
    for point in [F::ZERO, F::ONE, F::sample(999)] {
        let expected = coeffs.iter().rev().fold(F::ZERO, |mut acc, coeff| {
            acc.mul_assign(&point);
            acc.add_assign(coeff);
            acc
        });
        assert_eq!(F::monomial_eval(&mut state, point, context), expected);
    }
}
