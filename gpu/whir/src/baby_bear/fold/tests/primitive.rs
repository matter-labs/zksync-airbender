use super::*;
use crate::primitive_tests::PrimitiveField;

impl PrimitiveField for E4 {
    type State = GpuWhirState;
    fn sample(seed: u32) -> Self {
        sample_ext(seed)
    }
    fn state(log_n: u32, context: &ProverContext) -> Self::State {
        GpuWhirState::new(1usize << log_n, context).unwrap()
    }
    fn set_forms(
        state: &mut Self::State,
        monomials: &[Self],
        evals: &[Self],
        eq: &[Self],
        context: &ProverContext,
    ) {
        let vectorized = e4_coeffs_to_vectorized(monomials);
        state.sumchecked_poly_monomial_form =
            DeviceMatrixOwnsAllocation::new(alloc_and_copy(&vectorized, context), monomials.len());
        state.sumchecked_poly_evaluation_form = alloc_and_copy(evals, context);
        state.eq_poly = alloc_and_copy(eq, context);
        // The vectorized host scratch must outlive its H2D copy.
        context.get_exec_stream().synchronize().unwrap();
    }
    fn read_forms(
        state: &Self::State,
        context: &ProverContext,
    ) -> (Vec<Self>, Vec<Self>, Vec<Self>) {
        let vectorized = copy_back(state.sumchecked_poly_monomial_form.slice(), context);
        (
            vectorized_to_e4_coeffs(
                &vectorized,
                state.sumchecked_poly_monomial_form.stride(),
                state.current_len,
            ),
            copy_back(&state.sumchecked_poly_evaluation_form, context),
            copy_back(&state.eq_poly, context),
        )
    }
    fn build_eq(state: &mut Self::State, point: &[Self], context: &ProverContext) -> Vec<Self> {
        let point_device = alloc_and_copy(point, context);
        launch_build_eq_values_from_point(
            point_device.as_ptr(),
            0,
            point.len(),
            state.eq_group_tables.as_mut_ptr(),
            state.eq_poly.as_mut_ptr(),
            state.current_len,
            context,
        )
        .unwrap();
        copy_back(&state.eq_poly, context)
    }
    fn fold(state: &mut Self::State, challenge: Self, context: &ProverContext) {
        let old = (
            state.sumchecked_poly_monomial_form.slice().as_ptr(),
            state.sumchecked_poly_evaluation_form.as_ptr(),
            state.eq_poly.as_ptr(),
        );
        let next = state.current_len / 2;
        let challenge = alloc_and_copy(&[challenge], context);
        schedule_fold_state(state, &challenge[0], context).unwrap();
        assert_eq!(state.current_len, next);
        assert_eq!(state.sumchecked_poly_monomial_form.stride(), next);
        assert_eq!(
            state.sumchecked_poly_monomial_form.slice().len(),
            next * EXT4_DEGREE
        );
        assert_eq!(state.sumchecked_poly_evaluation_form.len(), next);
        assert_eq!(state.eq_poly.len(), next);
        assert_ne!(old.0, state.sumchecked_poly_monomial_form.slice().as_ptr());
        assert_ne!(old.1, state.sumchecked_poly_evaluation_form.as_ptr());
        assert_ne!(old.2, state.eq_poly.as_ptr());
    }
    fn three_point(state: &mut Self::State, context: &ProverContext) -> [Self; 3] {
        let (a, b, mut half) = special_three_point_eval_device(state, context).unwrap();
        half.double();
        half.double();
        [a, b, half]
    }
    fn monomial_eval(state: &mut Self::State, point: Self, context: &ProverContext) -> Self {
        evaluate_monomial_form_device(state, point, context).unwrap()
    }
}
