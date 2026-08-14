//! The reference backend: delegates verbatim to the historical free
//! functions, for any `<F, E>` — the parity baseline every other backend is
//! byte-compared against.

use super::*;

/// The reference implementation: delegates verbatim to the historical free
/// functions, for any `<F, E>`.
#[derive(Clone, Copy, Debug, Default)]
pub struct NaiveBackend;

impl<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field> Backend<F, E> for NaiveBackend {
    fn lde_multiple_polys_from_hypercubes(
        &self,
        evals: &[&[F]],
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<Vec<ColumnMajorCosetBoundTracePart<F, F>>> {
        lde_multiple_polys_parallel_from_hypercubes(evals, twiddles, lde_factor, worker)
    }

    fn lde_packed_monomials_into_cosets(
        &self,
        monomials: Vec<Vec<F>>,
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<ColumnMajorBaseOracleForCoset<F>> {
        lde_packed_monomials_into_cosets(monomials, twiddles, lde_factor, worker)
    }

    fn lde_ext_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[E],
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[E]>, F)> {
        compute_column_major_lde_from_monomial_form(
            monomial_form_normal_order,
            twiddles,
            lde_factor,
            Some(worker),
        )
    }

    fn lde_base_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[F],
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[F]>, F)> {
        compute_column_major_lde_from_monomial_form(
            monomial_form_normal_order,
            twiddles,
            lde_factor,
            Some(worker),
        )
    }

    fn pack_polys_from_hypercubes_to_monomials(
        &self,
        evals: &[&[F]],
        pack_log2: usize,
        worker: &Worker,
    ) -> Vec<Vec<F>> {
        pack_polys_parallel_from_hypercubes_to_monomials(evals, pack_log2, worker)
    }

    fn monomial_form_from_main_domain(
        &self,
        source_domain: Vec<E>,
        twiddles: &Twiddles<F, Global>,
        _worker: &Worker,
    ) -> Vec<E> {
        compute_column_major_monomial_form_from_main_domain_owned::<F, E, Global>(
            source_domain,
            twiddles,
        )
    }

    fn hypercube_evals_from_monomial_form(&self, monomial_form: Vec<E>, worker: &Worker) -> Vec<E> {
        // historical whir_fold sequence: worker-parallel ADD transform, then a
        // SERIAL bit-reversal
        let mut v = monomial_form;
        let log_n = v.len().trailing_zeros();
        crate::gkr::whir::hypercube_to_monomial::parallel_multivariate_coeffs_into_hypercube_evals(
            &mut v, log_n, worker,
        );
        // natural order out (LSB convention)
        v
    }

    fn update_eq_poly(
        &self,
        eq_poly: &mut [E],
        ood_samples: &[(E, E)],
        in_domain_samples: &[(F, E)],
        worker: &Worker,
    ) {
        crate::gkr::whir::update_eq_poly_reference(eq_poly, ood_samples, in_domain_samples, worker)
    }

    type ExtCoeffConv = StandardExtCoeffConv<F>;
    fn ext_coeff_conv(&self, coset_len: usize, values_per_leaf: usize) -> Self::ExtCoeffConv {
        StandardExtCoeffConv::new(coset_len, values_per_leaf)
    }
}
