//! The generic work-stealing backend: canonical kernels for every `<F, E>`
//! pair, poly x coset task grids over the worker's rayon pool, radix-4 fused
//! transforms, and all-threads O(1) batched-poly operations. Shared grid
//! machinery lives in the parent module.

use super::*;

/// Work-stealing implementation: identical values to [`NaiveBackend`], but the
/// LDE work is flattened into a `poly × coset` task grid and distributed over
/// the [`Worker`]'s rayon thread pool, with each task running the fused SERIAL
/// coset pipeline (`fft::lde_coset_natural_seq_fused`).
///
/// Why: the naive scheduling parallelizes either over polynomials only (base
/// commits — idle cores when few columns meet many cores) or runs cosets
/// sequentially with one barrier-heavy parallel NTT per coset (packed commits —
/// per-FFT parallel efficiency measured at only ~30–50% beyond 8 threads,
/// because every NTT stage is a synchronization barrier). Independent serial
/// FFTs have no barriers at all: with `polys × lde_factor` tasks (e.g. 7 packed
/// polys × 32 cosets = 224 tasks for the unified Proth120 circuit) every core
/// stays busy until the tail, and rayon's work stealing absorbs the imbalance.
#[derive(Clone, Copy, Debug, Default)]
pub struct WorkStealingBackend;

impl<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field> Backend<F, E>
    for WorkStealingBackend
{
    type TwiddleSet = Twiddles<F, Global>;
    fn make_twiddles(&self, domain_size: usize, worker: &Worker) -> Self::TwiddleSet {
        Twiddles::new(domain_size, worker)
    }

    fn lde_multiple_polys_from_hypercubes(
        &self,
        evals: &[&[F]],
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<Vec<ColumnMajorCosetBoundTracePart<F, F>>> {
        ws_lde_multiple_polys_from_hypercubes(
            evals,
            twiddles,
            lde_factor,
            &|m, o, t| fft::lde_coset_natural_seq_fused(m, o, t),
            &|v, l| {
                crate::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs_radix4(v, l)
            },
            &|m, o, t, w| lde_coset_canonical_parallel(m, o, t, w),
            worker,
        )
    }

    fn lde_packed_monomials_into_cosets(
        &self,
        monomials: Vec<Vec<F>>,
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<ColumnMajorBaseOracleForCoset<F>> {
        ws_lde_packed_monomials_into_cosets(
            monomials,
            twiddles,
            lde_factor,
            &|m, o, t| fft::lde_coset_natural_seq_fused(m, o, t),
            &|m, o, t, w| lde_coset_canonical_parallel(m, o, t, w),
            worker,
        )
    }

    fn lde_ext_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[E],
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[E]>, F)> {
        ws_lde_single_poly_from_monomial_form(
            monomial_form_normal_order,
            twiddles,
            lde_factor,
            &|m, o, t| fft::lde_coset_natural_seq_fused(m, o, t),
            &|m, o, t, w| lde_coset_canonical_parallel(m, o, t, w),
            worker,
        )
    }

    fn lde_base_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[F],
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[F]>, F)> {
        ws_lde_single_poly_from_monomial_form(
            monomial_form_normal_order,
            twiddles,
            lde_factor,
            &|m, o, t| fft::lde_coset_natural_seq_fused(m, o, t),
            &|m, o, t, w| lde_coset_canonical_parallel(m, o, t, w),
            worker,
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
        worker: &Worker,
    ) -> Vec<E> {
        ws_monomial_form_from_main_domain(source_domain, twiddles, worker)
    }

    fn hypercube_evals_from_monomial_form(&self, monomial_form: Vec<E>, worker: &Worker) -> Vec<E> {
        ws_hypercube_evals_from_monomial_form::<F, E>(monomial_form, worker)
    }

    fn update_eq_poly(
        &self,
        eq_poly: &mut [E],
        ood_samples: &[(E, E)],
        in_domain_samples: &[(F, E)],
        worker: &Worker,
    ) {
        ws_update_eq_poly(eq_poly, ood_samples, in_domain_samples, worker)
    }

    type ExtCoeffConv = StandardExtCoeffConv<F>;
    fn ext_coeff_conv(&self, coset_len: usize, values_per_leaf: usize) -> Self::ExtCoeffConv {
        StandardExtCoeffConv::new(coset_len, values_per_leaf)
    }
}
