//! Proth120-specific work-stealing backend: lazy-reduction radix-8 kernels on
//! both planner branches. See the struct docs for the measured wins.

use super::*;

/// Work-stealing backend running Proth120 LAZY-REDUCTION RADIX-8 coset
/// kernels on BOTH planner branches: values held in `[0, 2p)` through the NTT
/// (the Montgomery multiply loses its final conditional subtraction; one
/// canonicalization pass at the end), and three butterfly levels fused per
/// sweep (radix-4 / fused-radix-2 passes absorb leftover levels) — the array
/// is traversed ~log_n/3 times instead of log_n, which matters most when the
/// work saturates DRAM bandwidth (measured 2.0x vs the canonical kernel at
/// 224 concurrent 2^26 tasks on 88-core Sapphire Rapids; ~1.6x serial).
///
/// - Flat grid tasks (tasks ≥ threads — the base commits) run the SERIAL
///   `fft::proth120_lazy::lde_coset_lazy_r8`.
/// - The parallel-within-task plan (tasks < threads — notably the SMALLER
///   intermediate-WHIR-oracle FFTs, where `lde_factor` cosets < cores) runs
///   the worker-parallel `fft::proth120_lazy::lde_coset_lazy_parallel_r8`, so
///   the shrinking fold sizes keep the radix + lazy benefits.
///
/// Outputs are bit-identical to [`WorkStealingBackend`] / [`NaiveBackend`].
/// Implemented ONLY for `Backend<Proth120, Proth120>` — the kernels are
/// field-specific, and callers opt in where they concretely know the field
/// (the Proth120 tests/examples) instead of any runtime type dispatch.
#[derive(Clone, Copy, Debug, Default)]
pub struct Proth120WorkStealingLazyBackend;

impl Backend<Proth120, Proth120> for Proth120WorkStealingLazyBackend {
    type TwiddleSet = Twiddles<Proth120, Global>;
    fn make_twiddles(&self, domain_size: usize, worker: &Worker) -> Self::TwiddleSet {
        Twiddles::new(domain_size, worker)
    }

    fn lde_multiple_polys_from_hypercubes(
        &self,
        evals: &[&[Proth120]],
        twiddles: &Twiddles<Proth120, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<Vec<ColumnMajorCosetBoundTracePart<Proth120, Proth120>>> {
        ws_lde_multiple_polys_from_hypercubes(
            evals,
            twiddles,
            lde_factor,
            &|m, o, t| fft::proth120_lazy::lde_coset_lazy_r8(m, o, t),
            &|v, l| {
                crate::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs_radix4(v, l)
            },
            &|m, o, t, w| fft::proth120_lazy::lde_coset_lazy_parallel_r8(m, o, t, w),
            worker,
        )
    }

    fn lde_packed_monomials_into_cosets(
        &self,
        monomials: Vec<Vec<Proth120>>,
        twiddles: &Twiddles<Proth120, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<ColumnMajorBaseOracleForCoset<Proth120>> {
        ws_lde_packed_monomials_into_cosets(
            monomials,
            twiddles,
            lde_factor,
            &|m, o, t| fft::proth120_lazy::lde_coset_lazy_r8(m, o, t),
            &|m, o, t, w| fft::proth120_lazy::lde_coset_lazy_parallel_r8(m, o, t, w),
            worker,
        )
    }

    fn lde_ext_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[Proth120],
        twiddles: &Twiddles<Proth120, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[Proth120]>, Proth120)> {
        ws_lde_single_poly_from_monomial_form(
            monomial_form_normal_order,
            twiddles,
            lde_factor,
            &|m, o, t| fft::proth120_lazy::lde_coset_lazy_r8(m, o, t),
            &|m, o, t, w| fft::proth120_lazy::lde_coset_lazy_parallel_r8(m, o, t, w),
            worker,
        )
    }

    fn lde_ext_poly_from_monomial_form_continuous(
        &self,
        monomial_form_normal_order: &[Proth120],
        twiddles: &Twiddles<Proth120, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> (Box<[Proth120]>, Vec<Proth120>) {
        ws_lde_single_poly_continuous(
            monomial_form_normal_order,
            twiddles,
            lde_factor,
            &|m, o, t, out| fft::proth120_lazy::lde_coset_lazy_r8_into(m, o, t, out),
            &|m, o, t, w, out| fft::proth120_lazy::lde_coset_lazy_parallel_r8_into(m, o, t, w, out),
            worker,
        )
    }

    fn lde_base_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[Proth120],
        twiddles: &Twiddles<Proth120, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[Proth120]>, Proth120)> {
        ws_lde_single_poly_from_monomial_form(
            monomial_form_normal_order,
            twiddles,
            lde_factor,
            &|m, o, t| fft::proth120_lazy::lde_coset_lazy_r8(m, o, t),
            &|m, o, t, w| fft::proth120_lazy::lde_coset_lazy_parallel_r8(m, o, t, w),
            worker,
        )
    }

    fn pack_polys_from_hypercubes_to_monomials(
        &self,
        evals: &[&[Proth120]],
        pack_log2: usize,
        worker: &Worker,
    ) -> Vec<Vec<Proth120>> {
        pack_polys_parallel_from_hypercubes_to_monomials(evals, pack_log2, worker)
    }

    fn monomial_form_from_main_domain(
        &self,
        source_domain: Vec<Proth120>,
        twiddles: &Twiddles<Proth120, Global>,
        worker: &Worker,
    ) -> Vec<Proth120> {
        ws_monomial_form_from_main_domain(source_domain, twiddles, worker)
    }

    fn hypercube_evals_from_monomial_form(
        &self,
        monomial_form: Vec<Proth120>,
        worker: &Worker,
    ) -> Vec<Proth120> {
        ws_hypercube_evals_from_monomial_form::<Proth120, Proth120>(monomial_form, worker)
    }

    fn update_eq_poly(
        &self,
        eq_poly: &mut [Proth120],
        ood_samples: &[(Proth120, Proth120)],
        in_domain_samples: &[(Proth120, Proth120)],
        worker: &Worker,
    ) {
        ws_update_eq_poly(eq_poly, ood_samples, in_domain_samples, worker)
    }

    type ExtCoeffConv = StandardExtCoeffConv<Proth120>;
    fn ext_coeff_conv(&self, coset_len: usize, values_per_leaf: usize) -> Self::ExtCoeffConv {
        StandardExtCoeffConv::new(coset_len, values_per_leaf)
    }
}
