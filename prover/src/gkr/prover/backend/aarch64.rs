//! aarch64-specific BabyBear backend: NEON base-field coset kernels
//! (u64-accumulation radix-4 butterflies), combined-twiddle tables shared per
//! batched call. See the struct docs for the measured wins.

use super::*;

/// Work-stealing backend whose BASE-FIELD flat grid tasks run the NEON
/// BabyBear serial coset kernel (`fft::baby_bear_neon::lde_coset_neon`):
/// 4-lane Montgomery butterflies, all-NEON stage plan (`uzp`/`zip` shuffle
/// passes for `ppg = 1, 2`, u64-accumulation radix-4 fused passes, fused
/// tail), with the combined-twiddle tables built ONCE per batched call and
/// shared across its coset tasks. Measured 2.4x serial / 1.8x grid over the
/// scalar fused kernel on M3 (12 threads); extension-field ops stay on the
/// canonical generic kernels for now. Every poly size is supported — below 16
/// elements the kernel degrades to the scalar reference. Outputs are
/// bit-identical to [`WorkStealingBackend`] / [`NaiveBackend`].
///
/// Implemented ONLY for `Backend<BabyBearField, BabyBearExt4>` and only on
/// aarch64 — callers opt in via [`DefaultBabyBearBackend`].
#[derive(Clone, Copy, Debug, Default)]
pub struct BabyBearNeonWorkStealingBackend;

/// NEON leaf-fold conversion for the aarch64 BabyBear backend: whole Ext4
/// leaves (one element = one vector, <= 32 vectors) folded to coefficient
/// form entirely in registers with fused `root * 2^-1` twiddles — see
/// `fft::baby_bear_neon::ext4::leaves_to_coeff_form*`. Byte-identical to the
/// scalar context (parity-tested); leaf widths outside `2..=32` fall back to
/// it, and under `eval_leaves` the conversion is the identity.
pub struct BabyBearNeonExtCoeffConv {
    #[cfg(not(feature = "eval_leaves"))]
    ctx: crate::gkr::whir::ExtCoeffConvCtx<BabyBearField>,
    #[cfg(not(feature = "eval_leaves"))]
    hp_raw: Vec<u32>,
    #[cfg(feature = "eval_leaves")]
    _unused: (),
}

impl BabyBearNeonExtCoeffConv {
    pub fn new(coset_len: usize, values_per_leaf: usize) -> Self {
        #[cfg(not(feature = "eval_leaves"))]
        {
            let ctx =
                crate::gkr::whir::ExtCoeffConvCtx::<BabyBearField>::new(coset_len, values_per_leaf);
            let hp_raw = ctx
                .high_powers_offsets
                .iter()
                .map(|x| x.raw_u32_value())
                .collect();
            Self { ctx, hp_raw }
        }
        #[cfg(feature = "eval_leaves")]
        {
            let _ = (coset_len, values_per_leaf);
            Self { _unused: () }
        }
    }

    #[cfg(not(feature = "eval_leaves"))]
    fn neon_applicable(&self) -> bool {
        (2..=32).contains(&self.ctx.values_per_leaf)
    }

    #[cfg(not(feature = "eval_leaves"))]
    fn root_invs_raw(&self, offset: BabyBearField) -> Vec<u32> {
        let offset_inv = offset.inverse().unwrap();
        self.ctx
            .coset_gen_inv_powers
            .iter()
            .map(|p| {
                let mut x = *p;
                x.mul_assign(&offset_inv);
                x.raw_u32_value()
            })
            .collect()
    }
}

impl ExtCoeffConversion<BabyBearField, BabyBearExt4> for BabyBearNeonExtCoeffConv {
    fn apply(&self, column: &mut [BabyBearExt4], offset: BabyBearField, worker: &Worker) {
        #[cfg(not(feature = "eval_leaves"))]
        {
            if !self.neon_applicable() {
                return self.ctx.apply(column, offset, worker);
            }
            let root_invs = self.root_invs_raw(offset);
            fft::baby_bear_neon::ext4::leaves_to_coeff_form(
                column,
                &self.ctx.offsets,
                &self.hp_raw,
                self.ctx.two_inv,
                &root_invs,
                worker,
            );
        }
        #[cfg(feature = "eval_leaves")]
        {
            let _ = (column, offset, worker);
        }
    }

    fn apply_serial(&self, column: &mut [BabyBearExt4], offset: BabyBearField) {
        #[cfg(not(feature = "eval_leaves"))]
        {
            if !self.neon_applicable() {
                return self.ctx.apply_serial(column, offset);
            }
            let root_invs = self.root_invs_raw(offset);
            fft::baby_bear_neon::ext4::leaves_to_coeff_form_serial(
                column,
                &self.ctx.offsets,
                &self.hp_raw,
                self.ctx.two_inv,
                &root_invs,
            );
        }
        #[cfg(feature = "eval_leaves")]
        {
            let _ = (column, offset);
        }
    }
}

impl Backend<BabyBearField, BabyBearExt4> for BabyBearNeonWorkStealingBackend {
    fn lde_multiple_polys_from_hypercubes(
        &self,
        evals: &[&[BabyBearField]],
        twiddles: &Twiddles<BabyBearField, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<Vec<ColumnMajorCosetBoundTracePart<BabyBearField, BabyBearField>>> {
        let n = evals.first().map(|c| c.len()).unwrap_or(0);
        let ext = fft::baby_bear_neon::NeonTwiddleExt::build(&twiddles.forward_twiddles, n);
        ws_lde_multiple_polys_from_hypercubes(
            evals,
            twiddles,
            lde_factor,
            &|m, o, t| fft::baby_bear_neon::lde_coset_neon(m, o, t, &ext),
            &|v, l| {
                crate::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs_neon_bb(v, l)
            },
            &|m, o, t, w| lde_coset_canonical_parallel(m, o, t, w),
            worker,
        )
    }

    fn lde_packed_monomials_into_cosets(
        &self,
        monomials: Vec<Vec<BabyBearField>>,
        twiddles: &Twiddles<BabyBearField, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<ColumnMajorBaseOracleForCoset<BabyBearField>> {
        let n = monomials.first().map(|c| c.len()).unwrap_or(0);
        let ext = fft::baby_bear_neon::NeonTwiddleExt::build(&twiddles.forward_twiddles, n);
        ws_lde_packed_monomials_into_cosets(
            monomials,
            twiddles,
            lde_factor,
            &|m, o, t| fft::baby_bear_neon::lde_coset_neon(m, o, t, &ext),
            &|m, o, t, w| lde_coset_canonical_parallel(m, o, t, w),
            worker,
        )
    }

    fn lde_ext_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[BabyBearExt4],
        twiddles: &Twiddles<BabyBearField, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[BabyBearExt4]>, BabyBearField)> {
        use worker::rayon::prelude::*;

        let n = monomial_form_normal_order.len();
        let ext = fft::baby_bear_neon::NeonTwiddleExt::build(&twiddles.forward_twiddles, n);
        let root_powers = coset_offsets::<BabyBearField>(n, lde_factor);
        let tw = &twiddles.forward_twiddles[..];

        // MODE A everywhere: all cosets in parallel, each running the
        // worker-parallel kernel. With few cosets the nested scopes land on
        // the shared pool and idle threads steal butterfly chunks (297ms vs
        // 350ms flat at 2^23 x 16, 7.2ms vs 14.2ms at 2^20 x 4); with many
        // small cosets every thread already owns a coset, the nested scopes
        // find no idle workers and the kernel degenerates to the serial flat
        // schedule (measured identical: 165.5ms vs 165.7ms at 2^18 x 512) —
        // so one mode covers both regimes.
        worker.pool.install(|| {
            (0..lde_factor)
                .into_par_iter()
                .map(|coset| {
                    let offset = root_powers[coset];
                    let data = fft::baby_bear_neon::ext4::lde_coset_parallel(
                        monomial_form_normal_order,
                        offset,
                        tw,
                        &ext,
                        worker,
                    );
                    (data.into_boxed_slice(), offset)
                })
                .collect()
        })
    }

    fn lde_base_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[BabyBearField],
        twiddles: &Twiddles<BabyBearField, Global>,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[BabyBearField]>, BabyBearField)> {
        let n = monomial_form_normal_order.len();
        let ext = fft::baby_bear_neon::NeonTwiddleExt::build(&twiddles.forward_twiddles, n);
        ws_lde_single_poly_from_monomial_form(
            monomial_form_normal_order,
            twiddles,
            lde_factor,
            &|m, o, t| fft::baby_bear_neon::lde_coset_neon(m, o, t, &ext),
            &|m, o, t, w| lde_coset_canonical_parallel(m, o, t, w),
            worker,
        )
    }

    fn pack_polys_from_hypercubes_to_monomials(
        &self,
        evals: &[&[BabyBearField]],
        pack_log2: usize,
        worker: &Worker,
    ) -> Vec<Vec<BabyBearField>> {
        pack_polys_parallel_from_hypercubes_to_monomials(evals, pack_log2, worker)
    }

    fn monomial_form_from_main_domain(
        &self,
        source_domain: Vec<BabyBearExt4>,
        twiddles: &Twiddles<BabyBearField, Global>,
        worker: &Worker,
    ) -> Vec<BabyBearExt4> {
        let n = source_domain.len();
        let inv_ext = fft::baby_bear_neon::NeonTwiddleExt::build(&twiddles.inverse_twiddles, n);
        fft::baby_bear_neon::ext4::monomial_form_from_main_domain(
            source_domain,
            &twiddles.inverse_twiddles,
            &inv_ext,
            worker,
        )
    }

    fn hypercube_evals_from_monomial_form(
        &self,
        monomial_form: Vec<BabyBearExt4>,
        worker: &Worker,
    ) -> Vec<BabyBearExt4> {
        fft::baby_bear_neon::ext4::hypercube_evals_from_monomial_form(monomial_form, worker)
    }

    fn update_eq_poly(
        &self,
        eq_poly: &mut [BabyBearExt4],
        ood_samples: &[(BabyBearExt4, BabyBearExt4)],
        in_domain_samples: &[(BabyBearField, BabyBearExt4)],
        worker: &Worker,
    ) {
        ws_update_eq_poly(eq_poly, ood_samples, in_domain_samples, worker)
    }

    type ExtCoeffConv = BabyBearNeonExtCoeffConv;
    fn ext_coeff_conv(&self, coset_len: usize, values_per_leaf: usize) -> Self::ExtCoeffConv {
        BabyBearNeonExtCoeffConv::new(coset_len, values_per_leaf)
    }
}
