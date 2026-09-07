//! x86-64 (AVX2) BabyBear backend: the twin of the aarch64 NEON backend —
//! 8-lane AVX2 base-field coset kernels (u64-accumulation radix-4
//! butterflies), two-elements-per-vector Ext4 kernels, combined-twiddle
//! tables built once per proving run and shared across every batched call.

use super::*;

/// Work-stealing backend whose flat grid tasks run the AVX2 BabyBear coset
/// kernels (`fft::baby_bear_avx2`): the base-field serial kernel for the
/// base commits, the Ext4 serial/worker-parallel kernels for the
/// intermediate WHIR oracles, the fused inverse / ADD transforms for the
/// batched WHIR polynomial and the register-resident leaf folding for the
/// coefficient-form commits. Every poly size is supported — below the vector
/// widths the kernels degrade to the scalar references. Outputs are
/// bit-identical to [`WorkStealingBackend`] / [`NaiveBackend`].
///
/// Implemented ONLY for `Backend<BabyBearField, BabyBearExt4>` and only when
/// the build target enables AVX2 — callers opt in via
/// [`DefaultBabyBearBackend`].
#[derive(Clone, Copy, Debug, Default)]
pub struct BabyBearAvx2WorkStealingBackend;

/// AVX2 leaf-fold conversion for the x86-64 BabyBear backend: whole Ext4
/// leaves (two leaves per vector, <= 32 slots) folded to coefficient form
/// with fused `root * 2^-1` twiddles — see
/// `fft::baby_bear_avx2::ext4::leaves_to_coeff_form*`. Byte-identical to the
/// scalar context (parity-tested); leaf widths outside `2..=32` fall back to
/// it, and under `eval_leaves` the conversion is the identity.
pub struct BabyBearAvx2ExtCoeffConv {
    #[cfg(not(feature = "eval_leaves"))]
    ctx: crate::gkr::whir::ExtCoeffConvCtx<BabyBearField>,
    #[cfg(not(feature = "eval_leaves"))]
    hp_raw: Vec<u32>,
    #[cfg(feature = "eval_leaves")]
    _unused: (),
}

impl BabyBearAvx2ExtCoeffConv {
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
    fn avx2_applicable(&self) -> bool {
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

impl ExtCoeffConversion<BabyBearField, BabyBearExt4> for BabyBearAvx2ExtCoeffConv {
    fn apply(&self, column: &mut [BabyBearExt4], offset: BabyBearField, worker: &Worker) {
        #[cfg(not(feature = "eval_leaves"))]
        {
            if !self.avx2_applicable() {
                return self.ctx.apply(column, offset, worker);
            }
            let root_invs = self.root_invs_raw(offset);
            fft::baby_bear_avx2::ext4::leaves_to_coeff_form(
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
            if !self.avx2_applicable() {
                return self.ctx.apply_serial(column, offset);
            }
            let root_invs = self.root_invs_raw(offset);
            fft::baby_bear_avx2::ext4::leaves_to_coeff_form_serial(
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

/// The AVX2 backend's twiddle set: the plain radix-2 tables plus the
/// combined-twiddle tables for BOTH directions, all built ONCE per proving
/// run by `make_twiddles` (parallel fills) and shared across every batched
/// call — smaller transforms read prefixes, so no method ever rebuilds them.
pub struct BabyBearAvx2Twiddles {
    pub plain: Twiddles<BabyBearField, Global>,
    pub forward_ext: fft::baby_bear_avx2::Avx2TwiddleExt,
    pub inverse_ext: fft::baby_bear_avx2::Avx2TwiddleExt,
}

impl TwiddleSetOps<BabyBearField> for BabyBearAvx2Twiddles {
    #[inline(always)]
    fn plain(&self) -> &Twiddles<BabyBearField, Global> {
        &self.plain
    }
}

/// Size-dependent coset plan for Ext4 LDEs. Measured on the 192-core box with
/// 12 pinned 16-thread provers (the production batch shape): cosets of
/// 2^20 elements and up run EVERY coset on all threads through the blocked
/// kernel — the flat serial grid streams a 128 MB coset ~12 times from DRAM
/// under contention (2^23 x 16: all-threads 0.63 s vs serial grid 0.90 s;
/// 2^21 x 64: 0.52 vs 0.57) — while smaller cosets keep the tasks/threads
/// rule (2^18 x 512: serial grid 0.17 s vs all-threads 1.31 s, per-coset
/// scope overhead).
fn ext4_coset_plan(n: usize, lde_factor: usize, worker: &Worker) -> CosetGridPlan {
    if n >= (1usize << 20) {
        CosetGridPlan::ParallelWithinTask
    } else {
        plan_coset_grid::<BabyBearExt4>(lde_factor, worker)
    }
}

impl Backend<BabyBearField, BabyBearExt4> for BabyBearAvx2WorkStealingBackend {
    type TwiddleSet = BabyBearAvx2Twiddles;
    fn make_twiddles(&self, domain_size: usize, worker: &Worker) -> Self::TwiddleSet {
        let plain: Twiddles<BabyBearField, Global> = Twiddles::new(domain_size, worker);
        let forward_ext = fft::baby_bear_avx2::Avx2TwiddleExt::build_parallel(
            &plain.forward_twiddles,
            domain_size,
            worker,
        );
        let inverse_ext = fft::baby_bear_avx2::Avx2TwiddleExt::build_parallel(
            &plain.inverse_twiddles,
            domain_size,
            worker,
        );
        BabyBearAvx2Twiddles {
            plain,
            forward_ext,
            inverse_ext,
        }
    }

    fn lde_multiple_polys_from_hypercubes(
        &self,
        evals: &[&[BabyBearField]],
        twiddles: &Self::TwiddleSet,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<Vec<ColumnMajorCosetBoundTracePart<BabyBearField, BabyBearField>>> {
        let ext = &twiddles.forward_ext;
        let num_cols = evals.len();
        let n = evals.first().map(|c| c.len()).unwrap_or(0);
        let blocked_min = 1usize << fft::baby_bear_avx2::avx2::BLOCK_LOG2;
        // EXPERIMENT (base-commit scheduling): a 2^24 column is larger than
        // any L3, so per-column DRAM passes are what the machine pays; the
        // flat serial grid streams every column ~14 times while the blocked
        // kernel does it in ~5. Run EVERY column-coset on all threads when
        // this is set, not only when the grid is under-filled.
        const ALL_THREADS_PER_COSET: bool = true;
        let grid_fills_pool = num_cols * lde_factor >= worker.get_num_cores();
        if num_cols == 0 || n < blocked_min || (grid_fills_pool && !ALL_THREADS_PER_COSET) {
            return ws_lde_multiple_polys_from_hypercubes(
                evals,
                &twiddles.plain,
                lde_factor,
                &|m, o, t| fft::baby_bear_avx2::lde_coset_avx2(m, o, t, ext),
                &|v, l| {
                    crate::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs_avx2_bb(v, l)
                },
                &|m, o, t, w| lde_coset_canonical_parallel(m, o, t, w),
                worker,
            );
        }

        // ALL THREADS PER COLUMN: a 2^24 column is larger than any L3, so
        // what counts is the number of DRAM sweeps per column, not the task
        // grid. Each column's transform (copy + block-local levels in one
        // sweep, radix-16 sweeps for the high strides) and then every coset
        // FFT (fused scale/bit-reverse/copy sweep, block-local phase, radix-16
        // global passes) run on the whole worker, no nested scopes.
        let root_powers = coset_offsets::<BabyBearField>(n, lde_factor);
        let tw = &twiddles.plain.forward_twiddles[..];
        let size_log2 = n.trailing_zeros();
        let monomials: Vec<Vec<BabyBearField>> = evals
            .iter()
            .map(|col| {
                crate::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs_avx2_bb_parallel(col, size_log2, worker)
            })
            .collect();
        (0..lde_factor)
            .map(|coset| {
                let offset = root_powers[coset];
                (0..num_cols)
                    .map(|col| {
                        let data = fft::baby_bear_avx2::lde_coset_avx2_parallel(
                            &monomials[col],
                            offset,
                            tw,
                            ext,
                            worker,
                        );
                        ColumnMajorCosetBoundTracePart {
                            column: Arc::new(data.into_boxed_slice()),
                            offset,
                        }
                    })
                    .collect()
            })
            .collect()
    }

    fn lde_packed_monomials_into_cosets(
        &self,
        monomials: Vec<Vec<BabyBearField>>,
        twiddles: &Self::TwiddleSet,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<ColumnMajorBaseOracleForCoset<BabyBearField>> {
        let ext = &twiddles.forward_ext;
        ws_lde_packed_monomials_into_cosets(
            monomials,
            &twiddles.plain,
            lde_factor,
            &|m, o, t| fft::baby_bear_avx2::lde_coset_avx2(m, o, t, ext),
            &|m, o, t, w| lde_coset_canonical_parallel(m, o, t, w),
            worker,
        )
    }

    fn lde_ext_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[BabyBearExt4],
        twiddles: &Self::TwiddleSet,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[BabyBearExt4]>, BabyBearField)> {
        let ext = &twiddles.forward_ext;
        let plan = ext4_coset_plan(monomial_form_normal_order.len(), lde_factor, worker);
        // Planner-driven grid (unlike the NEON backend's "every coset on the
        // worker-parallel kernel" mode): with cosets >= threads each coset is
        // one SERIAL task — nesting thousands of barrier scopes per coset on
        // a wide pool measured 13x slower (2^13 x 16384 cosets, 96 threads).
        ws_lde_single_poly_from_monomial_form_planned(
            monomial_form_normal_order,
            &twiddles.plain,
            lde_factor,
            &|m, o, t| fft::baby_bear_avx2::ext4::lde_coset(m, o, t, ext),
            &|m, o, t, w| fft::baby_bear_avx2::ext4::lde_coset_parallel(m, o, t, ext, w),
            worker,
            plan,
        )
    }

    fn lde_ext_poly_from_monomial_form_continuous(
        &self,
        monomial_form_normal_order: &[BabyBearExt4],
        twiddles: &Self::TwiddleSet,
        lde_factor: usize,
        worker: &Worker,
    ) -> (Box<[BabyBearExt4]>, Vec<BabyBearField>) {
        let ext = &twiddles.forward_ext;
        let plan = ext4_coset_plan(monomial_form_normal_order.len(), lde_factor, worker);
        ws_lde_single_poly_continuous_planned(
            monomial_form_normal_order,
            &twiddles.plain,
            lde_factor,
            &|m, o, t, out| fft::baby_bear_avx2::ext4::lde_coset_into(m, o, t, ext, out),
            &|m, o, t, w, out| {
                fft::baby_bear_avx2::ext4::lde_coset_parallel_into(m, o, t, ext, w, out)
            },
            worker,
            plan,
        )
    }

    fn lde_base_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[BabyBearField],
        twiddles: &Self::TwiddleSet,
        lde_factor: usize,
        worker: &Worker,
    ) -> Vec<(Box<[BabyBearField]>, BabyBearField)> {
        let ext = &twiddles.forward_ext;
        ws_lde_single_poly_from_monomial_form(
            monomial_form_normal_order,
            &twiddles.plain,
            lde_factor,
            &|m, o, t| fft::baby_bear_avx2::lde_coset_avx2(m, o, t, ext),
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
        twiddles: &Self::TwiddleSet,
        worker: &Worker,
    ) -> Vec<BabyBearExt4> {
        let inv_ext = &twiddles.inverse_ext;
        fft::baby_bear_avx2::ext4::monomial_form_from_main_domain(
            source_domain,
            &twiddles.plain.inverse_twiddles,
            inv_ext,
            worker,
        )
    }

    fn hypercube_evals_from_monomial_form(
        &self,
        monomial_form: Vec<BabyBearExt4>,
        worker: &Worker,
    ) -> Vec<BabyBearExt4> {
        fft::baby_bear_avx2::ext4::hypercube_evals_from_monomial_form(monomial_form, worker)
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

    type ExtCoeffConv = BabyBearAvx2ExtCoeffConv;
    fn ext_coeff_conv(&self, coset_len: usize, values_per_leaf: usize) -> Self::ExtCoeffConv {
        BabyBearAvx2ExtCoeffConv::new(coset_len, values_per_leaf)
    }
}
