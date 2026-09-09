//! x86-64 (AVX2) BabyBear backend: the twin of the aarch64 NEON backend —
//! 8-lane AVX2 base-field coset kernels (u64-accumulation radix-4
//! butterflies), two-elements-per-vector Ext4 kernels, combined-twiddle
//! tables built once per proving run and shared across every batched call.

use super::*;
use crate::allocation_pool::AllocationPool;
use crate::gkr::prover::backend::ConvertedLeaves;

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
/// it.
pub struct BabyBearAvx2ExtCoeffConv {
    ctx: crate::gkr::whir::ExtCoeffConvCtx<BabyBearField>,
    hp_raw: Vec<u32>,
}

impl BabyBearAvx2ExtCoeffConv {
    pub fn new(coset_len: usize, values_per_leaf: usize) -> Self {
        let ctx =
            crate::gkr::whir::ExtCoeffConvCtx::<BabyBearField>::new(coset_len, values_per_leaf);
        let hp_raw = ctx
            .high_powers_offsets
            .iter()
            .map(|x| x.raw_u32_value())
            .collect();
        Self { ctx, hp_raw }
    }

    fn avx2_applicable(&self) -> bool {
        (2..=32).contains(&self.ctx.values_per_leaf)
    }

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

    /// `coset_gen_inv^leaf * offset_inv`, raw.
    #[inline(always)]
    fn root_inv_raw(&self, offset_inv: BabyBearField, leaf_index: usize) -> u32 {
        let mut x = self.ctx.coset_gen_inv_powers[leaf_index];
        x.mul_assign(&offset_inv);
        x.raw_u32_value()
    }
}

impl ExtCoeffConversion<BabyBearField, BabyBearExt4> for BabyBearAvx2ExtCoeffConv {
    fn apply(&self, column: &mut [BabyBearExt4], offset: BabyBearField, worker: &Worker) {
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

    fn apply_serial(&self, column: &mut [BabyBearExt4], offset: BabyBearField) {
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

    fn values_per_leaf(&self) -> usize {
        self.ctx.values_per_leaf
    }

    #[inline(always)]
    fn convert_gathered_leaf(
        &self,
        offset_inv: BabyBearField,
        leaf_index: usize,
        leaf: &mut [BabyBearExt4],
    ) {
        if !self.avx2_applicable() {
            return self.ctx.convert_gathered_leaf(offset_inv, leaf_index, leaf);
        }
        fft::baby_bear_avx2::ext4::leaf_to_coeff_form(
            leaf,
            &self.hp_raw,
            self.ctx.two_inv,
            self.root_inv_raw(offset_inv, leaf_index),
        );
    }

    #[inline(always)]
    fn convert_gathered_leaves(
        &self,
        offset_inv: BabyBearField,
        first_leaf: usize,
        count: usize,
        leaves: &mut [BabyBearExt4],
    ) {
        let vpl = self.ctx.values_per_leaf;
        if !self.avx2_applicable() {
            for (w, chunk) in leaves[..count * vpl].chunks_exact_mut(vpl).enumerate() {
                self.ctx
                    .convert_gathered_leaf(offset_inv, first_leaf + w, chunk);
            }
            return;
        }
        // pairs of leaves, slot-interleaved, through the two-leaf kernel
        let mut pair = [BabyBearExt4::ZERO; 64];
        let mut w = 0;
        while w + 2 <= count {
            let (l0, l1) = (first_leaf + w, first_leaf + w + 1);
            {
                let (a, b) = leaves[w * vpl..(w + 2) * vpl].split_at(vpl);
                for k in 0..vpl {
                    pair[2 * k] = a[k];
                    pair[2 * k + 1] = b[k];
                }
            }
            fft::baby_bear_avx2::ext4::leaf_pair_to_coeff_form(
                &mut pair[..2 * vpl],
                &self.hp_raw,
                self.ctx.two_inv,
                [
                    self.root_inv_raw(offset_inv, l0),
                    self.root_inv_raw(offset_inv, l1),
                ],
            );
            let (o0, o1) = leaves[w * vpl..(w + 2) * vpl].split_at_mut(vpl);
            for k in 0..vpl {
                o0[k] = pair[2 * k];
                o1[k] = pair[2 * k + 1];
            }
            w += 2;
        }
        if w < count {
            self.convert_gathered_leaf(
                offset_inv,
                first_leaf + w,
                &mut leaves[w * vpl..(w + 1) * vpl],
            );
        }
    }

    #[inline(always)]
    fn convert_gathered_block(
        &self,
        offset_inv: BabyBearField,
        first_leaf: usize,
        count: usize,
        block: &mut [BabyBearExt4],
    ) {
        let vpl = self.ctx.values_per_leaf;
        if self.avx2_applicable() && (count == 4 || count == 2) {
            let mut roots = [0u32; 4];
            for (w, r) in roots[..count].iter_mut().enumerate() {
                *r = self.root_inv_raw(offset_inv, first_leaf + w);
            }
            if count == 4 {
                fft::baby_bear_avx2::ext4::leaf_quad_to_coeff_form(
                    &mut block[..4 * vpl],
                    &self.hp_raw,
                    self.ctx.two_inv,
                    roots,
                );
            } else {
                fft::baby_bear_avx2::ext4::leaf_pair_to_coeff_form(
                    &mut block[..2 * vpl],
                    &self.hp_raw,
                    self.ctx.two_inv,
                    [roots[0], roots[1]],
                );
            }
            return;
        }
        // generic layout shuffle around the per-leaf conversion
        let mut leaves = vec![BabyBearExt4::ZERO; count * vpl];
        for w in 0..count {
            for k in 0..vpl {
                leaves[w * vpl + k] = block[k * count + w];
            }
        }
        self.convert_gathered_leaves(offset_inv, first_leaf, count, &mut leaves);
        for w in 0..count {
            for k in 0..vpl {
                block[k * count + w] = leaves[w * vpl + k];
            }
        }
    }

    #[inline(always)]
    fn convert_leaf(
        &self,
        column: &[BabyBearExt4],
        offset_inv: BabyBearField,
        leaf_index: usize,
        out: &mut [BabyBearExt4],
    ) {
        if !self.avx2_applicable() {
            return self.ctx.convert_leaf(column, offset_inv, leaf_index, out);
        }
        for (o, off) in out.iter_mut().zip(self.ctx.offsets.iter()) {
            *o = column[off + leaf_index];
        }
        fft::baby_bear_avx2::ext4::leaf_to_coeff_form(
            out,
            &self.hp_raw,
            self.ctx.two_inv,
            self.root_inv_raw(offset_inv, leaf_index),
        );
    }

    #[inline(always)]
    fn convert_leaves(
        &self,
        column: &[BabyBearExt4],
        offset_inv: BabyBearField,
        first_leaf: usize,
        count: usize,
        out: &mut [BabyBearExt4],
    ) {
        let vpl = self.ctx.values_per_leaf;
        if !self.avx2_applicable() {
            for (w, chunk) in out[..count * vpl].chunks_exact_mut(vpl).enumerate() {
                self.ctx
                    .convert_leaf(column, offset_inv, first_leaf + w, chunk);
            }
            return;
        }
        // pairs of leaves, slot-interleaved, through the two-leaf kernel
        let mut pair = [BabyBearExt4::ZERO; 64];
        let mut w = 0;
        while w + 2 <= count {
            let (l0, l1) = (first_leaf + w, first_leaf + w + 1);
            for (k, off) in self.ctx.offsets.iter().enumerate() {
                pair[2 * k] = column[off + l0];
                pair[2 * k + 1] = column[off + l1];
            }
            fft::baby_bear_avx2::ext4::leaf_pair_to_coeff_form(
                &mut pair[..2 * vpl],
                &self.hp_raw,
                self.ctx.two_inv,
                [
                    self.root_inv_raw(offset_inv, l0),
                    self.root_inv_raw(offset_inv, l1),
                ],
            );
            let (o0, o1) = out[w * vpl..(w + 2) * vpl].split_at_mut(vpl);
            for k in 0..vpl {
                o0[k] = pair[2 * k];
                o1[k] = pair[2 * k + 1];
            }
            w += 2;
        }
        if w < count {
            self.convert_leaf(
                column,
                offset_inv,
                first_leaf + w,
                &mut out[w * vpl..(w + 1) * vpl],
            );
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

/// Size-dependent coset plan of this backend, shared by the base-commitment
/// LDE (`El = BabyBearField`, `num_tasks = columns x cosets`) and the Ext4
/// LDEs (`num_tasks = cosets`); the AVX-512 backend inherits it for
/// everything but its 2^24 strided path. Measured on the 192-core box with
/// 12 pinned 16-thread provers (the production batch shape): cosets of
/// 2^20 elements and up run EVERY coset on all threads through the blocked
/// kernels — the flat serial grid streams a 128 MB coset ~12 times from DRAM
/// under contention (2^23 x 16: all-threads 0.63 s vs serial grid 0.90 s;
/// 2^21 x 64: 0.52 vs 0.57; a 2^24 base column is larger than any L3, so
/// the number of DRAM sweeps per column is what counts: ~5 for the blocked
/// kernel vs ~14 for the serial grid) — while smaller cosets keep the
/// tasks/threads rule of [`plan_coset_grid`] (2^18 x 512: serial grid 0.17 s
/// vs all-threads 1.31 s, per-coset scope overhead).
fn coset_plan<El>(n: usize, num_tasks: usize, worker: &Worker) -> CosetGridPlan {
    if n >= (1usize << 20) {
        CosetGridPlan::ParallelWithinTask
    } else {
        plan_coset_grid::<El>(num_tasks, worker)
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
        _pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
        worker: &Worker,
    ) -> Vec<Vec<ColumnMajorCosetBoundTracePart<BabyBearField, BabyBearField>>> {
        let ext = &twiddles.forward_ext;
        let num_cols = evals.len();
        let n = evals.first().map(|c| c.len()).unwrap_or(0);
        // the blocked kernels need at least one block per column
        let blocked_min = 1usize << fft::baby_bear_avx2::avx2::BLOCK_LOG2;
        let plan = coset_plan::<BabyBearField>(n, num_cols * lde_factor, worker);
        if num_cols == 0 || n < blocked_min || plan == CosetGridPlan::FlatSerialTasks {
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

        // `ParallelWithinTask`, every column-coset on all threads: each
        // column's transform (copy + block-local levels in one sweep, radix-16
        // sweeps for the high strides) and then every coset FFT (fused
        // scale/bit-reverse/copy sweep, block-local phase, radix-16 global
        // passes) run on the whole worker, no nested scopes.
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
                        ColumnMajorCosetBoundTracePart::owned(data.into_boxed_slice(), offset)
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
        _pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
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
        _pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
        worker: &Worker,
    ) -> Vec<(Box<[BabyBearExt4]>, BabyBearField)> {
        let ext = &twiddles.forward_ext;
        let plan = coset_plan::<BabyBearExt4>(monomial_form_normal_order.len(), lde_factor, worker);
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
        _pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
        worker: &Worker,
    ) -> (Box<[BabyBearExt4]>, Vec<BabyBearField>) {
        let ext = &twiddles.forward_ext;
        let plan = coset_plan::<BabyBearExt4>(monomial_form_normal_order.len(), lde_factor, worker);
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
        _pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
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
        _pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
        worker: &Worker,
    ) -> Vec<Vec<BabyBearField>> {
        pack_polys_parallel_from_hypercubes_to_monomials(evals, pack_log2, worker)
    }

    fn monomial_form_from_hypercube_evals(
        &self,
        evals: &[BabyBearExt4],
        worker: &Worker,
    ) -> Vec<BabyBearExt4> {
        let v = super::parallel_copy_to_vec(evals, worker);
        fft::baby_bear_avx2::ext4::monomial_form_from_hypercube_evals(v, worker)
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
    type CosetLeaves<'a>
        = ConvertedLeaves<'a, BabyBearField, BabyBearExt4, BabyBearAvx2ExtCoeffConv>
    where
        Self: 'a;
    fn coset_leaves<'a>(
        &self,
        conv: &'a Self::ExtCoeffConv,
        column: &'a [BabyBearExt4],
        offset: BabyBearField,
    ) -> Self::CosetLeaves<'a> {
        ConvertedLeaves::new(conv, column, offset)
    }
    fn ext_coeff_conv(&self, coset_len: usize, values_per_leaf: usize) -> Self::ExtCoeffConv {
        BabyBearAvx2ExtCoeffConv::new(coset_len, values_per_leaf)
    }
}

#[cfg(test)]
mod gathered_conversion_tests {
    use super::*;
    use field::Rand;

    /// The gathered-leaf conversions (single and pairs) must equal the
    /// column-gathering ones for every leaf size the AVX2 kernels serve.
    #[test]
    fn avx2_gathered_conversion_matches_column() {
        let mut rng = rand::thread_rng();
        let coset_len = 1usize << 12;
        let column: Vec<BabyBearExt4> = (0..coset_len)
            .map(|_| BabyBearExt4::random_element(&mut rng))
            .collect();
        let offset = BabyBearField::random_element(&mut rng);
        let offset_inv = offset.inverse().unwrap();
        for vpl in [2usize, 4, 8, 16, 32, 64] {
            let conv = BabyBearAvx2ExtCoeffConv::new(coset_len, vpl);
            let offsets = crate::gkr::whir::offsets_vec_for_leaf_construction(coset_len, vpl);
            let num_leaves = coset_len / vpl;
            for (first, count) in [
                (0usize, 1usize),
                (3, 2),
                (5, 7),
                (num_leaves - 4, 4),
                (num_leaves - 3, 3),
            ] {
                let mut a = vec![BabyBearExt4::ZERO; count * vpl];
                ExtCoeffConversion::<BabyBearField, BabyBearExt4>::convert_leaves(
                    &conv, &column, offset_inv, first, count, &mut a,
                );
                let mut b = vec![BabyBearExt4::ZERO; count * vpl];
                for w in 0..count {
                    for (k, &off) in offsets.iter().enumerate() {
                        b[w * vpl + k] = column[off + first + w];
                    }
                }
                let mut c = b.clone();
                ExtCoeffConversion::<BabyBearField, BabyBearExt4>::convert_gathered_leaves(
                    &conv, offset_inv, first, count, &mut b,
                );
                assert_eq!(a, b, "pairs: vpl {vpl} first {first} count {count}");
                // slot-major block variant
                let mut blk = vec![BabyBearExt4::ZERO; count * vpl];
                for w in 0..count {
                    for (k, &off) in offsets.iter().enumerate() {
                        blk[k * count + w] = column[off + first + w];
                    }
                }
                ExtCoeffConversion::<BabyBearField, BabyBearExt4>::convert_gathered_block(
                    &conv, offset_inv, first, count, &mut blk,
                );
                for w in 0..count {
                    for k in 0..vpl {
                        assert_eq!(
                            blk[k * count + w],
                            a[w * vpl + k],
                            "block: vpl {vpl} first {first} count {count} leaf {w} slot {k}"
                        );
                    }
                }
                for w in 0..count {
                    ExtCoeffConversion::<BabyBearField, BabyBearExt4>::convert_gathered_leaf(
                        &conv,
                        offset_inv,
                        first + w,
                        &mut c[w * vpl..(w + 1) * vpl],
                    );
                }
                assert_eq!(a, c, "single: vpl {vpl} first {first} count {count}");
            }
        }
    }
}
