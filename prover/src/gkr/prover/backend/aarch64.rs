//! aarch64-specific BabyBear backend: NEON base-field coset kernels
//! (u64-accumulation radix-4 butterflies), combined-twiddle tables shared per
//! batched call. See the struct docs for the measured wins.

use super::*;
use crate::allocation_pool::AllocationPool;
use crate::gkr::prover::backend::ConvertedLeaves;

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
/// it.
pub struct BabyBearNeonExtCoeffConv {
    ctx: crate::gkr::whir::ExtCoeffConvCtx<BabyBearField>,
    hp_raw: Vec<u32>,
}

impl BabyBearNeonExtCoeffConv {
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

    fn neon_applicable(&self) -> bool {
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
}

impl ExtCoeffConversion<BabyBearField, BabyBearExt4> for BabyBearNeonExtCoeffConv {
    fn apply(&self, column: &mut [BabyBearExt4], offset: BabyBearField, worker: &Worker) {
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

    fn apply_serial(&self, column: &mut [BabyBearExt4], offset: BabyBearField) {
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
        self.ctx.convert_gathered_leaf(offset_inv, leaf_index, leaf);
    }

    fn convert_leaf(
        &self,
        column: &[BabyBearExt4],
        offset_inv: BabyBearField,
        leaf_index: usize,
        out: &mut [BabyBearExt4],
    ) {
        self.ctx.convert_leaf(column, offset_inv, leaf_index, out);
    }
}

/// The NEON backend's twiddle set: the plain radix-2 tables plus the
/// combined-twiddle tables for BOTH directions, all built ONCE per proving
/// run by `make_twiddles` (parallel fills) and shared across every batched
/// call — smaller transforms read prefixes, so no method ever rebuilds them.
pub struct BabyBearNeonTwiddles {
    pub plain: Twiddles<BabyBearField, Global>,
    pub forward_ext: fft::baby_bear_neon::NeonTwiddleExt,
    pub inverse_ext: fft::baby_bear_neon::NeonTwiddleExt,
}

impl TwiddleSetOps<BabyBearField> for BabyBearNeonTwiddles {
    #[inline(always)]
    fn plain(&self) -> &Twiddles<BabyBearField, Global> {
        &self.plain
    }
}

impl Backend<BabyBearField, BabyBearExt4> for BabyBearNeonWorkStealingBackend {
    type TwiddleSet = BabyBearNeonTwiddles;
    fn make_twiddles(&self, domain_size: usize, worker: &Worker) -> Self::TwiddleSet {
        let plain: Twiddles<BabyBearField, Global> = Twiddles::new(domain_size, worker);
        let forward_ext = fft::baby_bear_neon::NeonTwiddleExt::build_parallel(
            &plain.forward_twiddles,
            domain_size,
            worker,
        );
        let inverse_ext = fft::baby_bear_neon::NeonTwiddleExt::build_parallel(
            &plain.inverse_twiddles,
            domain_size,
            worker,
        );
        BabyBearNeonTwiddles {
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
        ws_lde_multiple_polys_from_hypercubes(
            evals,
            &twiddles.plain,
            lde_factor,
            &|m, o, t| fft::baby_bear_neon::lde_coset_neon(m, o, t, ext),
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
            &|m, o, t| fft::baby_bear_neon::lde_coset_neon(m, o, t, ext),
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
        use worker::rayon::prelude::*;

        let n = monomial_form_normal_order.len();
        let ext = &twiddles.forward_ext;
        let root_powers = coset_offsets::<BabyBearField>(n, lde_factor);
        let tw = &twiddles.plain.forward_twiddles[..];

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
                        ext,
                        worker,
                    );
                    (data.into_boxed_slice(), offset)
                })
                .collect()
        })
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
        // The NEON kernel composes with an enclosing rayon task through the
        // shared pool and degenerates to the serial flat schedule when every
        // thread already owns a coset (see `lde_ext_poly_from_monomial_form`),
        // so it serves as both the serial and the parallel kernel here.
        ws_lde_single_poly_continuous(
            monomial_form_normal_order,
            &twiddles.plain,
            lde_factor,
            &|m, o, t, out| {
                fft::baby_bear_neon::ext4::lde_coset_parallel_into(m, o, t, ext, worker, out)
            },
            &|m, o, t, w, out| {
                fft::baby_bear_neon::ext4::lde_coset_parallel_into(m, o, t, ext, w, out)
            },
            worker,
        )
    }

    fn lde_ext_poly_leaf_coefficients(
        &self,
        monomial_form_normal_order: &[BabyBearExt4],
        twiddles: &Self::TwiddleSet,
        lde_factor: usize,
        values_per_leaf: usize,
        _pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
        worker: &Worker,
    ) -> Option<Vec<(Box<[BabyBearExt4]>, BabyBearField)>> {
        use worker::rayon::prelude::*;

        let n = monomial_form_normal_order.len();
        if !leaf_coefficients_applicable(n, values_per_leaf) {
            return None;
        }
        let ext = &twiddles.forward_ext;
        let root_powers = coset_offsets::<BabyBearField>(n, lde_factor);
        let tw = &twiddles.plain.forward_twiddles[..];
        // same schedule as `lde_ext_poly_from_monomial_form`
        Some(worker.pool.install(|| {
            (0..lde_factor)
                .into_par_iter()
                .map(|coset| {
                    let offset = root_powers[coset];
                    let mut data: Vec<BabyBearExt4> = Vec::with_capacity(n);
                    #[allow(clippy::uninit_vec)]
                    unsafe {
                        data.set_len(n)
                    };
                    fft::baby_bear_neon::ext4::lde_coset_leaf_coefficients_parallel_into(
                        monomial_form_normal_order,
                        offset,
                        tw,
                        ext,
                        values_per_leaf,
                        worker,
                        &mut data,
                    );
                    (data.into_boxed_slice(), offset)
                })
                .collect()
        }))
    }

    fn lde_ext_poly_leaf_coefficients_continuous(
        &self,
        monomial_form_normal_order: &[BabyBearExt4],
        twiddles: &Self::TwiddleSet,
        lde_factor: usize,
        values_per_leaf: usize,
        _pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
        worker: &Worker,
    ) -> Option<(Box<[BabyBearExt4]>, Vec<BabyBearField>)> {
        let n = monomial_form_normal_order.len();
        if !leaf_coefficients_applicable(n, values_per_leaf) {
            return None;
        }
        let ext = &twiddles.forward_ext;
        Some(ws_lde_single_poly_continuous(
            monomial_form_normal_order,
            &twiddles.plain,
            lde_factor,
            &|m, o, t, out| {
                fft::baby_bear_neon::ext4::lde_coset_leaf_coefficients_parallel_into(
                    m,
                    o,
                    t,
                    ext,
                    values_per_leaf,
                    worker,
                    out,
                )
            },
            &|m, o, t, w, out| {
                fft::baby_bear_neon::ext4::lde_coset_leaf_coefficients_parallel_into(
                    m,
                    o,
                    t,
                    ext,
                    values_per_leaf,
                    w,
                    out,
                )
            },
            worker,
        ))
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
            &|m, o, t| fft::baby_bear_neon::lde_coset_neon(m, o, t, ext),
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

    fn lde_packed_polys_from_hypercubes(
        &self,
        evals: &[&[BabyBearField]],
        pack_log2: usize,
        twiddles: &Self::TwiddleSet,
        lde_factor: usize,
        _pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
        worker: &Worker,
    ) -> Vec<ColumnMajorBaseOracleForCoset<BabyBearField>> {
        let ext = &twiddles.forward_ext;
        ws_lde_packed_polys_from_hypercubes(
            evals,
            pack_log2,
            &twiddles.plain,
            lde_factor,
            &|block| {
                crate::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs_neon_bb(
                    block,
                    block.len().trailing_zeros(),
                )
            },
            &|m, o, t| fft::baby_bear_neon::lde_coset_neon(m, o, t, ext),
            &|m, o, t, w| lde_coset_canonical_parallel(m, o, t, w),
            worker,
        )
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
    type CosetLeaves<'a>
        = ConvertedLeaves<'a, BabyBearField, BabyBearExt4, BabyBearNeonExtCoeffConv>
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
        BabyBearNeonExtCoeffConv::new(coset_len, values_per_leaf)
    }
}

/// Shapes the partial-transform leaf-coefficient kernels serve: a power-of-two
/// leaf of at least 2 values, at least 4 leaves per coset, cosets of at least
/// 16 elements.
fn leaf_coefficients_applicable(n: usize, values_per_leaf: usize) -> bool {
    n >= 16 && values_per_leaf.is_power_of_two() && values_per_leaf >= 2 && values_per_leaf * 4 <= n
}

#[cfg(test)]
mod leaf_coefficient_tests {
    //! The committed WHIR leaf (multilinear = monomial coefficients of the
    //! leaf's degree-<vpl polynomial) versus the NTT state before its last
    //! log2(vpl) stages.
    use super::*;
    use crate::gkr::whir::ExtCoeffConvCtx;
    use fft::bitreverse_enumeration_inplace;

    fn rnd(st: &mut u64) -> u64 {
        *st = st.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = *st;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn rb(st: &mut u64) -> BabyBearField {
        BabyBearField::new((rnd(st) % 0x7800_0001) as u32)
    }

    #[test]
    fn partial_ntt_state_is_root_scaled_leaf_coefficients() {
        let worker = Worker::new_with_num_threads(2);
        for (log_n, vpl) in [(10usize, 32usize), (11, 32), (10, 16), (12, 8)] {
            let n = 1usize << log_n;
            let backend = BabyBearNeonWorkStealingBackend;
            let tw = backend.make_twiddles(n * 4, &worker);
            let mut st = 0x1234u64 ^ (log_n as u64) << 8 ^ vpl as u64;
            let input: Vec<BabyBearExt4> = (0..n)
                .map(|_| BabyBearExt4::from_array_of_base(core::array::from_fn(|_| rb(&mut st))))
                .collect();
            let offset = fft::domain_generator_for_size::<BabyBearField>((n * 4) as u64);
            // production: full LDE coset + in-place conversion
            let mut full = fft::baby_bear_neon::ext4::lde_coset(
                &input,
                offset,
                &tw.plain.forward_twiddles,
                &tw.forward_ext,
            );
            let ctx = ExtCoeffConvCtx::<BabyBearField>::new(n, vpl);
            ctx.apply_serial(&mut full, offset);
            // candidate: the transform stopped log2(vpl) stages early
            let skip = vpl.trailing_zeros() as usize;
            let mut partial = vec![BabyBearExt4::ZERO; n];
            fft::baby_bear_neon::ext4::lde_coset_partial_into(
                &input,
                offset,
                &tw.plain.forward_twiddles,
                &tw.forward_ext,
                skip,
                &mut partial,
            );
            // hypothesis: partial[b s + j] = root_j^{m1} * full[b s + j],
            // root_j = offset * omega^j, m1 = bitrev(b)
            let s = n / vpl;
            let omega = fft::domain_generator_for_size::<BabyBearField>(n as u64);
            let mut m1_of_block: Vec<usize> = (0..vpl).collect();
            bitreverse_enumeration_inplace(&mut m1_of_block);
            let mut mismatches = 0usize;
            for b in 0..vpl {
                let m1 = m1_of_block[b];
                for j in 0..s {
                    let mut root = omega.pow(j as u32);
                    root.mul_assign(&offset);
                    let factor = root.pow(m1 as u32);
                    let mut expect = full[b * s + j];
                    expect.mul_assign_by_base(&factor);
                    if expect != partial[b * s + j] {
                        if mismatches < 6 {
                            let mut ratio = partial[b * s + j];
                            ratio.mul_assign(&full[b * s + j].inverse().unwrap());
                            println!(
                                "log_n {log_n} vpl {vpl} b {b} (m1 {m1}) j {j}: partial/full = {:?}, hypothesised factor {:?}",
                                ratio, factor
                            );
                        }
                        mismatches += 1;
                    }
                }
            }
            assert_eq!(
                mismatches, 0,
                "log_n {log_n} vpl {vpl}: {mismatches} mismatches"
            );
        }
    }

    fn convert_reference(
        cosets: &mut [(Box<[BabyBearExt4]>, BabyBearField)],
        n: usize,
        vpl: usize,
    ) {
        let ctx = ExtCoeffConvCtx::<BabyBearField>::new(n, vpl);
        for (c, o) in cosets.iter_mut() {
            ctx.apply_serial(&mut c[..], *o);
        }
    }

    #[test]
    fn leaf_coefficient_kernels_match_production_conversion() {
        let worker = Worker::new_with_num_threads(3);
        for (log_n, vpl) in [
            (10usize, 32usize),
            (11, 32),
            (13, 32),
            (13, 16),
            (12, 8),
            (10, 2),
        ] {
            let n = 1usize << log_n;
            let backend = BabyBearNeonWorkStealingBackend;
            let tw = backend.make_twiddles(n * 4, &worker);
            let mut st = 0x55u64 ^ (log_n as u64) << 8 ^ vpl as u64;
            let input: Vec<BabyBearExt4> = (0..n)
                .map(|_| BabyBearExt4::from_array_of_base(core::array::from_fn(|_| rb(&mut st))))
                .collect();
            let gen = fft::domain_generator_for_size::<BabyBearField>((n * 4) as u64);
            for offset in [BabyBearField::ONE, gen, gen.pow(3)] {
                let mut full = fft::baby_bear_neon::ext4::lde_coset(
                    &input,
                    offset,
                    &tw.plain.forward_twiddles,
                    &tw.forward_ext,
                );
                ExtCoeffConvCtx::<BabyBearField>::new(n, vpl).apply_serial(&mut full, offset);
                let mut serial = vec![BabyBearExt4::ZERO; n];
                fft::baby_bear_neon::ext4::lde_coset_leaf_coefficients_into(
                    &input,
                    offset,
                    &tw.plain.forward_twiddles,
                    &tw.forward_ext,
                    vpl,
                    &mut serial,
                );
                assert_eq!(serial, full, "serial log_n {log_n} vpl {vpl}");
                let mut par = vec![BabyBearExt4::ZERO; n];
                fft::baby_bear_neon::ext4::lde_coset_leaf_coefficients_parallel_into(
                    &input,
                    offset,
                    &tw.plain.forward_twiddles,
                    &tw.forward_ext,
                    vpl,
                    &worker,
                    &mut par,
                );
                assert_eq!(par, full, "parallel log_n {log_n} vpl {vpl}");
            }
        }
    }

    #[test]
    fn backend_leaf_coefficients_match_converted_lde() {
        let worker = Worker::new_with_num_threads(3);
        let pool = crate::allocation_pool::default_pool_for::<BabyBearField, BabyBearExt4>();
        for (log_n, lde, vpl) in [(13usize, 4usize, 32usize), (10, 16, 32), (12, 2, 8)] {
            let n = 1usize << log_n;
            let backend = BabyBearNeonWorkStealingBackend;
            let tw = backend.make_twiddles(n * lde, &worker);
            let mut st = 0x77u64 ^ (log_n as u64) << 8 ^ lde as u64;
            let mono: Vec<BabyBearExt4> = (0..n)
                .map(|_| BabyBearExt4::from_array_of_base(core::array::from_fn(|_| rb(&mut st))))
                .collect();
            let mut reference =
                backend.lde_ext_poly_from_monomial_form(&mono, &tw, lde, &*pool, &worker);
            convert_reference(&mut reference, n, vpl);
            let got = backend
                .lde_ext_poly_leaf_coefficients(&mono, &tw, lde, vpl, &*pool, &worker)
                .expect("applicable shape");
            assert_eq!(got.len(), reference.len());
            for (g, r) in got.iter().zip(reference.iter()) {
                assert_eq!(g.1, r.1);
                assert_eq!(
                    &g.0[..],
                    &r.0[..],
                    "boxed log_n {log_n} lde {lde} vpl {vpl}"
                );
            }
            let (buf, offsets) = backend
                .lde_ext_poly_leaf_coefficients_continuous(&mono, &tw, lde, vpl, &*pool, &worker)
                .expect("applicable shape");
            for (k, chunk) in buf.chunks(n).enumerate() {
                assert_eq!(offsets[k], reference[k].1);
                assert_eq!(
                    chunk,
                    &reference[k].0[..],
                    "continuous log_n {log_n} lde {lde} vpl {vpl} coset {k}"
                );
            }
        }
    }
}
