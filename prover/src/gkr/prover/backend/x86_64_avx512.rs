//! x86-64 AVX-512 BabyBear backend: the AVX2 backend plus the strided-gather
//! base-commitment LDE of `fft::baby_bear_avx512` — a partial 2^20 transform
//! per column, then per coset one strided gather sweep (block-local stages in
//! 2^14 blocks) and one radix-1024 global sweep, writing block-padded
//! codewords (block `b` at `b * PADDED_GEOMETRY.stride()`) straight into pooled,
//! 64-byte aligned buffers. Two DRAM sweeps per coset instead of four, no
//! materialized monomials, no fresh allocations after the first proof.
//! Values are byte-identical to the AVX2 pipeline (parity test below); only
//! the storage layout differs, which the tree builder and the query paths
//! address through [`ColumnLayout::PaddedBlocks`]. The radix-1024 pass is a
//! 2^24-only kernel, so other sizes (and a missing `avx512f`, or
//! `FFT_STRIDED=0`) take the AVX2 path unchanged.

use super::x86_64::{
    BabyBearAvx2ExtCoeffConv, BabyBearAvx2Twiddles, BabyBearAvx2WorkStealingBackend,
};
use super::*;
use crate::allocation_pool::x86_64_baby_bear::PADDED_GEOMETRY;
use crate::allocation_pool::{AllocationPool, ColumnLayout};

/// Trace length of the strided pipeline's radix-1024 global pass.
const STRIDED_LOG_N: u32 = 24;
/// Chunk stride of the partial transform: the 16 read streams of the gather
/// pass must not share L1/L2 sets.
const STRIDED_CHUNK_STRIDE: usize = (1 << (STRIDED_LOG_N - 4)) + 1088;

/// The AVX2 work-stealing backend with the AVX-512 strided base LDE on top.
/// `Default` detects `avx512f` at runtime (and honours `FFT_STRIDED=0`).
#[derive(Clone, Copy, Debug)]
pub struct BabyBearAvx512WorkStealingBackend {
    strided: bool,
    /// Commit the 2^23-value WHIR oracle by coefficient through the strided
    /// pipeline (see [`Backend::by_coefficient_lde_len`]); needs `strided`.
    by_coefficient: bool,
    inner: BabyBearAvx2WorkStealingBackend,
}

impl BabyBearAvx512WorkStealingBackend {
    /// `strided` requires `avx512f` (panics otherwise).
    pub fn new(strided: bool) -> Self {
        assert!(
            !strided || is_x86_feature_detected!("avx512f"),
            "BabyBearAvx512WorkStealingBackend: avx512f requested but not available"
        );
        Self {
            strided,
            by_coefficient: strided,
            inner: BabyBearAvx2WorkStealingBackend,
        }
    }
    /// The strided base LDE when the CPU has `avx512f` and env `FFT_STRIDED`
    /// is not `0`; the plain AVX2 backend otherwise. The by-coefficient WHIR
    /// oracle rides on the strided pipeline unless env `WHIR_BY_COEFF` is `0`.
    pub fn detect() -> Self {
        let wanted = std::env::var("FFT_STRIDED")
            .map(|v| v != "0")
            .unwrap_or(true);
        let by_coefficient = std::env::var("WHIR_BY_COEFF")
            .map(|v| v != "0")
            .unwrap_or(true);
        Self::new(wanted && is_x86_feature_detected!("avx512f")).with_by_coefficient(by_coefficient)
    }
    /// Enable/disable the by-coefficient WHIR oracle (a no-op without `strided`).
    pub fn with_by_coefficient(mut self, on: bool) -> Self {
        self.by_coefficient = on && self.strided;
        self
    }
    pub fn uses_strided(&self) -> bool {
        self.strided
    }
    pub fn uses_by_coefficient(&self) -> bool {
        self.by_coefficient
    }
}

impl Default for BabyBearAvx512WorkStealingBackend {
    fn default() -> Self {
        Self::detect()
    }
}

/// The strided pipeline over every column: `result[coset][column]` in the
/// block-padded layout, all buffers from the pool.
fn strided_base_lde(
    evals: &[&[BabyBearField]],
    twiddles: &BabyBearAvx2Twiddles,
    lde_factor: usize,
    pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
    worker: &Worker,
) -> Option<Vec<Vec<ColumnMajorCosetBoundTracePart<BabyBearField, BabyBearField>>>> {
    use fft::baby_bear_avx512::{
        out_len, strided_gather_pass_into, strided_global_phase, transform_partial_chunked_into,
        StridedCfg,
    };
    let n = 1usize << STRIDED_LOG_N;
    let cfg = StridedCfg {
        stream: true,
        r256: true,
        out_block_stride: PADDED_GEOMETRY.stride(),
        group: 1,
        prefetch: false,
        blk_log2: PADDED_GEOMETRY.block_log2,
    };
    assert_eq!(
        out_len(STRIDED_LOG_N, cfg.blk_log2, cfg.out_block_stride),
        PADDED_GEOMETRY.padded_len(n),
        "the pool's padded layout must match the strided kernel's output layout"
    );
    let root_powers = coset_offsets::<BabyBearField>(n, lde_factor);
    let tw = &twiddles.plain.forward_twiddles[..];
    let tw_raw: &[u32] =
        unsafe { core::slice::from_raw_parts(tw.as_ptr() as *const u32, tw.len()) };
    let ext = &twiddles.forward_ext;

    // scratch for the partially transformed column: 16 chunks at the padded
    // stride, carved from the same size class as the outputs
    let mut part = pool.alloc_base(n, ColumnLayout::PaddedBlocks(PADDED_GEOMETRY));
    if part.as_ptr() as usize % 64 != 0 {
        // a pool without 64-byte windows (the generic one): the streaming
        // stores of the strided kernels need them, so take the AVX2 path
        pool.give_base(part);
        return None;
    }
    assert!(part.len() >= 16 * STRIDED_CHUNK_STRIDE);
    let part_ptr = part.as_mut_ptr() as *mut u32;
    let part_len = 16 * STRIDED_CHUNK_STRIDE;

    let mut result: Vec<Vec<ColumnMajorCosetBoundTracePart<BabyBearField, BabyBearField>>> = (0
        ..lde_factor)
        .map(|_| Vec::with_capacity(evals.len()))
        .collect();
    for col in evals.iter() {
        assert_eq!(col.len(), n, "the strided base LDE is a 2^24 kernel");
        let col_raw: &[u32] = unsafe { core::slice::from_raw_parts(col.as_ptr() as *const u32, n) };
        unsafe {
            let part_mut = core::slice::from_raw_parts_mut(part_ptr, part_len);
            transform_partial_chunked_into(
                col_raw,
                part_mut,
                STRIDED_LOG_N,
                STRIDED_LOG_N - 4,
                STRIDED_CHUNK_STRIDE,
                true,
                worker,
            );
        }
        let part_ref: &[u32] = unsafe { core::slice::from_raw_parts(part_ptr, part_len) };
        for (coset, &offset) in root_powers.iter().enumerate() {
            let mut out = pool.alloc_base(n, ColumnLayout::PaddedBlocks(PADDED_GEOMETRY));
            assert_eq!(out.len(), PADDED_GEOMETRY.padded_len(n));
            assert_eq!(
                out.as_ptr() as usize % 64,
                0,
                "streaming stores need a 64-byte aligned codeword buffer"
            );
            let out_u32: &mut [u32] =
                unsafe { core::slice::from_raw_parts_mut(out.as_mut_ptr() as *mut u32, out.len()) };
            unsafe {
                strided_gather_pass_into(
                    part_ref,
                    STRIDED_CHUNK_STRIDE,
                    STRIDED_LOG_N,
                    offset,
                    tw_raw,
                    &ext.ao,
                    &ext.bo,
                    out_u32,
                    worker,
                    cfg,
                );
                strided_global_phase(
                    out_u32,
                    STRIDED_LOG_N,
                    tw_raw,
                    &ext.ao,
                    &ext.bo,
                    worker,
                    cfg,
                );
            }
            // the kernels never touch the gaps between blocks: zero them so
            // the whole window is initialized memory
            for b in 0..(n >> PADDED_GEOMETRY.block_log2) {
                let g = b * PADDED_GEOMETRY.stride() + PADDED_GEOMETRY.block();
                out_u32[g..g + PADDED_GEOMETRY.pad].fill(0);
            }
            result[coset].push(unsafe {
                ColumnMajorCosetBoundTracePart::pooled(
                    out,
                    offset,
                    ColumnLayout::PaddedBlocks(PADDED_GEOMETRY),
                )
            });
        }
    }
    pool.give_base(part);
    Some(result)
}

impl Backend<BabyBearField, BabyBearExt4> for BabyBearAvx512WorkStealingBackend {
    type TwiddleSet = BabyBearAvx2Twiddles;
    fn make_twiddles(&self, domain_size: usize, worker: &Worker) -> Self::TwiddleSet {
        self.inner.make_twiddles(domain_size, worker)
    }

    fn lde_multiple_polys_from_hypercubes(
        &self,
        evals: &[&[BabyBearField]],
        twiddles: &Self::TwiddleSet,
        lde_factor: usize,
        pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
        worker: &Worker,
    ) -> Vec<Vec<ColumnMajorCosetBoundTracePart<BabyBearField, BabyBearField>>> {
        let n = evals.first().map(|c| c.len()).unwrap_or(0);
        if self.strided && n == (1usize << STRIDED_LOG_N) {
            if let Some(result) = strided_base_lde(evals, twiddles, lde_factor, pool, worker) {
                return result;
            }
            static WARNED: std::sync::Once = std::sync::Once::new();
            WARNED.call_once(|| {
                eprintln!(
                    "[x86 backend] the pool has no 64-byte aligned windows: strided base LDE disabled, AVX2 path used"
                )
            });
        }
        self.inner
            .lde_multiple_polys_from_hypercubes(evals, twiddles, lde_factor, pool, worker)
    }

    fn by_coefficient_lde_len(&self) -> Option<usize> {
        if self.by_coefficient {
            Some(1usize << STRIDED_LOG_N)
        } else {
            None
        }
    }

    fn lde_packed_monomials_into_cosets(
        &self,
        monomials: Vec<Vec<BabyBearField>>,
        twiddles: &Self::TwiddleSet,
        lde_factor: usize,
        pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
        worker: &Worker,
    ) -> Vec<ColumnMajorBaseOracleForCoset<BabyBearField>> {
        self.inner
            .lde_packed_monomials_into_cosets(monomials, twiddles, lde_factor, pool, worker)
    }

    fn lde_ext_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[BabyBearExt4],
        twiddles: &Self::TwiddleSet,
        lde_factor: usize,
        pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
        worker: &Worker,
    ) -> Vec<(Box<[BabyBearExt4]>, BabyBearField)> {
        self.inner.lde_ext_poly_from_monomial_form(
            monomial_form_normal_order,
            twiddles,
            lde_factor,
            pool,
            worker,
        )
    }

    fn lde_ext_poly_from_monomial_form_continuous(
        &self,
        monomial_form_normal_order: &[BabyBearExt4],
        twiddles: &Self::TwiddleSet,
        lde_factor: usize,
        pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
        worker: &Worker,
    ) -> (Box<[BabyBearExt4]>, Vec<BabyBearField>) {
        self.inner.lde_ext_poly_from_monomial_form_continuous(
            monomial_form_normal_order,
            twiddles,
            lde_factor,
            pool,
            worker,
        )
    }

    fn lde_base_poly_from_monomial_form(
        &self,
        monomial_form_normal_order: &[BabyBearField],
        twiddles: &Self::TwiddleSet,
        lde_factor: usize,
        pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
        worker: &Worker,
    ) -> Vec<(Box<[BabyBearField]>, BabyBearField)> {
        self.inner.lde_base_poly_from_monomial_form(
            monomial_form_normal_order,
            twiddles,
            lde_factor,
            pool,
            worker,
        )
    }

    fn pack_polys_from_hypercubes_to_monomials(
        &self,
        evals: &[&[BabyBearField]],
        pack_log2: usize,
        pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
        worker: &Worker,
    ) -> Vec<Vec<BabyBearField>> {
        self.inner
            .pack_polys_from_hypercubes_to_monomials(evals, pack_log2, pool, worker)
    }

    fn monomial_form_from_main_domain(
        &self,
        source_domain: Vec<BabyBearExt4>,
        twiddles: &Self::TwiddleSet,
        pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
        worker: &Worker,
    ) -> Vec<BabyBearExt4> {
        self.inner
            .monomial_form_from_main_domain(source_domain, twiddles, pool, worker)
    }

    fn hypercube_evals_from_monomial_form(
        &self,
        monomial_form: Vec<BabyBearExt4>,
        pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
        worker: &Worker,
    ) -> Vec<BabyBearExt4> {
        self.inner
            .hypercube_evals_from_monomial_form(monomial_form, pool, worker)
    }

    fn update_eq_poly(
        &self,
        eq_poly: &mut [BabyBearExt4],
        ood_samples: &[(BabyBearExt4, BabyBearExt4)],
        in_domain_samples: &[(BabyBearField, BabyBearExt4)],
        worker: &Worker,
    ) {
        self.inner
            .update_eq_poly(eq_poly, ood_samples, in_domain_samples, worker)
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
        self.inner.ext_coeff_conv(coset_len, values_per_leaf)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::Rand;

    /// The strided pipeline's block-padded codeword equals the AVX2 codeword
    /// value for value (one 2^24 column, LDE 2), and the padded buffers come
    /// back out of the pool.
    #[test]
    fn avx512_strided_base_lde_matches_avx2() {
        if !is_x86_feature_detected!("avx512f") {
            eprintln!("avx512f not available: skipping");
            return;
        }
        let worker = Worker::new_with_num_threads(8);
        let n = 1usize << STRIDED_LOG_N;
        let mut rng = rand::thread_rng();
        let col: Vec<BabyBearField> = (0..n)
            .map(|_| BabyBearField::random_element(&mut rng))
            .collect();
        let cols: Vec<&[BabyBearField]> = vec![&col[..]];
        let avx2 = BabyBearAvx2WorkStealingBackend;
        let twiddles = avx2.make_twiddles(2 * n, &worker);
        let pool = crate::allocation_pool::X86BabyBearAllocationPool::new();
        let strided = BabyBearAvx512WorkStealingBackend::new(true);
        // the base commits' factor 2 and the by-coefficient WHIR oracle's 8
        for lde_factor in [2usize, 8] {
            let reference = avx2
                .lde_multiple_polys_from_hypercubes(&cols, &twiddles, lde_factor, &pool, &worker);
            let got = strided
                .lde_multiple_polys_from_hypercubes(&cols, &twiddles, lde_factor, &pool, &worker);
            assert_eq!(got.len(), reference.len());
            for (coset, (a, b)) in got.iter().zip(reference.iter()).enumerate() {
                assert_eq!(a.len(), 1);
                assert_eq!(a[0].offset, b[0].offset);
                assert_eq!(a[0].layout, ColumnLayout::PaddedBlocks(PADDED_GEOMETRY));
                assert_eq!(a[0].len(), n);
                let x = a[0].to_vec();
                let y = b[0].to_vec();
                if x != y {
                    let idx = x.iter().zip(y.iter()).position(|(p, q)| p != q).unwrap();
                    panic!("lde {lde_factor} coset {coset}: first mismatch at natural index {idx}");
                }
            }
        }
        let got = strided.lde_multiple_polys_from_hypercubes(&cols, &twiddles, 2, &pool, &worker);
        // the outputs return to the pool once dropped
        let misses_before = pool.stats().misses;
        drop(got);
        // (the trace parts hold Arcs: dropping the last owner frees, releasing
        // goes through `AllocationType::release`; here we just check the
        // second run reuses the scratch buffer)
        let got2 = strided.lde_multiple_polys_from_hypercubes(&cols, &twiddles, 2, &pool, &worker);
        let misses_after = pool.stats().misses;
        assert!(misses_after <= misses_before + 2, "scratch reuse expected");
        drop(got2);
    }
}
