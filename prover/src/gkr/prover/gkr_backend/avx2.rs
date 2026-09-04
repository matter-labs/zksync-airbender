//! x86-64 AVX2 + BabyBear/Ext4 specialization, the twin of the aarch64
//! [`NeonGKRBackend`](super::neon::NeonGKRBackend): AVX2 per-relation
//! forward ops, the AVX2 fused-sweep chunk kernels of the dimension-reducing
//! backward path (two `Ext4` elements per vector, the `[v0, vinf]` tri row
//! packed into one 256-bit slot), and the AVX2 SoA window-3 chain executor.
//! Implemented for the concrete BabyBear pair only; every value it produces
//! is byte-identical to the naive backend's.

use std::collections::BTreeMap;

use super::super::dimension_reduction::forward::{
    evaluate_dimension_reduction_forward_with, DimensionReducingInputOutput,
};
use super::super::dimension_reduction::lsb_backward::{FoldBufferTracker, LsbDimReducingRelation};
use super::super::{GKRAddress, GKRStorage, SendConstPtr, SumcheckIntermediateProofValues};
use super::{DimReducingSumcheckScratch, GKRBackend};
use crate::gkr::prover::sumcheck_loop::windowed_mode::avx2 as k;
use crate::gkr::prover::sumcheck_loop::windowed_mode::{lsb_avx2, lsb_generic};
use crate::gkr::prover::EvaluationPointEntry;
use crate::gkr::sumcheck::evaluation_kernels::GKRInputs;
use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use core::arch::x86_64::*;
use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};
use field::{Field, FieldExtension, PrimeField};
use transcript::Transcript;
use worker::Worker;

/// AVX2 forward pairwise product: `out[i] = in[2i] (x) in[2i+1]`, two
/// outputs per vector.
pub fn forward_pairwise_avx2<F: PrimeField, E: FieldExtension<F> + Field>(
    gkr_storage: &mut GKRStorage<F, E>,
    input: GKRAddress,
    output: GKRAddress,
    expected_output_layer: usize,
    input_trace_len: usize,
    worker: &Worker,
) {
    use crate::gkr::PAR_THRESHOLD;
    let output_trace_len = input_trace_len / 2;
    unsafe {
        let inputs = GKRInputs {
            inputs_in_base: Vec::new(),
            inputs_in_extension: vec![input],
            outputs_in_base: Vec::new(),
            outputs_in_extension: Vec::new(),
        };
        let sources = gkr_storage.get_for_sumcheck_round_0(&inputs);
        let src: &[E] = sources.extension_field_inputs[0].current_values();
        let mut destination = Box::<[E]>::new_uninit_slice(output_trace_len);
        let src_addr = crate::gkr::prover::SendConstPtr(src.as_ptr());
        let dst_addr = crate::gkr::prover::SendPtr(destination.as_mut_ptr());
        worker.scope_with_threshold(output_trace_len, PAR_THRESHOLD, |scope, geometry| {
            for thread_idx in 0..geometry.num_chunks {
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                let chunk_size = geometry.get_chunk_size(thread_idx);
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let sp = src_addr.get() as *const BabyBearExt4;
                    let dp = dst_addr.get() as *mut BabyBearExt4;
                    let r11v = k::r11v();
                    let end = chunk_start + chunk_size;
                    let mut i = chunk_start;
                    while i + 1 < end {
                        // in[2i], in[2i+1] | in[2i+2], in[2i+3]
                        let v0 = k::load2(sp.add(2 * i));
                        let v1 = k::load2(sp.add(2 * i + 2));
                        k::store2(
                            dp.add(i),
                            k::ext_mul2(k::lows(v0, v1), k::highs(v0, v1), r11v),
                        );
                        i += 2;
                    }
                    if i < end {
                        let v = k::load2(sp.add(2 * i));
                        k::store1(dp.add(i), k::ext_mul2(k::dup_lo(v), k::dup_hi(v), r11v));
                    }
                })
            }
        });
        let values = destination.assume_init();
        output.assert_as_layer(expected_output_layer);
        gkr_storage.insert_extension_at_layer(
            expected_output_layer,
            output,
            crate::gkr::sumcheck::access_and_fold::ExtensionFieldPoly::new(values),
        );
    }
}

/// AVX2 forward logup fraction add, two outputs per vector.
pub fn forward_logup_avx2<F: PrimeField, E: FieldExtension<F> + Field>(
    gkr_storage: &mut GKRStorage<F, E>,
    inputs: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    expected_output_layer: usize,
    input_trace_len: usize,
    worker: &Worker,
) {
    use crate::gkr::PAR_THRESHOLD;
    let output_trace_len = input_trace_len / 2;
    unsafe {
        let gkr_inputs = GKRInputs {
            inputs_in_base: Vec::new(),
            inputs_in_extension: inputs.to_vec(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: Vec::new(),
        };
        let sources = gkr_storage.get_for_sumcheck_round_0(&gkr_inputs);
        let n_src: &[E] = sources.extension_field_inputs[0].current_values();
        let d_src: &[E] = sources.extension_field_inputs[1].current_values();
        let mut num_dst = Box::<[E]>::new_uninit_slice(output_trace_len);
        let mut den_dst = Box::<[E]>::new_uninit_slice(output_trace_len);
        let n_addr = crate::gkr::prover::SendConstPtr(n_src.as_ptr());
        let d_addr = crate::gkr::prover::SendConstPtr(d_src.as_ptr());
        let nd_addr = crate::gkr::prover::SendPtr(num_dst.as_mut_ptr());
        let dd_addr = crate::gkr::prover::SendPtr(den_dst.as_mut_ptr());
        worker.scope_with_threshold(output_trace_len, PAR_THRESHOLD, |scope, geometry| {
            for thread_idx in 0..geometry.num_chunks {
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                let chunk_size = geometry.get_chunk_size(thread_idx);
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let np = n_addr.get() as *const BabyBearExt4;
                    let dp = d_addr.get() as *const BabyBearExt4;
                    let ndp = nd_addr.get() as *mut BabyBearExt4;
                    let ddp = dd_addr.get() as *mut BabyBearExt4;
                    let r11v = k::r11v();
                    let end = chunk_start + chunk_size;
                    let mut i = chunk_start;
                    // num = n0 (x) d1 + n1 (x) d0, den = d0 (x) d1
                    while i + 1 < end {
                        let n01 = k::load2(np.add(2 * i));
                        let n23 = k::load2(np.add(2 * i + 2));
                        let d01 = k::load2(dp.add(2 * i));
                        let d23 = k::load2(dp.add(2 * i + 2));
                        let n0 = k::lows(n01, n23);
                        let n1 = k::highs(n01, n23);
                        let d0 = k::lows(d01, d23);
                        let d1 = k::highs(d01, d23);
                        let num = k::add8(k::ext_mul2(n0, d1, r11v), k::ext_mul2(n1, d0, r11v));
                        k::store2(ndp.add(i), num);
                        k::store2(ddp.add(i), k::ext_mul2(d0, d1, r11v));
                        i += 2;
                    }
                    if i < end {
                        let n = k::load2(np.add(2 * i));
                        let d = k::load2(dp.add(2 * i));
                        let num = k::add8(
                            k::ext_mul2(k::dup_lo(n), k::dup_hi(d), r11v),
                            k::ext_mul2(k::dup_hi(n), k::dup_lo(d), r11v),
                        );
                        k::store1(ndp.add(i), num);
                        k::store1(ddp.add(i), k::ext_mul2(k::dup_lo(d), k::dup_hi(d), r11v));
                    }
                })
            }
        });
        for (addr, dst) in outputs
            .into_iter()
            .zip([num_dst.assume_init(), den_dst.assume_init()].into_iter())
        {
            addr.assert_as_layer(expected_output_layer);
            gkr_storage.insert_extension_at_layer(
                expected_output_layer,
                addr,
                crate::gkr::sumcheck::access_and_fold::ExtensionFieldPoly::new(dst),
            );
        }
    }
}

#[inline(always)]
fn as_bb<E: Field>(c: &E) -> &BabyBearExt4 {
    unsafe { &*(c as *const E as *const _) }
}

enum RelM {
    Pair {
        input: GKRAddress,
        output: GKRAddress,
        a: k::ExtMatrix2,
    },
    Logup {
        num: GKRAddress,
        den: GKRAddress,
        num_output: GKRAddress,
        den_output: GKRAddress,
        an: k::ExtMatrix2,
        ad: k::ExtMatrix2,
    },
}

fn rel_matrices<E: Field>(relations: &[LsbDimReducingRelation<E>]) -> Vec<RelM> {
    relations
        .iter()
        .map(|rel| match rel {
            LsbDimReducingRelation::PairwiseProduct {
                input,
                output,
                alpha,
            } => RelM::Pair {
                input: *input,
                output: *output,
                a: k::ExtMatrix2::new(as_bb(alpha)),
            },
            LsbDimReducingRelation::LogupPair {
                num,
                den,
                num_output,
                den_output,
                alpha_num,
                alpha_den,
            } => RelM::Logup {
                num: *num,
                den: *den,
                num_output: *num_output,
                den_output: *den_output,
                an: k::ExtMatrix2::new(as_bb(alpha_num)),
                ad: k::ExtMatrix2::new(as_bb(alpha_den)),
            },
        })
        .collect()
}

/// The 4 pair values of row `j` (elements `4j .. 4j+4`) as `([a0 | b0],
/// [a1 | b1])`, no pending fold.
#[inline(always)]
unsafe fn fetch4_direct(src: *const BabyBearExt4, j: usize) -> (__m256i, __m256i) {
    (k::load2(src.add(4 * j)), k::load2(src.add(4 * j + 2)))
}

/// Fold-on-read fetch of the CURRENT 4 pair values of row `j`: the pending
/// challenge's matrix applied in-register, the folded values stored to `dst`
/// for the next round while hot.
#[inline(always)]
unsafe fn fetch4_fold(
    src: *const BabyBearExt4,
    dst: *mut BabyBearExt4,
    fm: &k::ExtMatrix2,
    j: usize,
) -> (__m256i, __m256i) {
    // yy = 0: lo = src[8j + b], hi = src[8j + 2 + b]; out -> dst[4j + b]
    let lo = k::load2(src.add(8 * j));
    let hi = k::load2(src.add(8 * j + 2));
    let v01 = k::add8(lo, k::mat_mul2(fm, k::sub8(hi, lo)));
    k::store2(dst.add(4 * j), v01);
    // yy = 1: lo = src[8j + 4 + b], hi = src[8j + 6 + b]; out -> dst[4j + 2 + b]
    let lo = k::load2(src.add(8 * j + 4));
    let hi = k::load2(src.add(8 * j + 6));
    let v23 = k::add8(lo, k::mat_mul2(fm, k::sub8(hi, lo)));
    k::store2(dst.add(4 * j + 2), v23);
    (v01, v23)
}

/// `[out_j | (a1 - a0) (x) (b1 - b0)]`-style merge: low half from `lo_src`,
/// high half from `hi_src`.
#[inline(always)]
unsafe fn merge_halves(lo_src: __m256i, hi_src: __m256i) -> __m256i {
    _mm256_blend_epi32::<0xF0>(lo_src, hi_src)
}

/// Fused T-dot over the chunk's hot tri slots (`[v0 | vinf]` per row).
#[inline(always)]
unsafe fn tdot<E: Field>(
    tri: *const u8,
    rows: usize,
    t_ptr: SendConstPtr<E>,
    chunk_start: usize,
) -> [E; 2] {
    let r11v = k::r11v();
    let t_tab = t_ptr.0 as *const BabyBearExt4;
    let mut acc = _mm256_setzero_si256();
    for jj in 0..rows {
        let w = k::bcast_elem(&*t_tab.add(chunk_start + jj));
        let t = _mm256_loadu_si256(tri.add(32 * jj) as *const __m256i);
        acc = k::add8(acc, k::ext_mul2(w, t, r11v));
    }
    let mut raw = [BabyBearExt4::ZERO; 2];
    k::store2(raw.as_mut_ptr(), acc);
    [
        *(raw.as_ptr() as *const E),
        *(raw.as_ptr().add(1) as *const E),
    ]
}

/// AVX2 chunk kernel of the INITIAL round (see `neon_initial_chunk` for the
/// contract): gate values at `X = 0` from the OUTPUT layer, `X = inf` from
/// the input differences; nothing is folded.
///
/// # Safety
///
/// Same pointer contract as `scalar_initial_chunk`; `scratch` must hold
/// `chunk_size` 32-byte slots; `E` must be BabyBearExt4.
pub unsafe fn avx2_initial_chunk<E: Field>(
    inputs: &BTreeMap<GKRAddress, &[E]>,
    outputs: &BTreeMap<GKRAddress, &[E]>,
    relations: &[LsbDimReducingRelation<E>],
    t_ptr: SendConstPtr<E>,
    chunk_start: usize,
    chunk_size: usize,
    scratch: crate::gkr::prover::SendPtr<[u128; 2]>,
) -> [E; 2] {
    let r11v = k::r11v();
    let rels = rel_matrices(relations);
    if rels.is_empty() {
        return [E::ZERO; 2];
    }
    let tri = scratch.0 as *mut u8;
    let slot = |jj: usize| tri.add(32 * jj) as *mut __m256i;

    let mut first = true;
    for rel in rels.iter() {
        match rel {
            RelM::Pair { input, output, a } => {
                let src = inputs[input].as_ptr() as *const BabyBearExt4;
                let out = outputs[output].as_ptr() as *const BabyBearExt4;
                for jj in 0..chunk_size {
                    let j = chunk_start + jj;
                    let (ab0, ab1) = fetch4_direct(src, j);
                    // X = inf: (a1 - a0) (x) (b1 - b0)
                    let d = k::sub8(ab1, ab0);
                    let prod = k::ext_mul2(k::dup_lo(d), k::dup_hi(d), r11v);
                    // X = 0: the output layer already holds the gate value
                    let x = merge_halves(k::load1(out.add(2 * j)), prod);
                    let t = k::mat_mul2(a, x);
                    if first {
                        _mm256_storeu_si256(slot(jj), t);
                    } else {
                        _mm256_storeu_si256(slot(jj), k::add8(_mm256_loadu_si256(slot(jj)), t));
                    }
                }
            }
            RelM::Logup {
                num,
                den,
                num_output,
                den_output,
                an,
                ad,
            } => {
                let n_src = inputs[num].as_ptr() as *const BabyBearExt4;
                let d_src = inputs[den].as_ptr() as *const BabyBearExt4;
                let n_out = outputs[num_output].as_ptr() as *const BabyBearExt4;
                let d_out = outputs[den_output].as_ptr() as *const BabyBearExt4;
                for jj in 0..chunk_size {
                    let j = chunk_start + jj;
                    let (n01, n23) = fetch4_direct(n_src, j);
                    let (d01, d23) = fetch4_direct(d_src, j);
                    // X = inf: the fraction-add on the differences
                    let dn = k::sub8(n23, n01); // [dn0 | dn1]
                    let dd = k::sub8(d23, d01); // [dd0 | dd1]
                    let numi = k::add8(
                        k::ext_mul2(k::dup_lo(dn), k::dup_hi(dd), r11v),
                        k::ext_mul2(k::dup_hi(dn), k::dup_lo(dd), r11v),
                    );
                    let deni = k::ext_mul2(k::dup_lo(dd), k::dup_hi(dd), r11v);
                    let numv = merge_halves(k::load1(n_out.add(2 * j)), numi);
                    let denv = merge_halves(k::load1(d_out.add(2 * j)), deni);
                    let t = k::add8(k::mat_mul2(an, numv), k::mat_mul2(ad, denv));
                    if first {
                        _mm256_storeu_si256(slot(jj), t);
                    } else {
                        _mm256_storeu_si256(slot(jj), k::add8(_mm256_loadu_si256(slot(jj)), t));
                    }
                }
            }
        }
        first = false;
    }

    tdot(tri, chunk_size, t_ptr, chunk_start)
}

/// AVX2 chunk kernel of a CONTINUING round (see `neon_continuing_chunk` for
/// the contract): the previous round's `folding_challenge` applied on read,
/// folded values stored to the trackers' output regions.
///
/// # Safety
///
/// Same pointer contract as `scalar_continuing_chunk`; `scratch` must hold
/// `chunk_size` 32-byte slots; `E` must be BabyBearExt4.
pub unsafe fn avx2_continuing_chunk<E: Field>(
    buffers: &BTreeMap<GKRAddress, FoldBufferTracker<E>>,
    relations: &[LsbDimReducingRelation<E>],
    folding_challenge: E,
    t_ptr: SendConstPtr<E>,
    chunk_start: usize,
    chunk_size: usize,
    scratch: crate::gkr::prover::SendPtr<[u128; 2]>,
) -> [E; 2] {
    let r11v = k::r11v();
    let fold_m = k::ExtMatrix2::new(as_bb(&folding_challenge));
    let rels = rel_matrices(relations);
    if rels.is_empty() {
        return [E::ZERO; 2];
    }
    let tri = scratch.0 as *mut u8;
    let slot = |jj: usize| tri.add(32 * jj) as *mut __m256i;

    let mut first = true;
    for rel in rels.iter() {
        match rel {
            RelM::Pair { input, a, .. } => {
                let src = buffers[input].input_ptr_range().start as *const BabyBearExt4;
                let d = buffers[input].output_ptr_range().start as *mut BabyBearExt4;
                for jj in 0..chunk_size {
                    let j = chunk_start + jj;
                    let (ab0, ab1) = fetch4_fold(src, d, &fold_m, j);
                    let p0 = k::ext_mul2(k::dup_lo(ab0), k::dup_hi(ab0), r11v);
                    let dd = k::sub8(ab1, ab0);
                    let pinf = k::ext_mul2(k::dup_lo(dd), k::dup_hi(dd), r11v);
                    let t = k::mat_mul2(a, merge_halves(p0, pinf));
                    if first {
                        _mm256_storeu_si256(slot(jj), t);
                    } else {
                        _mm256_storeu_si256(slot(jj), k::add8(_mm256_loadu_si256(slot(jj)), t));
                    }
                }
            }
            RelM::Logup {
                num, den, an, ad, ..
            } => {
                let n_src = buffers[num].input_ptr_range().start as *const BabyBearExt4;
                let n_dst = buffers[num].output_ptr_range().start as *mut BabyBearExt4;
                let d_src = buffers[den].input_ptr_range().start as *const BabyBearExt4;
                let d_dst = buffers[den].output_ptr_range().start as *mut BabyBearExt4;
                for jj in 0..chunk_size {
                    let j = chunk_start + jj;
                    let (n01, n23) = fetch4_fold(n_src, n_dst, &fold_m, j);
                    let (d01, d23) = fetch4_fold(d_src, d_dst, &fold_m, j);
                    // num = n0*d1 + n1*d0, den = d0*d1
                    let num0 = k::add8(
                        k::ext_mul2(k::dup_lo(n01), k::dup_hi(d01), r11v),
                        k::ext_mul2(k::dup_hi(n01), k::dup_lo(d01), r11v),
                    );
                    let den0 = k::ext_mul2(k::dup_lo(d01), k::dup_hi(d01), r11v);
                    // X = inf: same on the differences
                    let dn = k::sub8(n23, n01);
                    let dd = k::sub8(d23, d01);
                    let numi = k::add8(
                        k::ext_mul2(k::dup_lo(dn), k::dup_hi(dd), r11v),
                        k::ext_mul2(k::dup_hi(dn), k::dup_lo(dd), r11v),
                    );
                    let deni = k::ext_mul2(k::dup_lo(dd), k::dup_hi(dd), r11v);
                    let t = k::add8(
                        k::mat_mul2(an, merge_halves(num0, numi)),
                        k::mat_mul2(ad, merge_halves(den0, deni)),
                    );
                    if first {
                        _mm256_storeu_si256(slot(jj), t);
                    } else {
                        _mm256_storeu_si256(slot(jj), k::add8(_mm256_loadu_si256(slot(jj)), t));
                    }
                }
            }
        }
        first = false;
    }

    tdot(tri, chunk_size, t_ptr, chunk_start)
}

/// The x86-64 AVX2 + BabyBear/Ext4 same-size chain executor: the window
/// passes and folds run the `lsb_avx2` SoA kernels; the (currently
/// unreachable) uniskip schedule falls back to the portable kernels.
pub struct Avx2SameSizeChain {
    prog: crate::gkr::prover::sumcheck_loop::OwnedSoaProgram<BabyBearField, BabyBearExt4>,
    /// per-FOLDED-slot difference-extension flags (base slots then ext
    /// slots) for the window-3 continuing passes
    folded_interp: Vec<bool>,
    mat: lsb_generic::Lde8Matrix<BabyBearField>,
}

impl Avx2SameSizeChain {
    pub fn new(
        prog: crate::gkr::prover::sumcheck_loop::OwnedSoaProgram<BabyBearField, BabyBearExt4>,
    ) -> Self {
        let omega16_bb = ::fft::domain_generator_for_size::<BabyBearField>(16);
        // slots read at the infinity cells must carry the interpolation flag
        for form in prog.forms.iter() {
            for (_, idx) in form.members.iter() {
                assert!(prog.base_interp[*idx as usize]);
            }
        }
        for (a, b, _) in prog.products.iter() {
            for r in [a, b] {
                if let crate::gkr::prover::sumcheck_loop::windowed_mode::program::FormRef::Slot(i) =
                    r
                {
                    assert!(prog.base_interp[*i as usize]);
                }
            }
        }
        let folded_interp: Vec<bool> = prog
            .base_interp
            .iter()
            .chain(prog.ext_interp.iter())
            .copied()
            .collect();
        Self {
            prog,
            folded_interp,
            mat: lsb_generic::Lde8Matrix::new(omega16_bb),
        }
    }
}

impl crate::gkr::prover::sumcheck_loop::SameSizeChainOps<BabyBearField, BabyBearExt4>
    for Avx2SameSizeChain
{
    fn uniskip_initial_pass(
        &self,
        base_polys: &[&[BabyBearField]],
        ext_polys: &[&[BabyBearExt4]],
        eq_suffix: &[BabyBearExt4],
        out_size: usize,
        worker: &Worker,
    ) -> [BabyBearExt4; 16] {
        use crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::quasi;
        lsb_generic::head_pass::<BabyBearField, BabyBearExt4>(
            &quasi::<BabyBearField, false>(base_polys),
            &quasi::<BabyBearExt4, false>(ext_polys),
            &self.prog,
            &self.mat,
            eq_suffix,
            out_size,
            worker,
        )
    }

    fn uniskip_continuing_pass(
        &self,
        folded: &[&[BabyBearExt4]],
        eq_suffix: &[BabyBearExt4],
        out_size: usize,
        worker: &Worker,
    ) -> [BabyBearExt4; 16] {
        use crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::quasi;
        lsb_generic::ext_pass::<BabyBearField, BabyBearExt4>(
            &quasi::<BabyBearExt4, false>(folded),
            &self.prog,
            &self.mat,
            eq_suffix,
            out_size,
            worker,
        )
    }

    fn window_initial_pass(
        &self,
        base_polys: &[&[BabyBearField]],
        ext_polys: &[&[BabyBearExt4]],
        eq_suffix: &[BabyBearExt4],
        out_size: usize,
        worker: &Worker,
    ) -> [BabyBearExt4; 27] {
        use crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::quasi;
        let base_srcs = quasi::<BabyBearField, false>(base_polys);
        let ext_srcs = quasi::<BabyBearExt4, false>(ext_polys);
        let acc = if out_size % 2 == 0 {
            lsb_avx2::lsb_soa_full_parallel_w3::<2>(
                &base_srcs,
                &ext_srcs,
                &self.prog.base_interp,
                &self.prog.ext_interp,
                &self.prog.forms,
                &self.prog.products,
                &self.prog.rest_steps,
                &self.prog.additive_constant,
                eq_suffix,
                out_size,
                worker,
            )
        } else {
            lsb_avx2::lsb_soa_full_parallel_w3::<1>(
                &base_srcs,
                &ext_srcs,
                &self.prog.base_interp,
                &self.prog.ext_interp,
                &self.prog.forms,
                &self.prog.products,
                &self.prog.rest_steps,
                &self.prog.additive_constant,
                eq_suffix,
                out_size,
                worker,
            )
        };
        core::array::from_fn(|g| acc[lsb_avx2::w3_soa_cell_of_generic(g)])
    }

    fn window_continuing_pass(
        &self,
        folded: &[&[BabyBearExt4]],
        eq_suffix: &[BabyBearExt4],
        out_size: usize,
        worker: &Worker,
    ) -> [BabyBearExt4; 27] {
        use crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::quasi;
        let srcs = quasi::<BabyBearExt4, false>(folded);
        let acc = if out_size % 2 == 0 {
            lsb_avx2::lsb_soa_ext_pass_parallel_w3::<2>(
                &srcs,
                &self.folded_interp,
                &self.prog.forms,
                &self.prog.products,
                &self.prog.folded_quad,
                &self.prog.folded_lin,
                &self.prog.additive_constant,
                eq_suffix,
                out_size,
                worker,
            )
        } else {
            lsb_avx2::lsb_soa_ext_pass_parallel_w3::<1>(
                &srcs,
                &self.folded_interp,
                &self.prog.forms,
                &self.prog.products,
                &self.prog.folded_quad,
                &self.prog.folded_lin,
                &self.prog.additive_constant,
                eq_suffix,
                out_size,
                worker,
            )
        };
        core::array::from_fn(|g| acc[lsb_avx2::w3_soa_cell_of_generic(g)])
    }

    fn fold_initial(
        &self,
        base_polys: &[&[BabyBearField]],
        ext_polys: &[&[BabyBearExt4]],
        weights: &[BabyBearExt4; 8],
        trackers: &mut [FoldBufferTracker<BabyBearExt4>],
        worker: &Worker,
    ) {
        use crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::chain_fold_dst;
        use crate::gkr::sumcheck::access_and_fold::DisjointAccessQuasiSlice;
        let nb = base_polys.len();
        assert_eq!(trackers.len(), nb + ext_polys.len());
        for (i, src) in base_polys.iter().enumerate() {
            let rows = src.len() / 8;
            let dst = chain_fold_dst(&trackers[i], rows);
            if rows % 8 == 0 {
                lsb_avx2::lsb_fold_base_soa_parallel(
                    src.as_ptr() as *const u8,
                    dst,
                    weights,
                    worker,
                );
            } else {
                let q = DisjointAccessQuasiSlice::<_, false>::from_init_slice(src);
                lsb_generic::fold_base::<BabyBearField, BabyBearExt4>(&q, dst, weights, worker);
            }
        }
        for (i, src) in ext_polys.iter().enumerate() {
            let rows = src.len() / 8;
            let dst = chain_fold_dst(&trackers[nb + i], rows);
            if rows % 8 == 0 {
                lsb_avx2::lsb_fold_ext_soa_parallel(
                    src.as_ptr() as *const u8,
                    dst,
                    weights,
                    worker,
                );
            } else {
                lsb_generic::fold_ext::<BabyBearExt4>(
                    crate::gkr::prover::SendConstPtr(src.as_ptr()),
                    dst,
                    weights,
                    worker,
                );
            }
        }
    }

    fn fold_continuing(
        &self,
        weights: &[BabyBearExt4; 8],
        trackers: &mut [FoldBufferTracker<BabyBearExt4>],
        worker: &Worker,
    ) {
        use crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::chain_fold_dst;
        for tracker in trackers.iter_mut() {
            let fold_out = tracker.output_len();
            assert_eq!(tracker.input_len(), 8 * fold_out);
            let src_ptr = tracker.input_ptr_range().start;
            let dst = chain_fold_dst(tracker, fold_out);
            if fold_out % 8 == 0 {
                lsb_avx2::lsb_fold_ext_soa_parallel(src_ptr as *const u8, dst, weights, worker);
            } else {
                lsb_generic::fold_ext::<BabyBearExt4>(
                    crate::gkr::prover::SendConstPtr(src_ptr),
                    dst,
                    weights,
                    worker,
                );
            }
        }
    }

    fn tail_round_message(
        &self,
        trackers: &[FoldBufferTracker<BabyBearExt4>],
        tail_t_table: &[BabyBearExt4],
        worker: &Worker,
    ) -> (BabyBearExt4, BabyBearExt4) {
        crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::tail_round_message_with_program(
            &self.prog,
            trackers,
            tail_t_table,
            worker,
        )
    }
}

/// The x86-64 AVX2 + BabyBear/Ext4 backend. Implemented for that concrete
/// field pair ONLY — the arch and field expectations live entirely in this
/// type, never in the callers.
#[derive(Clone, Copy, Debug, Default)]
pub struct Avx2GKRBackend;

impl GKRBackend<BabyBearField, BabyBearExt4> for Avx2GKRBackend {
    type DimensionReducingBuffer = DimReducingSumcheckScratch<BabyBearExt4, [u128; 2]>;

    fn make_dim_reducing_work_buffers(
        &self,
        max_rounds: usize,
        max_polys: usize,
        worker: &Worker,
    ) -> Self::DimensionReducingBuffer {
        DimReducingSumcheckScratch::new(max_rounds, max_polys, worker)
    }

    fn dimension_reduction_forward(
        &self,
        storage: &mut GKRStorage<BabyBearField, BabyBearExt4>,
        compiled_circuit: &GKRCircuitArtifact<BabyBearField>,
        initial_trace_log_2: usize,
        final_trace_log_2: usize,
        worker: &Worker,
    ) -> (
        usize,
        BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
    ) {
        evaluate_dimension_reduction_forward_with(
            storage,
            compiled_circuit,
            initial_trace_log_2,
            final_trace_log_2,
            worker,
            forward_pairwise_avx2,
            forward_logup_avx2,
        )
    }

    fn dimension_reducing_sumcheck_for_layer<TR: Transcript<BabyBearField, BabyBearExt4>>(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        layer_idx: usize,
        layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
        claim_points: &mut BTreeMap<usize, Vec<EvaluationPointEntry<BabyBearExt4>>>,
        claims_storage: &mut BTreeMap<usize, BTreeMap<GKRAddress, BabyBearExt4>>,
        gkr_storage: &mut GKRStorage<BabyBearField, BabyBearExt4>,
        batching_challenge: &mut BabyBearExt4,
        seed: &mut TR::Seed,
        trace_len_after_reduction: usize,
        worker: &Worker,
        buffers: &mut Self::DimensionReducingBuffer,
    ) -> SumcheckIntermediateProofValues<BabyBearField, BabyBearExt4> {
        super::super::sumcheck_loop::evaluate_dimension_reducing_sumcheck_for_layer_lsb::<
            BabyBearField,
            BabyBearExt4,
            TR,
            [u128; 2],
            _,
            _,
        >(
            |cur, outs, rels, tp, cs, cl, sp| unsafe {
                avx2_initial_chunk::<BabyBearExt4>(cur, outs, rels, tp, cs, cl, sp)
            },
            |buffers, rels, r, tp, cs, cl, sp| unsafe {
                avx2_continuing_chunk::<BabyBearExt4>(buffers, rels, r, tp, cs, cl, sp)
            },
            schedule,
            layer_idx,
            layer,
            claim_points,
            claims_storage,
            gkr_storage,
            batching_challenge,
            seed,
            trace_len_after_reduction,
            worker,
            buffers,
        )
    }

    type NaiveSameSizeFoldBuffer = Box<[core::mem::MaybeUninit<BabyBearExt4>]>;
    type WindowedSameSizeFoldBuffer = Box<[core::mem::MaybeUninit<BabyBearExt4>]>;
    type UniskipSameSizeFoldBuffer = Box<[core::mem::MaybeUninit<BabyBearExt4>]>;

    fn make_naive_same_size_fold_buffers(
        &self,
        _schedule: &[crate::gkr::prover_config::SumcheckStep],
        _trace_len: usize,
        _num_base_polys: usize,
        _num_ext_polys: usize,
    ) -> Vec<Self::NaiveSameSizeFoldBuffer> {
        Vec::new()
    }

    fn make_windowed_same_size_fold_buffers(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        trace_len: usize,
        num_base_polys: usize,
        num_ext_polys: usize,
    ) -> Vec<Self::WindowedSameSizeFoldBuffer> {
        let capacity = super::same_size_chain_fold_capacity(schedule, trace_len);
        (0..num_base_polys + num_ext_polys)
            .map(|_| Box::new_uninit_slice(capacity))
            .collect()
    }

    fn make_uniskip_same_size_fold_buffers(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        trace_len: usize,
        num_base_polys: usize,
        num_ext_polys: usize,
    ) -> Vec<Self::UniskipSameSizeFoldBuffer> {
        let capacity = super::same_size_chain_fold_capacity(schedule, trace_len);
        (0..num_base_polys + num_ext_polys)
            .map(|_| Box::new_uninit_slice(capacity))
            .collect()
    }

    type SameSizeChain = Avx2SameSizeChain;

    fn make_same_size_chain(
        &self,
        prog: crate::gkr::prover::sumcheck_loop::OwnedSoaProgram<BabyBearField, BabyBearExt4>,
    ) -> Self::SameSizeChain {
        Avx2SameSizeChain::new(prog)
    }

    fn evaluate_same_size_sumcheck_for_layer<TR: Transcript<BabyBearField, BabyBearExt4>>(
        &self,
        layer_idx: usize,
        layer: &cs::gkr_compiler::GKRLayerDescription<BabyBearField>,
        claim_points: &mut BTreeMap<usize, Vec<EvaluationPointEntry<BabyBearExt4>>>,
        claims_storage: &mut BTreeMap<usize, BTreeMap<GKRAddress, BabyBearExt4>>,
        gkr_storage: &mut GKRStorage<BabyBearField, BabyBearExt4>,
        batching_challenge: &mut BabyBearExt4,
        trace_len: usize,
        lookup_challenges_multiplicative_part: BabyBearExt4,
        lookup_challenges_additive_part: BabyBearExt4,
        inits_and_teardowns_top_bits: &[u32],
        address_high_bits_shift: u32,
        external_challenges: &super::super::GKRExternalChallenges<BabyBearField, BabyBearExt4>,
        prover_config: &crate::gkr::prover_config::ProverConfig,
        seed: &mut TR::Seed,
        worker: &Worker,
    ) -> SumcheckIntermediateProofValues<BabyBearField, BabyBearExt4> {
        super::super::sumcheck_loop::evaluate_sumcheck_for_layer::<BabyBearField, BabyBearExt4, TR, _>(
            layer_idx,
            layer,
            claim_points,
            claims_storage,
            gkr_storage,
            batching_challenge,
            trace_len,
            lookup_challenges_multiplicative_part,
            lookup_challenges_additive_part,
            inits_and_teardowns_top_bits,
            address_high_bits_shift,
            external_challenges,
            prover_config,
            seed,
            worker,
            |s, t, b, e| self.make_uniskip_same_size_fold_buffers(s, t, b, e),
            |s, t, b, e| self.make_windowed_same_size_fold_buffers(s, t, b, e),
            |prog| self.make_same_size_chain(prog),
        )
    }
}
