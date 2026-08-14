//! aarch64 + BabyBear/Ext4 specialization, mirroring the FFT/tree
//! `BabyBearNeonWorkStealingBackend`: NEON per-relation forward ops and the
//! NEON fused-sweep chunk kernel for the backward path. This module is the
//! ONLY place the GKR backend tree contains platform-specific code, and
//! [`NeonGKRBackend`] is implemented for the concrete BabyBear pair only —
//! generic-field callers use [`NaiveGKRBackend`](super::NaiveGKRBackend).

use std::collections::BTreeMap;

use super::super::dimension_reduction::forward::{
    evaluate_dimension_reduction_forward_with, DimensionReducingInputOutput,
};
use super::super::dimension_reduction::lsb_backward::{FoldBufferTracker, LsbDimReducingRelation};
use super::super::{GKRAddress, GKRStorage, SendConstPtr, SumcheckIntermediateProofValues};
use super::{DimReducingSumcheckScratch, GKRBackend};
use crate::gkr::prover::sumcheck_loop::windowed_mode::neon::{add4, ext_mul_var, r11};
use crate::gkr::prover::EvaluationPointEntry;
use crate::gkr::sumcheck::evaluation_kernels::GKRInputs;
use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use core::arch::aarch64::{vdupq_n_u32, vld1q_u32, vst1q_u32};
use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};
use field::{Field, FieldExtension, PrimeField};
use transcript::Transcript;
use worker::Worker;

/// NEON forward pairwise product: `out[i] = in[2i] (x) in[2i+1]`.
pub fn forward_pairwise_neon<F: PrimeField, E: FieldExtension<F> + Field>(
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
                    let sp = src_addr.get() as *const u32;
                    let dp = dst_addr.get() as *mut u32;
                    let r11v = vdupq_n_u32(r11());
                    for i in chunk_start..(chunk_start + chunk_size) {
                        let a = vld1q_u32(sp.add(8 * i));
                        let b = vld1q_u32(sp.add(8 * i + 4));
                        vst1q_u32(dp.add(4 * i), ext_mul_var(a, b, r11v));
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

/// NEON forward logup fraction add.
pub fn forward_logup_neon<F: PrimeField, E: FieldExtension<F> + Field>(
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
                    let np = n_addr.get() as *const u32;
                    let dp = d_addr.get() as *const u32;
                    let ndp = nd_addr.get() as *mut u32;
                    let ddp = dd_addr.get() as *mut u32;
                    let r11v = vdupq_n_u32(r11());
                    for i in chunk_start..(chunk_start + chunk_size) {
                        let n0 = vld1q_u32(np.add(8 * i));
                        let n1 = vld1q_u32(np.add(8 * i + 4));
                        let d0 = vld1q_u32(dp.add(8 * i));
                        let d1 = vld1q_u32(dp.add(8 * i + 4));
                        let num_v = add4(ext_mul_var(n0, d1, r11v), ext_mul_var(n1, d0, r11v));
                        vst1q_u32(ndp.add(4 * i), num_v);
                        vst1q_u32(ddp.add(4 * i), ext_mul_var(d0, d1, r11v));
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

/// `E -> BabyBearExt4` reference cast (callers are BabyBear-pair-only by
/// construction: [`NeonGKRBackend`] implements the trait for that pair).
#[inline(always)]
fn as_bb<E: Field>(c: &E) -> &BabyBearExt4 {
    unsafe { &*(c as *const E as *const _) }
}

/// Per-relation alpha matrices with the relation's poly ADDRESSES carried
/// along; resolved against the pointer maps once per chunk.
enum RelM {
    Pair {
        input: GKRAddress,
        output: GKRAddress,
        a: crate::gkr::prover::sumcheck_loop::windowed_mode::neon::ExtMatrix,
    },
    Logup {
        num: GKRAddress,
        den: GKRAddress,
        num_output: GKRAddress,
        den_output: GKRAddress,
        an: crate::gkr::prover::sumcheck_loop::windowed_mode::neon::ExtMatrix,
        ad: crate::gkr::prover::sumcheck_loop::windowed_mode::neon::ExtMatrix,
    },
}

fn rel_matrices<E: Field>(relations: &[LsbDimReducingRelation<E>]) -> Vec<RelM> {
    use crate::gkr::prover::sumcheck_loop::windowed_mode::neon::ExtMatrix;
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
                a: ExtMatrix::new(as_bb(alpha)),
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
                an: ExtMatrix::new(as_bb(alpha_num)),
                ad: ExtMatrix::new(as_bb(alpha_den)),
            },
        })
        .collect()
}

/// Direct fetch of the 4 pair values of row `j` (no pending fold), one Ext4
/// element per NEON vector.
#[inline(always)]
unsafe fn neon_fetch4_direct(src: *const u32, j: usize) -> [core::arch::aarch64::uint32x4_t; 4] {
    core::array::from_fn(|k| vld1q_u32(src.add((4 * j + k) * 4)))
}

/// Fold-on-read fetch of the CURRENT 4 pair values of row `j`, applying the
/// pending challenge's `ExtMatrix` in-register and storing the folded values
/// to `dst` for the next round while hot.
#[inline(always)]
unsafe fn neon_fetch4_fold(
    src: *const u32,
    dst: *mut u32,
    fm: &crate::gkr::prover::sumcheck_loop::windowed_mode::neon::ExtMatrix,
    j: usize,
) -> [core::arch::aarch64::uint32x4_t; 4] {
    use crate::gkr::prover::sumcheck_loop::windowed_mode::neon::{add4, mat_mul, sub4};
    let mut out = [vdupq_n_u32(0); 4];
    for yy in 0..2 {
        for b in 0..2 {
            let lo = vld1q_u32(src.add((2 * (4 * j + 2 * yy) + b) * 4));
            let hi = vld1q_u32(src.add((2 * (4 * j + 2 * yy + 1) + b) * 4));
            let v = add4(lo, mat_mul(fm, sub4(hi, lo)));
            vst1q_u32(dst.add((2 * (2 * j + yy) + b) * 4), v);
            out[2 * yy + b] = v;
        }
    }
    out
}

/// Fused T-dot over the chunk's hot tri vectors.
#[inline(always)]
unsafe fn neon_tdot<E: Field>(
    tri: &[[core::arch::aarch64::uint32x4_t; 2]],
    t_ptr: SendConstPtr<E>,
    chunk_start: usize,
) -> [E; 2] {
    let r11v = vdupq_n_u32(r11());
    let t_tab = t_ptr.0 as *const u32;
    let mut acc = [vdupq_n_u32(0); 2];
    for (jj, t) in tri.iter().enumerate() {
        let w = vld1q_u32(t_tab.add((chunk_start + jj) * 4));
        for k in 0..2 {
            acc[k] = add4(acc[k], ext_mul_var(w, t[k], r11v));
        }
    }
    let mut out = [E::ZERO; 2];
    for k in 0..2 {
        let mut raw = [0u32; 4];
        vst1q_u32(raw.as_mut_ptr(), acc[k]);
        out[k] = *(raw.as_ptr() as *const E);
    }
    out
}

/// aarch64 + BabyBear/Ext4 chunk kernel of the INITIAL round: gate values at
/// `X = 0` are loaded straight from the OUTPUT layer polys, `X = inf` from
/// the input differences; nothing is folded. AoS throughout, one Ext4
/// element per NEON vector.
///
/// # Safety
///
/// Same pointer contract as `scalar_initial_chunk`: for rows
/// `chunk_start..chunk_start + chunk_size`, `inputs` pointers cover the full
/// input polys (`8 * pairs` values), `outputs` pointers the full output
/// polys (`2 * pairs` values), `t_ptr` the round's suffix eq table (at least
/// `pairs` entries), and `scratch` is this thread's EXCLUSIVE tri slot with
/// capacity for `chunk_size` 32-byte `[u128; 2]` rows (reinterpreted as
/// `[uint32x4_t; 2]` `[v0, vinf]` accumulators; may be uninitialized).
/// Additionally `E` must be BabyBearExt4 (enforced by [`NeonGKRBackend`]'s
/// concrete impl).
pub unsafe fn neon_initial_chunk<E: Field>(
    inputs: &BTreeMap<GKRAddress, &[E]>,
    outputs: &BTreeMap<GKRAddress, &[E]>,
    relations: &[LsbDimReducingRelation<E>],
    t_ptr: SendConstPtr<E>,
    chunk_start: usize,
    chunk_size: usize,
    scratch: crate::gkr::prover::SendPtr<[u128; 2]>,
) -> [E; 2] {
    use crate::gkr::prover::sumcheck_loop::windowed_mode::neon::{mat_mul, sub4};
    use core::arch::aarch64::uint32x4_t;
    let r11v = vdupq_n_u32(r11());
    let rels = rel_matrices(relations);

    // caller-provided tri scratch as raw vectors: [v0, vinf] per row
    // ([u128; 2] slots are size/align-compatible with [uint32x4_t; 2])
    let tri = core::slice::from_raw_parts_mut(scratch.0 as *mut [uint32x4_t; 2], chunk_size);
    for t in tri.iter_mut() {
        *t = [vdupq_n_u32(0); 2];
    }

    let mut first = true;
    for rel in rels.iter() {
        match rel {
            RelM::Pair { input, output, a } => {
                let src = inputs[input].as_ptr() as *const u32;
                let out = outputs[output].as_ptr() as *const u32;
                for (jj, t) in tri.iter_mut().enumerate() {
                    let j = chunk_start + jj;
                    let [a0, b0, a1, b1] = neon_fetch4_direct(src, j);
                    // the output layer already holds the gate value at X = 0
                    let v0 = mat_mul(a, vld1q_u32(out.add(8 * j)));
                    let vinf = mat_mul(a, ext_mul_var(sub4(a1, a0), sub4(b1, b0), r11v));
                    if first {
                        *t = [v0, vinf];
                    } else {
                        t[0] = add4(t[0], v0);
                        t[1] = add4(t[1], vinf);
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
                let n_src = inputs[num].as_ptr() as *const u32;
                let d_src = inputs[den].as_ptr() as *const u32;
                let n_out = outputs[num_output].as_ptr() as *const u32;
                let d_out = outputs[den_output].as_ptr() as *const u32;
                for (jj, t) in tri.iter_mut().enumerate() {
                    let j = chunk_start + jj;
                    let [n0, n1, n2, n3] = neon_fetch4_direct(n_src, j);
                    let [d0, d1, d2, d3] = neon_fetch4_direct(d_src, j);
                    // X = 0 from the output layer
                    let (num0, den0) = (vld1q_u32(n_out.add(8 * j)), vld1q_u32(d_out.add(8 * j)));
                    // X = inf: the fraction-add on the differences
                    let (dn0, dn1) = (sub4(n2, n0), sub4(n3, n1));
                    let (dd0, dd1) = (sub4(d2, d0), sub4(d3, d1));
                    let numi = add4(ext_mul_var(dn0, dd1, r11v), ext_mul_var(dn1, dd0, r11v));
                    let deni = ext_mul_var(dd0, dd1, r11v);
                    let v0 = add4(mat_mul(an, num0), mat_mul(ad, den0));
                    let vinf = add4(mat_mul(an, numi), mat_mul(ad, deni));
                    if first {
                        *t = [v0, vinf];
                    } else {
                        t[0] = add4(t[0], v0);
                        t[1] = add4(t[1], vinf);
                    }
                }
            }
        }
        first = false;
    }

    neon_tdot(tri, t_ptr, chunk_start)
}

/// aarch64 + BabyBear/Ext4 chunk kernel of a CONTINUING round: the previous
/// round's `folding_challenge` is applied in-register on read (`ExtMatrix`
/// of the challenge), folded values stored to `dst` + consumed hot by the
/// gate products.
///
/// # Safety
///
/// Same pointer contract as `scalar_continuing_chunk`: for rows
/// `chunk_start..chunk_start + chunk_size`, every tracker's INPUT range
/// covers the round's UNFOLDED source (`8 * pairs` values) and its OUTPUT
/// range a DISJOINT destination (`4 * pairs` values written), `t_ptr` the
/// round's suffix eq table (at least `pairs` entries), and `scratch` is this
/// thread's EXCLUSIVE tri slot with capacity for `chunk_size` 32-byte
/// `[u128; 2]` rows (reinterpreted as `[uint32x4_t; 2]` accumulators; may be
/// uninitialized). Additionally `E` must be BabyBearExt4 (enforced by
/// [`NeonGKRBackend`]'s concrete impl).
pub unsafe fn neon_continuing_chunk<E: Field>(
    buffers: &BTreeMap<GKRAddress, FoldBufferTracker<E>>,
    relations: &[LsbDimReducingRelation<E>],
    folding_challenge: E,
    t_ptr: SendConstPtr<E>,
    chunk_start: usize,
    chunk_size: usize,
    scratch: crate::gkr::prover::SendPtr<[u128; 2]>,
) -> [E; 2] {
    use crate::gkr::prover::sumcheck_loop::windowed_mode::neon::{mat_mul, sub4, ExtMatrix};
    use core::arch::aarch64::uint32x4_t;
    let r11v = vdupq_n_u32(r11());
    let fold_m = ExtMatrix::new(as_bb(&folding_challenge));
    let rels = rel_matrices(relations);

    // caller-provided tri scratch as raw vectors: [v0, vinf] per row
    let tri = core::slice::from_raw_parts_mut(scratch.0 as *mut [uint32x4_t; 2], chunk_size);
    for t in tri.iter_mut() {
        *t = [vdupq_n_u32(0); 2];
    }

    let mut first = true;
    for rel in rels.iter() {
        match rel {
            RelM::Pair { input, a, .. } => {
                let src = buffers[input].input_ptr_range().start as *const u32;
                let d = buffers[input].output_ptr_range().start as *mut u32;
                for (jj, t) in tri.iter_mut().enumerate() {
                    let j = chunk_start + jj;
                    let [a0, b0, a1, b1] = neon_fetch4_fold(src, d, &fold_m, j);
                    let v0 = mat_mul(a, ext_mul_var(a0, b0, r11v));
                    let vinf = mat_mul(a, ext_mul_var(sub4(a1, a0), sub4(b1, b0), r11v));
                    if first {
                        *t = [v0, vinf];
                    } else {
                        t[0] = add4(t[0], v0);
                        t[1] = add4(t[1], vinf);
                    }
                }
            }
            RelM::Logup {
                num, den, an, ad, ..
            } => {
                let n_src = buffers[num].input_ptr_range().start as *const u32;
                let n_dst = buffers[num].output_ptr_range().start as *mut u32;
                let d_src = buffers[den].input_ptr_range().start as *const u32;
                let d_dst = buffers[den].output_ptr_range().start as *mut u32;
                for (jj, t) in tri.iter_mut().enumerate() {
                    let j = chunk_start + jj;
                    let [n0, n1, n2, n3] = neon_fetch4_fold(n_src, n_dst, &fold_m, j);
                    let [d0, d1, d2, d3] = neon_fetch4_fold(d_src, d_dst, &fold_m, j);
                    // num = n0*d1 + n1*d0, den = d0*d1
                    let num0 = add4(ext_mul_var(n0, d1, r11v), ext_mul_var(n1, d0, r11v));
                    let den0 = ext_mul_var(d0, d1, r11v);
                    // X = inf: same on the differences
                    let (dn0, dn1) = (sub4(n2, n0), sub4(n3, n1));
                    let (dd0, dd1) = (sub4(d2, d0), sub4(d3, d1));
                    let numi = add4(ext_mul_var(dn0, dd1, r11v), ext_mul_var(dn1, dd0, r11v));
                    let deni = ext_mul_var(dd0, dd1, r11v);
                    let v0 = add4(mat_mul(an, num0), mat_mul(ad, den0));
                    let vinf = add4(mat_mul(an, numi), mat_mul(ad, deni));
                    if first {
                        *t = [v0, vinf];
                    } else {
                        t[0] = add4(t[0], v0);
                        t[1] = add4(t[1], vinf);
                    }
                }
            }
        }
        first = false;
    }

    neon_tdot(tri, t_ptr, chunk_start)
}

/// The aarch64 + BabyBear/Ext4 backend. Implemented for that concrete field
/// pair ONLY — the arch and field expectations live entirely in this type,
/// never in the callers.
#[derive(Clone, Copy, Debug, Default)]
pub struct NeonGKRBackend;

impl GKRBackend<BabyBearField, BabyBearExt4> for NeonGKRBackend {
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
            forward_pairwise_neon,
            forward_logup_neon,
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
                neon_initial_chunk::<BabyBearExt4>(cur, outs, rels, tp, cs, cl, sp)
            },
            |buffers, rels, r, tp, cs, cl, sp| unsafe {
                neon_continuing_chunk::<BabyBearExt4>(buffers, rels, r, tp, cs, cl, sp)
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
}
