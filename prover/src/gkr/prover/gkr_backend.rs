//! GKR-argument counterpart of the FFT/tree [`Backend`](super::backend::Backend)
//! trait: pins the heavy per-layer operations of the GKR prover behind a
//! swappable strategy so alternative implementations (LSB-binding windowed /
//! uniskip engines, GPU offload) can replace the execution while keeping the
//! transcript BYTE-IDENTICAL for identical schedules.
//!
//! Contract mirror of `Backend`: [`NaiveGKRBackend`] delegates to the
//! historical free functions unchanged and works for every `<F, E>` pair;
//! alternative backends may re-schedule or re-vectorize the work, and — when
//! the [`SumcheckStep`](crate::gkr::prover_config::SumcheckStep) schedule
//! selects non-naive steps — produce the CORRESPONDING transcript messages
//! ([`SumcheckRoundCoefficients::Uniskip`](super::SumcheckRoundCoefficients)
//! rounds etc.), which is a protocol-level choice recorded in the
//! [`ProverConfig`](crate::gkr::prover_config::ProverConfig), not a
//! backend-private one.
//!
//! Migration plan (kept incremental so `gkr_self_checks` stays green at every
//! stage):
//! 1. dimension-reducing layers (fixed gate set: pairwise products + logup
//!    reduction) — forward path and backward (sumcheck) path;
//! 2. same-size layer sumchecks (windowed / uniskip schedules over the
//!    bracket-preserving compiled relations);
//! 3. remaining glue (eq-table maintenance, folds).

use std::collections::BTreeMap;

use super::dimension_reduction::forward::evaluate_dimension_reduction_forward;
use super::sumcheck_loop::evaluate_dimension_reducing_sumcheck_for_layer;
use super::dimension_reduction::forward::DimensionReducingInputOutput;
use super::{GKRStorage, SumcheckIntermediateProofValues};
use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};
use field::{Field, FieldExtension, PrimeField};
use transcript::Transcript;
use worker::Worker;

/// Strategy for the GKR prover's per-layer heavy operations. Methods are
/// generic (no `dyn` use is intended); implementations must be pure with
/// respect to the transcript: for the same schedule, every backend produces
/// identical field values in identical order.
pub trait GKRBackend<F: PrimeField, E: FieldExtension<F> + Field>: Send + Sync {
    /// Forward (output-construction) evaluation of ALL dimension-reducing
    /// layers, mirroring
    /// [`evaluate_dimension_reduction_forward`]'s contract: consumes the
    /// grand-product / logup inputs from `storage`, materializes every
    /// intermediate layer, and returns the first layer index for the
    /// backward pass plus the per-layer input/output descriptions.
    fn dimension_reduction_forward(
        &self,
        storage: &mut GKRStorage<F, E>,
        compiled_circuit: &GKRCircuitArtifact<F>,
        initial_trace_log_2: usize,
        final_trace_log_2: usize,
        worker: &Worker,
    ) -> (
        usize,
        BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
    );

    /// Backward (sumcheck) pass over ONE dimension-reducing layer,
    /// mirroring [`evaluate_dimension_reducing_sumcheck_for_layer`]. The
    /// dimension-reducing gate set is fixed (pairwise products and logup
    /// reduction gates only), so implementations may specialize far more
    /// aggressively than for the same-size layers.
    #[allow(clippy::too_many_arguments)]
    fn dimension_reducing_sumcheck_for_layer<TR: Transcript<F, E>>(
        &self,
        layer_idx: usize,
        layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
        claim_points: &mut BTreeMap<usize, Vec<E>>,
        claims_storage: &mut BTreeMap<usize, BTreeMap<super::GKRAddress, E>>,
        gkr_storage: &mut GKRStorage<F, E>,
        batching_challenge: &mut E,
        seed: &mut TR::Seed,
        trace_len_after_reduction: usize,
        worker: &Worker,
    ) -> SumcheckIntermediateProofValues<F, E>
    where
        [(); E::DEGREE]: Sized;
}

/// The reference backend: byte-identical delegation to the historical free
/// functions (single-variable naive sumcheck rounds everywhere).
#[derive(Clone, Copy, Debug, Default)]
pub struct NaiveGKRBackend;

impl<F: PrimeField, E: FieldExtension<F> + Field> GKRBackend<F, E> for NaiveGKRBackend {
    fn dimension_reduction_forward(
        &self,
        storage: &mut GKRStorage<F, E>,
        compiled_circuit: &GKRCircuitArtifact<F>,
        initial_trace_log_2: usize,
        final_trace_log_2: usize,
        worker: &Worker,
    ) -> (
        usize,
        BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
    ) {
        super::dimension_reduction::forward::evaluate_dimension_reduction_forward_with(
            storage,
            compiled_circuit,
            initial_trace_log_2,
            final_trace_log_2,
            worker,
            super::dimension_reduction::forward::forward_pairwise_specialized,
            super::dimension_reduction::forward::forward_logup_specialized,
        )
    }

    fn dimension_reducing_sumcheck_for_layer<TR: Transcript<F, E>>(
        &self,
        layer_idx: usize,
        layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
        claim_points: &mut BTreeMap<usize, Vec<E>>,
        claims_storage: &mut BTreeMap<usize, BTreeMap<super::GKRAddress, E>>,
        gkr_storage: &mut GKRStorage<F, E>,
        batching_challenge: &mut E,
        seed: &mut TR::Seed,
        trace_len_after_reduction: usize,
        worker: &Worker,
    ) -> SumcheckIntermediateProofValues<F, E>
    where
        [(); E::DEGREE]: Sized,
    {
        super::sumcheck_loop::evaluate_dimension_reducing_sumcheck_for_layer_lsb::<F, E, TR, _>(
            super::dimension_reduction::lsb_backward::scalar_fused_chunk::<E>,
            layer_idx,
            layer,
            claim_points,
            claims_storage,
            gkr_storage,
            batching_challenge,
            seed,
            trace_len_after_reduction,
            worker,
        )
    }
}

/// aarch64 + BabyBear specialization, mirroring the FFT/tree
/// `BabyBearNeonWorkStealingBackend`: NEON per-relation forward ops and the
/// NEON fused-sweep chunk kernel for the backward path. ALL platform and
/// field-pair dispatch is confined to this module and the `run_*` selection
/// wrappers below -- implementation bodies elsewhere stay platform-free.
#[cfg(target_arch = "aarch64")]
pub mod aarch64 {
    use super::super::dimension_reduction::forward::evaluate_dimension_reduction_forward_with;
    use super::super::dimension_reduction::lsb_backward::LsbDimReducingRelation;
    use super::super::GKRStorage;
    use super::{BTreeMap, DimensionReducingInputOutput, GKRCircuitArtifact, OutputType};
    use crate::gkr::prover::sumcheck_loop::windowed_mode::neon::{add4, ext_mul_var, r11};
    use crate::gkr::sumcheck::evaluation_kernels::GKRInputs;
    use core::arch::aarch64::{vdupq_n_u32, vld1q_u32, vst1q_u32};
    use super::super::GKRAddress;
    use field::{Field, FieldExtension, PrimeField};
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
            let src_addr = src.as_ptr() as usize;
            let dst_addr = destination.as_mut_ptr() as usize;
            worker.scope_with_threshold(output_trace_len, PAR_THRESHOLD, |scope, geometry| {
                for thread_idx in 0..geometry.num_chunks {
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        let sp = src_addr as *const u32;
                        let dp = dst_addr as *mut u32;
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
            let n_addr = n_src.as_ptr() as usize;
            let d_addr = d_src.as_ptr() as usize;
            let nd_addr = num_dst.as_mut_ptr() as usize;
            let dd_addr = den_dst.as_mut_ptr() as usize;
            worker.scope_with_threshold(output_trace_len, PAR_THRESHOLD, |scope, geometry| {
                for thread_idx in 0..geometry.num_chunks {
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        let np = n_addr as *const u32;
                        let dp = d_addr as *const u32;
                        let ndp = nd_addr as *mut u32;
                        let ddp = dd_addr as *mut u32;
                        let r11v = vdupq_n_u32(r11());
                        for i in chunk_start..(chunk_start + chunk_size) {
                            let n0 = vld1q_u32(np.add(8 * i));
                            let n1 = vld1q_u32(np.add(8 * i + 4));
                            let d0 = vld1q_u32(dp.add(8 * i));
                            let d1 = vld1q_u32(dp.add(8 * i + 4));
                            let num_v =
                                add4(ext_mul_var(n0, d1, r11v), ext_mul_var(n1, d0, r11v));
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

    /// NEON forward pass = the shared skeleton with the NEON per-relation ops.
    pub fn dimension_reduction_forward_neon<F: PrimeField, E: FieldExtension<F> + Field>(
        storage: &mut GKRStorage<F, E>,
        compiled_circuit: &GKRCircuitArtifact<F>,
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

/// aarch64 + BabyBear/Ext4 chunk kernel for the fused sweep: one Ext4 element
/// per NEON vector, AoS throughout. Per output pair: 8 contiguous vector
/// loads per poly, the pending fold applied in-register (`ExtMatrix` of the
/// challenge), folded values stored + consumed hot by the gate products
/// (`ext_mul_var`), alpha applied via each relation's precomputed
/// `ExtMatrix`, and the T-dot fused over the chunk's tri vectors.
#[allow(clippy::too_many_arguments)]
pub unsafe fn fused_chunk_neon<E: Field>(
    cur_ptrs: &[usize],
    dst_ptrs: &[usize],
    out_ptrs: &[[usize; 2]],
    relations: &[LsbDimReducingRelation<E>],
    pending_r: Option<E>,
    t_ptr: usize,
    chunk_start: usize,
    chunk_size: usize,
) -> [E; 2] {
    use crate::gkr::prover::sumcheck_loop::windowed_mode::neon::{
        add4, ext_mul_var, mat_mul, r11, sub4, ExtMatrix,
    };
    use ::field::baby_bear::ext4::BabyBearExt4;
    use core::arch::aarch64::{uint32x4_t, vdupq_n_u32, vld1q_u32, vst1q_u32};

    let ec = |c: &E| -> &BabyBearExt4 { &*(c as *const E as *const _) };
    let r11v = vdupq_n_u32(r11());
    let fold_m = pending_r.as_ref().map(|r| ExtMatrix::new(ec(r)));
    // per-relation alpha matrices
    enum RelM {
        Pair { input: usize, a: ExtMatrix },
        Logup { num: usize, den: usize, an: ExtMatrix, ad: ExtMatrix },
    }
    let rels: Vec<RelM> = relations
        .iter()
        .map(|rel| match rel {
            LsbDimReducingRelation::PairwiseProduct { input, alpha } => RelM::Pair {
                input: *input,
                a: ExtMatrix::new(ec(alpha)),
            },
            LsbDimReducingRelation::LogupPair {
                num,
                den,
                alpha_num,
                alpha_den,
            } => RelM::Logup {
                num: *num,
                den: *den,
                an: ExtMatrix::new(ec(alpha_num)),
                ad: ExtMatrix::new(ec(alpha_den)),
            },
        })
        .collect();

    // tri buffer as raw vectors: [v0, vinf] per row
    let mut tri: Vec<[uint32x4_t; 2]> = vec![[vdupq_n_u32(0); 2]; chunk_size];

    // fetch the 4 current pair values of poly p at row j (fold-on-read)
    let fetch = |p: usize, j: usize| -> [uint32x4_t; 4] {
        let src = cur_ptrs[p] as *const u32;
        match &fold_m {
            None => core::array::from_fn(|k| vld1q_u32(src.add((4 * j + k) * 4))),
            Some(fm) => {
                let d = dst_ptrs[p] as *mut u32;
                let mut out = [vdupq_n_u32(0); 4];
                for yy in 0..2 {
                    for b in 0..2 {
                        let lo = vld1q_u32(src.add((2 * (4 * j + 2 * yy) + b) * 4));
                        let hi = vld1q_u32(src.add((2 * (4 * j + 2 * yy + 1) + b) * 4));
                        let v = add4(lo, mat_mul(fm, sub4(hi, lo)));
                        vst1q_u32(d.add((2 * (2 * j + yy) + b) * 4), v);
                        out[2 * yy + b] = v;
                    }
                }
                out
            }
        }
    };

    let mut first = true;
    for (rel_idx, rel) in rels.iter().enumerate() {
        match rel {
            RelM::Pair { input, a } => {
                for (jj, t) in tri.iter_mut().enumerate() {
                    let j = chunk_start + jj;
                    let [a0, b0, a1, b1] = fetch(*input, j);
                    // round 0: read the gate value from the output layer
                    let v0raw = if pending_r.is_none() {
                        vld1q_u32((out_ptrs[rel_idx][0] as *const u32).add(8 * j))
                    } else {
                        ext_mul_var(a0, b0, r11v)
                    };
                    let v0 = mat_mul(a, v0raw);
                    let vinf = mat_mul(a, ext_mul_var(sub4(a1, a0), sub4(b1, b0), r11v));
                    if first {
                        *t = [v0, vinf];
                    } else {
                        t[0] = add4(t[0], v0);
                        t[1] = add4(t[1], vinf);
                    }
                }
            }
            RelM::Logup { num, den, an, ad } => {
                for (jj, t) in tri.iter_mut().enumerate() {
                    let j = chunk_start + jj;
                    let [n0, n1, n2, n3] = fetch(*num, j);
                    let [d0, d1, d2, d3] = fetch(*den, j);
                    // X = 0: read from the output layer at round 0, else
                    // num = n0*d1 + n1*d0, den = d0*d1
                    let (num0, den0) = if pending_r.is_none() {
                        (
                            vld1q_u32((out_ptrs[rel_idx][0] as *const u32).add(8 * j)),
                            vld1q_u32((out_ptrs[rel_idx][1] as *const u32).add(8 * j)),
                        )
                    } else {
                        (
                            add4(
                                ext_mul_var(n0, d1, r11v),
                                ext_mul_var(n1, d0, r11v),
                            ),
                            ext_mul_var(d0, d1, r11v),
                        )
                    };
                    // X = inf: same on the differences
                    let (dn0, dn1) = (sub4(n2, n0), sub4(n3, n1));
                    let (dd0, dd1) = (sub4(d2, d0), sub4(d3, d1));
                    let numi = add4(
                        ext_mul_var(dn0, dd1, r11v),
                        ext_mul_var(dn1, dd0, r11v),
                    );
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

    // fused T-dot over the hot tri vectors
    let t_tab = t_ptr as *const u32;
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
}

/// Selection wrappers: the ONLY place platform / field-pair dispatch happens.
/// Callers (`prover/mod.rs`) and implementation bodies are platform-free.
pub fn run_dimension_reduction_forward<F: PrimeField, E: FieldExtension<F> + Field>(
    storage: &mut GKRStorage<F, E>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    initial_trace_log_2: usize,
    final_trace_log_2: usize,
    worker: &Worker,
) -> (
    usize,
    BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
) {
    #[cfg(target_arch = "aarch64")]
    if const { crate::gkr::prover::sumcheck_loop::windowed_mode::neon::is_bb_pair::<F, E>() } {
        return aarch64::dimension_reduction_forward_neon(
            storage,
            compiled_circuit,
            initial_trace_log_2,
            final_trace_log_2,
            worker,
        );
    }
    GKRBackend::<F, E>::dimension_reduction_forward(
        &NaiveGKRBackend,
        storage,
        compiled_circuit,
        initial_trace_log_2,
        final_trace_log_2,
        worker,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn run_dimension_reducing_sumcheck_for_layer<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    TR: Transcript<F, E>,
>(
    layer_idx: usize,
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
    claim_points: &mut BTreeMap<usize, Vec<E>>,
    claims_storage: &mut BTreeMap<usize, BTreeMap<super::GKRAddress, E>>,
    gkr_storage: &mut GKRStorage<F, E>,
    batching_challenge: &mut E,
    seed: &mut TR::Seed,
    trace_len_after_reduction: usize,
    worker: &Worker,
) -> SumcheckIntermediateProofValues<F, E>
where
    [(); E::DEGREE]: Sized,
{
    #[cfg(target_arch = "aarch64")]
    if const { crate::gkr::prover::sumcheck_loop::windowed_mode::neon::is_bb_pair::<F, E>() } {
        return super::sumcheck_loop::evaluate_dimension_reducing_sumcheck_for_layer_lsb::<
            F,
            E,
            TR,
            _,
        >(
            |cur, dst, outs, rels, rp, tp, cs, cl| unsafe {
                aarch64::fused_chunk_neon::<E>(cur, dst, outs, rels, rp, tp, cs, cl)
            },
            layer_idx,
            layer,
            claim_points,
            claims_storage,
            gkr_storage,
            batching_challenge,
            seed,
            trace_len_after_reduction,
            worker,
        );
    }
    GKRBackend::<F, E>::dimension_reducing_sumcheck_for_layer::<TR>(
        &NaiveGKRBackend,
        layer_idx,
        layer,
        claim_points,
        claims_storage,
        gkr_storage,
        batching_challenge,
        seed,
        trace_len_after_reduction,
        worker,
    )
}
