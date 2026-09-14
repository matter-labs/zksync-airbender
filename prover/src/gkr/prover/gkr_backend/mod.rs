//! GKR-argument counterpart of the FFT/tree [`Backend`](super::backend::Backend)
//! trait: pins the heavy per-layer operations of the GKR prover behind a
//! swappable strategy so alternative implementations (LSB-binding windowed /
//! uniskip engines, GPU offload) can replace the execution while keeping the
//! transcript BYTE-IDENTICAL for identical schedules.
//!
//! Dispatch mirrors the `Backend` pattern exactly: the prover entry points
//! take a `&impl GKRBackend<F, E>`, every implementation lives in its own
//! arch-gated submodule ([`naive`] is portable, [`neon`] is
//! `aarch64`-only), and [`DefaultBabyBearGKRBackend`] is the arch-conditional
//! alias concrete BabyBear callers should use. NO function in this module
//! tree outside the arch-gated submodules contains platform-specific code —
//! a backend fully controls which architectures it compiles for.
//!
//! Migration plan (kept incremental so `gkr_self_checks` stays green at every
//! stage):
//! 1. dimension-reducing layers (fixed gate set: pairwise products + logup
//!    reduction) — forward path and backward (sumcheck) path; DONE.
//! 2. same-size layer sumchecks (windowed / uniskip schedules over the
//!    bracket-preserving compiled relations);
//! 3. remaining glue (eq-table maintenance, folds).

use crate::allocation_pool::AllocationPool;
use std::collections::BTreeMap;

use super::dimension_reduction::forward::DimensionReducingInputOutput;
use super::{GKRStorage, SumcheckIntermediateProofValues};
use crate::gkr::prover::EvaluationPointEntry;
use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};
use field::{Field, FieldExtension, PrimeField};
use transcript::Transcript;
use worker::{IterableWithGeometry, Worker};

mod naive;
pub use naive::NaiveGKRBackend;

#[cfg(target_arch = "aarch64")]
mod neon;
#[cfg(target_arch = "aarch64")]
pub use neon::NeonGKRBackend;

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
mod avx2;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
pub use avx2::Avx2GKRBackend;

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
mod avx512;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
mod avx512_dr;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
pub use avx512::X86GKRBackend;

/// The GKR backend concrete BabyBear/Ext4 callers should default to: the
/// NEON-specialized backend on aarch64, the AVX2-specialized backend on
/// AVX2-enabled x86-64 builds, the portable naive backend elsewhere.
/// Mirrors [`DefaultBabyBearBackend`](super::backend::DefaultBabyBearBackend).
#[cfg(target_arch = "aarch64")]
pub type DefaultBabyBearGKRBackend = NeonGKRBackend;
/// The GKR backend concrete BabyBear/Ext4 callers should default to: on
/// AVX2-enabled x86-64 builds the runtime-dispatching backend (AVX-512
/// same-size kernels when `avx512f` is detected, AVX2 otherwise) with the
/// pre-touched fold buffer pool.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
pub type DefaultBabyBearGKRBackend = X86GKRBackend;
/// The GKR backend concrete BabyBear/Ext4 callers should default to: the
/// NEON-specialized backend on aarch64, the AVX2 backend on AVX2-enabled
/// x86-64 builds, the portable naive backend elsewhere.
#[cfg(not(any(
    target_arch = "aarch64",
    all(target_arch = "x86_64", target_feature = "avx2")
)))]
pub type DefaultBabyBearGKRBackend = NaiveGKRBackend;

/// Strategy for the GKR prover's per-layer heavy operations. Methods are
/// generic (no `dyn` use is intended); implementations must be pure with
/// respect to the transcript: for the same schedule, every backend produces
/// identical field values in identical order.
///
/// # Sumcheck round wire format (contract for ALL layer types)
///
/// Every scalar sumcheck round emitted through this trait — the same-size
/// layers AND the dimension-reducing layers alike — uses the SAME normalized
/// single-eq-factor cubic form: the message is the 4 monomial coefficients
/// of `q_s(X) = eq(tau_s, X) * h_s(X)` (the LOCAL eq factor only, built by
/// `output_univariate_monomial_form_max_quadratic` from the claim divided by
/// the PREVIOUS round's factor), the chaining is
/// `eq(tau_{s-1}, r_{s-1}) * (q_s(0) + q_s(1)) == claim_s` with
/// `claim_{s+1} = q_s(r_s)`, and the layer's final identity is
/// `claim == eq(tau_last, r_last) * gate(final values)`. The generated
/// verifier checks every layer type with the ONE shared round routine
/// (`verify_sumcheck_rounds`); verifier bytecode size matters, so do not
/// introduce a second wire format.
pub trait GKRBackend<F: PrimeField, E: FieldExtension<F> + Field>: Send + Sync {
    /// Forward (output-construction) evaluation of ALL dimension-reducing
    /// layers, mirroring
    /// [`evaluate_dimension_reduction_forward`](super::dimension_reduction::forward::evaluate_dimension_reduction_forward)'s
    /// contract: consumes the grand-product / logup inputs from `storage`,
    /// materializes every intermediate layer, and returns the first layer
    /// index for the backward pass plus the per-layer input/output
    /// descriptions.
    fn dimension_reduction_forward(
        &self,
        storage: &mut GKRStorage<F, E>,
        compiled_circuit: &GKRCircuitArtifact<F>,
        initial_trace_log_2: usize,
        final_trace_log_2: usize,
        pool: &dyn AllocationPool<F, E>,
        worker: &Worker,
    ) -> (
        usize,
        BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
    );

    /// Backend-owned reusable state for the WHOLE dimension-reducing
    /// backward pass: scratch buffers and any other precomputed elements the
    /// backend wants to carry across layers. The shape is entirely the
    /// backend's business — a non-vectorized backend carries plainly typed
    /// row accumulators, a SIMD backend may carry vector-compatible erased
    /// slots. Constructed once by the external driver loop from the largest
    /// layer's shape and passed by `&mut` into every per-layer call.
    type DimensionReducingBuffer;

    /// Constructor for the pass-wide buffers: `max_rounds` is the largest
    /// layer's round count (log2 of its post-reduction trace length),
    /// `max_polys` the largest distinct-input-poly count of any layer.
    fn make_dim_reducing_work_buffers(
        &self,
        max_rounds: usize,
        max_polys: usize,
        pool: &dyn AllocationPool<F, E>,
        worker: &Worker,
    ) -> Self::DimensionReducingBuffer;

    /// Hands the pass-wide dimension-reducing buffers back after the last
    /// dimension-reducing layer (the bundled backends return the scratch to
    /// the pool; the default drops it).
    fn recycle_dim_reducing_work_buffers(
        &self,
        buffers: Self::DimensionReducingBuffer,
        _pool: &dyn AllocationPool<F, E>,
    ) {
        drop(buffers);
    }

    /// Statically resolved fold-buffer shapes of the whole backward pass —
    /// `[(dimension-reducing: max polys, capacity), (same-size: max polys,
    /// capacity)]` — offered ONCE before the pass so the pool can be
    /// pre-filled with touched buffers. The default ignores them.
    fn prepare_fold_pool(
        &self,
        _shapes: &[(usize, usize)],
        _pool: &dyn AllocationPool<F, E>,
        _worker: &Worker,
    ) {
    }

    /// Hands a same-size layer's fold buffers back after the layer: to the
    /// pool.
    fn recycle_same_size_fold_buffers(
        &self,
        buffers: Vec<Box<[core::mem::MaybeUninit<E>]>>,
        pool: &dyn AllocationPool<F, E>,
    ) {
        for b in buffers {
            pool.give_box(b);
        }
    }

    /// Backward (sumcheck) pass over ONE dimension-reducing layer. The
    /// dimension-reducing gate set is fixed (pairwise products and logup
    /// reduction gates only), so implementations may specialize far more
    /// aggressively than for the same-size layers. `schedule` describes the
    /// leading windowed passes of the round plan (empty = all-naive rounds);
    /// it is an execution strategy — every backend emits the same transcript
    /// messages for the same layer regardless of it.
    #[allow(clippy::too_many_arguments)]
    fn dimension_reducing_sumcheck_for_layer<TR: Transcript<F, E>>(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        layer_idx: usize,
        layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
        claim_points: &mut BTreeMap<usize, Vec<EvaluationPointEntry<E>>>,
        claims_storage: &mut BTreeMap<usize, BTreeMap<super::GKRAddress, E>>,
        gkr_storage: &mut GKRStorage<F, E>,
        batching_challenge: &mut E,
        seed: &mut TR::Seed,
        trace_len_after_reduction: usize,
        pool: &dyn AllocationPool<F, E>,
        worker: &Worker,
        buffers: &mut Self::DimensionReducingBuffer,
    ) -> SumcheckIntermediateProofValues<F, E>
    where
        [(); E::DEGREE]: Sized;

    /// Fold-scratch buffer of the all-naive same-size schedule. The naive
    /// loop's lazy folds live inside `GKRStorage`, so the bundled backends
    /// use an empty buffer set here; the type exists so alternative
    /// backends can carry state of their own.
    type NaiveSameSizeFoldBuffer;
    /// Fold-scratch buffer of the windowed same-size chain (one per input
    /// poly of the layer's batched relation).
    type WindowedSameSizeFoldBuffer;
    /// Fold-scratch buffer of the uniskip same-size chain (one per input
    /// poly of the layer's batched relation).
    type UniskipSameSizeFoldBuffer;

    /// The batched WHIR proximity polynomial straight from the base-layer
    /// columns: `dst[t.dst_offset + i] += t.power * t.column[i]` over every
    /// term (`ext += ext * base`), every `dst` element written exactly once
    /// (zero where no term lands). `dst` is `k` slices of one column length
    /// (`k > 1` only for packed commitments, whose sub-polys are concatenated
    /// block by block). The default is the worker-parallel scalar loop;
    /// backends override it with vector kernels. The values must equal
    /// [`accumulate_base_columns_into_scalar`]'s.
    fn accumulate_base_columns_into(
        &self,
        dst: &mut [core::mem::MaybeUninit<E>],
        terms: &[BatchedBaseColumn<'_, F, E>],
        worker: &Worker,
    ) {
        accumulate_base_columns_into_scalar::<F, E>(dst, terms, worker);
    }

    /// Constructor for the all-naive same-size fold buffers: takes the
    /// validated schedule, the trace length, and the input poly counts
    /// (base, extension) that require a buffer; returns one buffer per poly
    /// that needs one.
    /// One LSB folding step of a WHIR-style poly: `dst[i] = src[2i] +
    /// challenge * (src[2i+1] - src[2i])` for `i < src.len() / 2`, written
    /// into a SEPARATE buffer (ping-pong) so no serial compaction pass is
    /// needed. Used for the WHIR equality poly (see
    /// [`crate::gkr::whir::ping_pong::PingPongPoly`]); the values must equal
    /// [`crate::gkr::whir::fold_eq_poly`]'s. The default is the worker-parallel
    /// scalar loop; backends override it with vector kernels.
    fn fold_eq_poly_into(
        &self,
        src: &[E],
        challenge: &E,
        dst: &mut [core::mem::MaybeUninit<E>],
        worker: &Worker,
    ) {
        fold_eq_poly_into_scalar::<F, E>(src, challenge, dst, worker);
    }

    fn make_naive_same_size_fold_buffers(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        trace_len: usize,
        num_base_polys: usize,
        num_ext_polys: usize,
        pool: &dyn AllocationPool<F, E>,
    ) -> Vec<Self::NaiveSameSizeFoldBuffer>;

    /// Constructor for the windowed-chain fold buffers (same contract as
    /// [`GKRBackend::make_naive_same_size_fold_buffers`]).
    fn make_windowed_same_size_fold_buffers(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        trace_len: usize,
        num_base_polys: usize,
        num_ext_polys: usize,
        pool: &dyn AllocationPool<F, E>,
    ) -> Vec<Self::WindowedSameSizeFoldBuffer>;

    /// Constructor for the uniskip-chain fold buffers (same contract as
    /// [`GKRBackend::make_naive_same_size_fold_buffers`]).
    fn make_uniskip_same_size_fold_buffers(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        trace_len: usize,
        num_base_polys: usize,
        num_ext_polys: usize,
        pool: &dyn AllocationPool<F, E>,
    ) -> Vec<Self::UniskipSameSizeFoldBuffer>;

    /// The per-layer same-size chain EXECUTOR (compiled SoA program +
    /// whatever kernel tables the platform needs) — the analog of the
    /// dimension-reducing chunk kernels. Arch-specific concrete types live
    /// in the arch-gated backend modules; no platform dispatch exists
    /// anywhere else.
    type SameSizeChain: crate::gkr::prover::sumcheck_loop::SameSizeChainOps<F, E>;

    /// Constructor for the per-layer chain executor from the layer's
    /// compiled SoA program.
    fn make_same_size_chain(
        &self,
        prog: crate::gkr::prover::sumcheck_loop::OwnedSoaProgram<F, E>,
    ) -> Self::SameSizeChain
    where
        F: field::TwoAdicField;

    /// Sumcheck over ONE same-size layer: builds the layer's batched
    /// relation, selects + validates the schedule from the
    /// [`ProverConfig`](crate::gkr::prover_config::ProverConfig) by layer
    /// width, branches into the all-naive / windowed / uniskip case engine
    /// (constructing that case's fold buffers through the constructors
    /// above), and emits the layer's claims and claim point.
    #[allow(clippy::too_many_arguments)]
    fn evaluate_same_size_sumcheck_for_layer<TR: Transcript<F, E>>(
        &self,
        layer_idx: usize,
        layer: &cs::gkr_compiler::GKRLayerDescription<F>,
        claim_points: &mut BTreeMap<usize, Vec<EvaluationPointEntry<E>>>,
        claims_storage: &mut BTreeMap<usize, BTreeMap<super::GKRAddress, E>>,
        gkr_storage: &mut GKRStorage<F, E>,
        batching_challenge: &mut E,
        trace_len: usize,
        lookup_challenges_multiplicative_part: E,
        lookup_challenges_additive_part: E,
        inits_and_teardowns_top_bits: &[u32],
        address_high_bits_shift: u32,
        external_challenges: &super::GKRExternalChallenges<F, E>,
        prover_config: &crate::gkr::prover_config::ProverConfig,
        seed: &mut TR::Seed,
        pool: &dyn AllocationPool<F, E>,
        worker: &Worker,
    ) -> SumcheckIntermediateProofValues<F, E>
    where
        F: field::TwoAdicField,
        [(); E::DEGREE]: Sized;
}

/// Fold-scratch capacity (elements per input poly) of the same-size chain
/// engines for the given STRICT schedule: the chain's [`FoldBufferTracker`]s
/// ping-pong between the first pass's output region (`trace_len / 2^w`) and
/// the region right behind it (at most half that), so `3/2` of the first
/// output covers every later stage. Returns 0 for all-naive schedules (the
/// naive loop's lazy folds live inside `GKRStorage`).
///
/// [`FoldBufferTracker`]: super::dimension_reduction::lsb_backward::FoldBufferTracker
pub fn same_size_chain_fold_capacity(
    schedule: &[crate::gkr::prover_config::SumcheckStep],
    trace_len: usize,
) -> usize {
    use crate::gkr::prover_config::SumcheckStep;
    let first_window = match schedule.first() {
        Some(SumcheckStep::UniskipInitial { window })
        | Some(SumcheckStep::WindowInitial { window }) => *window,
        _ => return 0,
    };
    let first_out = trace_len >> first_window;
    first_out + first_out / 2
}

/// Pass-wide work buffers shared by the bundled backends for the
/// dimension-reducing backward pass: allocated ONCE for the largest layer
/// and reused down the chain. Uninit throughout -- every consumer writes a
/// region before reading it, and untouched tail pages of the max-sized
/// buffers never fault.
///
/// `S` is the chunk kernel's per-row tri-scratch slot type: the naive
/// backend uses plainly typed `[E; 2]` rows, the NEON backend keeps
/// vector-compatible 16-aligned 32-byte `[u128; 2]` slots. Backends that
/// need a different shape entirely define their own
/// [`GKRBackend::DimensionReducingBuffer`] instead.
pub struct DimReducingSumcheckScratch<E, S> {
    /// per-poly fold scratch, sized for the largest layer (3/4 of its 2m
    /// input length per poly)
    pub fold: Vec<Box<[core::mem::MaybeUninit<E>]>>,
    /// per-worker-slot tri scratch for the chunk kernels
    pub tri: Vec<Box<[core::mem::MaybeUninit<S>]>>,
}

impl<E, S> DimReducingSumcheckScratch<E, S> {
    pub fn new<F, EE>(
        max_rounds: usize,
        max_polys: usize,
        pool: &dyn AllocationPool<F, EE>,
        worker: &Worker,
    ) -> Self {
        let m = 1usize << max_rounds;
        let tri_cap = (m / 2)
            .div_ceil(worker.num_cores)
            .max(crate::gkr::PAR_THRESHOLD);
        Self {
            fold: (0..max_polys)
                .map(|_| pool.alloc_box::<E>(m + m / 2))
                .collect(),
            tri: (0..worker.num_cores)
                .map(|_| pool.alloc_box::<S>(tri_cap))
                .collect(),
        }
    }

    /// Return every buffer to the pool.
    pub fn release<F, EE>(self, pool: &dyn AllocationPool<F, EE>) {
        for b in self.fold {
            pool.give_box(b);
        }
        for b in self.tri {
            pool.give_box(b);
        }
    }
}

/// One base-layer column's share of the batched WHIR proximity polynomial
/// (see [`GKRBackend::accumulate_base_columns_into`]).
#[derive(Clone, Copy)]
pub struct BatchedBaseColumn<'a, F, E> {
    /// The column's boolean-hypercube evaluations.
    pub column: &'a [F],
    /// Its batching weight (a power of the batching challenge).
    pub power: E,
    /// Where the column lands in `dst` (a multiple of the column length).
    pub dst_offset: usize,
}

/// Rows per accumulation block: the block of the destination stays in L1
/// while the columns stream through it once each.
const ACCUMULATE_BLOCK: usize = 1 << 12;

/// The scalar, worker-parallel reference of
/// [`GKRBackend::accumulate_base_columns_into`].
pub fn accumulate_base_columns_into_scalar<F: PrimeField, E: FieldExtension<F> + Field>(
    dst: &mut [core::mem::MaybeUninit<E>],
    terms: &[BatchedBaseColumn<'_, F, E>],
    worker: &Worker,
) {
    let n = terms.first().map(|t| t.column.len()).unwrap_or(dst.len());
    assert!(n > 0 && dst.len() % n == 0);
    for t in terms.iter() {
        assert_eq!(t.column.len(), n);
        assert!(t.dst_offset % n == 0 && t.dst_offset + n <= dst.len());
    }
    let slices = dst.len() / n;
    for y in 0..slices {
        let off = y * n;
        let slice_terms: Vec<&BatchedBaseColumn<'_, F, E>> =
            terms.iter().filter(|t| t.dst_offset == off).collect();
        let dst_slice = &mut dst[off..off + n];
        let slice_terms = &slice_terms;
        worker.scope_with_threshold(n, crate::gkr::PAR_THRESHOLD, |scope, geometry| {
            dst_slice
                .chunks_for_geometry_mut(geometry)
                .enumerate()
                .for_each(|(idx, chunk)| {
                    let row0 = geometry.get_chunk_start_pos(idx);
                    Worker::smart_spawn(scope, idx == geometry.len() - 1, move |_| {
                        for (b, block) in chunk.chunks_mut(ACCUMULATE_BLOCK).enumerate() {
                            let start = row0 + b * ACCUMULATE_BLOCK;
                            for d in block.iter_mut() {
                                d.write(E::ZERO);
                            }
                            // SAFETY: just initialized
                            let block: &mut [E] = unsafe {
                                core::slice::from_raw_parts_mut(
                                    block.as_mut_ptr() as *mut E,
                                    block.len(),
                                )
                            };
                            for t in slice_terms.iter() {
                                let src = &t.column[start..start + block.len()];
                                for (d, s) in block.iter_mut().zip(src.iter()) {
                                    d.add_assign_product_with_base(&t.power, s);
                                }
                            }
                        }
                    });
                })
        });
    }
}

#[cfg(test)]
mod accumulate_scalar_tests {
    use super::*;
    use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
    use field::Rand;

    /// The scalar accumulation against the definition, over odd lengths,
    /// two packed slices and the empty term list.
    #[test]
    fn accumulate_base_columns_scalar_matches_definition() {
        let worker = Worker::new_with_num_threads(3);
        let mut rng = rand::thread_rng();
        for (n, slices, num_cols) in [
            (1usize << 10, 1usize, 5usize),
            (4097, 2, 7),
            (37, 1, 3),
            (1 << 13, 1, 0),
        ] {
            let cols: Vec<Vec<BabyBearField>> = (0..num_cols)
                .map(|_| {
                    (0..n)
                        .map(|_| BabyBearField::random_element(&mut rng))
                        .collect()
                })
                .collect();
            let terms: Vec<BatchedBaseColumn<'_, BabyBearField, BabyBearExt4>> = cols
                .iter()
                .enumerate()
                .map(|(j, c)| BatchedBaseColumn {
                    column: &c[..],
                    power: BabyBearExt4::random_element(&mut rng),
                    dst_offset: (j % slices) * n,
                })
                .collect();
            let len = n * slices;
            let mut a: Vec<core::mem::MaybeUninit<BabyBearExt4>> = Vec::with_capacity(len);
            unsafe { a.set_len(len) };
            accumulate_base_columns_into_scalar::<BabyBearField, BabyBearExt4>(
                &mut a, &terms, &worker,
            );
            let a: Vec<BabyBearExt4> = a.iter().map(|x| unsafe { x.assume_init() }).collect();
            for y in 0..slices {
                for i in 0..n {
                    let mut v = BabyBearExt4::ZERO;
                    for t in terms.iter().filter(|t| t.dst_offset == y * n) {
                        let mut w = t.power;
                        w.mul_assign_by_base(&t.column[i]);
                        v.add_assign(&w);
                    }
                    assert_eq!(
                        a[y * n + i],
                        v,
                        "n {n} slices {slices} cols {num_cols} at {y}/{i}"
                    );
                }
            }
        }
    }
}

/// The scalar, worker-parallel reference of [`GKRBackend::fold_eq_poly_into`].
pub fn fold_eq_poly_into_scalar<F: PrimeField, E: FieldExtension<F> + Field>(
    src: &[E],
    challenge: &E,
    dst: &mut [core::mem::MaybeUninit<E>],
    worker: &Worker,
) {
    let half = src.len() / 2;
    assert!(src.len().is_power_of_two());
    assert!(dst.len() >= half);
    if half == 0 {
        return;
    }
    let pairs = src.as_chunks::<2>().0;
    let dst = &mut dst[..half];
    let ch = *challenge;
    worker.scope_with_threshold(half, crate::gkr::PAR_THRESHOLD, |scope, geometry| {
        pairs
            .chunks_for_geometry(geometry)
            .zip(dst.chunks_for_geometry_mut(geometry))
            .enumerate()
            .for_each(|(idx, (src_chunk, dst_chunk))| {
                Worker::smart_spawn(scope, idx == geometry.len() - 1, |_| {
                    for ([a, b], d) in src_chunk.iter().zip(dst_chunk.iter_mut()) {
                        let mut t = *b;
                        t.sub_assign(a);
                        t.mul_assign(&ch);
                        t.add_assign(a);
                        d.write(t);
                    }
                });
            })
    });
}
