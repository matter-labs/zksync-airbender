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

use std::collections::BTreeMap;

use super::dimension_reduction::forward::DimensionReducingInputOutput;
use super::{GKRStorage, SumcheckIntermediateProofValues};
use crate::gkr::prover::EvaluationPointEntry;
use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};
use field::{Field, FieldExtension, PrimeField};
use transcript::Transcript;
use worker::Worker;

mod naive;
pub use naive::NaiveGKRBackend;

#[cfg(target_arch = "aarch64")]
mod neon;
#[cfg(target_arch = "aarch64")]
pub use neon::NeonGKRBackend;

/// The GKR backend concrete BabyBear/Ext4 callers should default to: the
/// NEON-specialized backend on aarch64, the portable naive backend elsewhere.
/// Mirrors [`DefaultBabyBearBackend`](super::backend::DefaultBabyBearBackend).
#[cfg(target_arch = "aarch64")]
pub type DefaultBabyBearGKRBackend = NeonGKRBackend;
/// The GKR backend concrete BabyBear/Ext4 callers should default to: the
/// NEON-specialized backend on aarch64, the portable naive backend elsewhere.
#[cfg(not(target_arch = "aarch64"))]
pub type DefaultBabyBearGKRBackend = NaiveGKRBackend;

/// Strategy for the GKR prover's per-layer heavy operations. Methods are
/// generic (no `dyn` use is intended); implementations must be pure with
/// respect to the transcript: for the same schedule, every backend produces
/// identical field values in identical order.
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
        worker: &Worker,
    ) -> Self::DimensionReducingBuffer;

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

    /// Constructor for the all-naive same-size fold buffers: takes the
    /// validated schedule, the trace length, and the input poly counts
    /// (base, extension) that require a buffer; returns one buffer per poly
    /// that needs one.
    fn make_naive_same_size_fold_buffers(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        trace_len: usize,
        num_base_polys: usize,
        num_ext_polys: usize,
    ) -> Vec<Self::NaiveSameSizeFoldBuffer>;

    /// Constructor for the windowed-chain fold buffers (same contract as
    /// [`GKRBackend::make_naive_same_size_fold_buffers`]).
    fn make_windowed_same_size_fold_buffers(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        trace_len: usize,
        num_base_polys: usize,
        num_ext_polys: usize,
    ) -> Vec<Self::WindowedSameSizeFoldBuffer>;

    /// Constructor for the uniskip-chain fold buffers (same contract as
    /// [`GKRBackend::make_naive_same_size_fold_buffers`]).
    fn make_uniskip_same_size_fold_buffers(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        trace_len: usize,
        num_base_polys: usize,
        num_ext_polys: usize,
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
    pub fn new(max_rounds: usize, max_polys: usize, worker: &Worker) -> Self {
        let m = 1usize << max_rounds;
        let tri_cap = (m / 2)
            .div_ceil(worker.num_cores)
            .max(crate::gkr::PAR_THRESHOLD);
        Self {
            fold: (0..max_polys)
                .map(|_| Box::new_uninit_slice(m + m / 2))
                .collect(),
            tri: (0..worker.num_cores)
                .map(|_| Box::new_uninit_slice(tri_cap))
                .collect(),
        }
    }
}
