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
}

/// Batch allocation of the SAME-SIZE layers' fold buffers: ONE call per
/// layer, one uninitialized buffer per input poly keyed by address (after
/// the first fold every poly lives in the extension field). The LSB chain
/// writes each fold output into a fresh dense region, so the footprint is
/// the sum of the pass regions plus one live-sized region for a scalar
/// tail. Buffers are `Box<[MaybeUninit<E>]>` (uninit is free on fresh pages
/// and skips the memset on allocator-reused ones); the engine communicates
/// positions via pointer ranges, never reallocating, so the map also guards
/// against accidental deallocation.
pub fn allocate_same_size_fold_buffers<F: PrimeField, E: FieldExtension<F> + Field>(
    schedule: &[crate::gkr::prover_config::SumcheckStep],
    trace_len: usize,
    base_polys: &[super::GKRAddress],
    ext_polys: &[super::GKRAddress],
) -> BTreeMap<super::GKRAddress, Box<[core::mem::MaybeUninit<E>]>> {
    let first_fold = schedule
        .first()
        .map(|s| 1usize << s.variables_bound())
        .unwrap_or(2);
    let after_first = (trace_len / first_fold).max(2);
    // the LSB chain writes every fold output into a fresh dense region:
    // one region per leading pass (m/8, m/64, ...), then -- if the schedule
    // truncates into scalar tail rounds -- the tail's halving folds, which
    // sum to strictly less than one extra live-sized region
    let per_poly = {
        let n = trace_len.trailing_zeros() as usize;
        let passes = schedule
            .iter()
            .take_while(|s| {
                matches!(
                    s,
                    crate::gkr::prover_config::SumcheckStep::UniskipInitial { .. }
                        | crate::gkr::prover_config::SumcheckStep::Uniskip { .. }
                        | crate::gkr::prover_config::SumcheckStep::WindowedOp(_)
                )
            })
            .count()
            .max(1)
            .min(n / 3);
        let mut cap = 0usize;
        let mut live = trace_len;
        for _ in 0..passes {
            live >>= 3;
            cap += live;
        }
        if 3 * passes < n {
            cap += live;
        }
        cap.max(2)
    };
    base_polys
        .iter()
        .chain(ext_polys.iter())
        .map(|addr| (*addr, Box::new_uninit_slice(per_poly)))
        .collect()
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
