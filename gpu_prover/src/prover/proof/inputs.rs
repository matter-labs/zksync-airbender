// Consolidated H2D bundle for prove() and commit_memory_from_transfers().
//
// Replaces the prior N-separate-transfers design: each pre-prove H2D piece
// (setup, decoder, inits_and_teardowns, tracing_data, memory caps,
// canonical_top_bits, external_challenges) used to own its own `Transfer<'a>`
// with its own `allocated`/`transferred` event pair. After this module, all
// H2D for one prove (or one commit_memory) lives on the bundle's single
// shared `Transfer`, so `prove()` does one `ensure_transferred` at the top
// instead of N, and the exec_stream prologue carries no callback or H2D
// before the first kernel.
//
// The per-piece wrappers (GpuGKRSetupTransfer, DecoderTableTransfer, etc.)
// keep their (host source, device buffer) state and gain a
// `schedule_transfer(&mut Transfer<'a>, context)` method that enqueues their
// H2D against the bundle's shared Transfer.

use std::marker::PhantomData;
use std::sync::Arc;

use era_cudart::result::CudaResult;
use fft::GoodAllocator;

use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, ProverContext};
use crate::primitives::field::{BF, E4};
use crate::primitives::static_host::{alloc_static_pinned_box_uninit, StaticPinnedBox};
use crate::primitives::transfer::Transfer;
use crate::prover::gkr::setup::GpuGKRSetupTransfer;
use crate::prover::trace::decoder::DecoderTableTransfer;
use crate::prover::trace::memory_transfer::GpuGKRMemoryTransfer;
use crate::prover::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use crate::upstream::{GKRExternalChallenges, NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES};

/// Number of `E4` slots needed to hold a `GKRExternalChallenges` value
/// (the linearization-challenge vector + 1 additive part).
pub(crate) const EXTERNAL_CHALLENGES_E4_LEN: usize =
    NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 1;

// ---------------------------------------------------------------------------
// CanonicalTopBitsTransfer
// ---------------------------------------------------------------------------

/// H2D wrapper for the canonical inits-and-teardowns top-bits transcript
/// prefix. The host source is `SchedulerHostAllocator`-backed and filled
/// once on the scheduling thread at construction; the bundle's shared
/// `Transfer` H2Ds it to device on `h2d_stream`.
///
/// Only constructed when the compiled circuit has at least one teardown set
/// (i.e. `canonical_top_bits.len() > 0`).
pub(crate) struct CanonicalTopBitsTransfer<'a> {
    pub(crate) host: Arc<StaticPinnedBox<u32>>,
    pub(crate) device: DeviceAllocation<u32>,
    _marker: PhantomData<&'a ()>,
}

impl<'a> CanonicalTopBitsTransfer<'a> {
    pub(crate) fn new(canonical_top_bits: &[u32], context: &ProverContext) -> CudaResult<Self> {
        assert!(
            !canonical_top_bits.is_empty(),
            "CanonicalTopBitsTransfer requires at least one top-bit entry",
        );
        let len = canonical_top_bits.len();
        let mut host = alloc_static_pinned_box_uninit::<u32>(len)?;
        host.copy_from_slice(canonical_top_bits);
        let device = context.alloc::<u32>(len, AllocationPlacement::BestFit)?;
        Ok(Self {
            host: Arc::new(host),
            device,
            _marker: PhantomData,
        })
    }

    pub(crate) fn schedule_transfer(
        &mut self,
        transfer: &mut Transfer<'a>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        transfer.schedule(self.host.clone(), &mut self.device, context)
    }
}

// ---------------------------------------------------------------------------
// ExternalChallengesTransfer
// ---------------------------------------------------------------------------

/// H2D wrapper for the GKR external challenges. The host source is
/// `SchedulerHostAllocator`-backed and filled at construction with the
/// flattened linearization-challenges + additive-part E4 layout consumed by
/// `transcript_commit_initial_chunked` and by backward as a device pointer.
///
/// The original Rust-side `GKRExternalChallenges` value is retained in
/// `value` because it is still consumed by forward layout construction and
/// terminal proof assembly. Backward only reads the device-resident copy.
pub(crate) struct ExternalChallengesTransfer<'a> {
    pub(crate) host: Arc<StaticPinnedBox<E4>>,
    pub(crate) device: DeviceAllocation<E4>,
    pub(crate) value: GKRExternalChallenges<BF, E4>,
    _marker: PhantomData<&'a ()>,
}

impl<'a> ExternalChallengesTransfer<'a> {
    pub(crate) fn new(
        value: GKRExternalChallenges<BF, E4>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let mut host = alloc_static_pinned_box_uninit::<E4>(EXTERNAL_CHALLENGES_E4_LEN)?;
        host[..NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES]
            .copy_from_slice(&value.permutation_argument_linearization_challenges);
        host[NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES] =
            value.permutation_argument_additive_part;
        let device =
            context.alloc::<E4>(EXTERNAL_CHALLENGES_E4_LEN, AllocationPlacement::BestFit)?;
        Ok(Self {
            host: Arc::new(host),
            device,
            value,
            _marker: PhantomData,
        })
    }

    pub(crate) fn schedule_transfer(
        &mut self,
        transfer: &mut Transfer<'a>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        transfer.schedule(self.host.clone(), &mut self.device, context)
    }
}

// ---------------------------------------------------------------------------
// GpuGKRProofTransfer
// ---------------------------------------------------------------------------

/// One bundle for everything `prove()` needs to land on the device before
/// any kernel runs. Owns a single shared `Transfer<'a>`; all per-piece
/// wrappers schedule their H2D against it. `prove()` does a single
/// `ensure_transferred` at the top.
pub(crate) struct GpuGKRProofTransfer<'a, A: GoodAllocator> {
    pub(crate) transfer: Transfer<'a>,
    pub(crate) setup: Option<GpuGKRSetupTransfer<'a>>,
    pub(crate) decoder: Option<DecoderTableTransfer<'a>>,
    pub(crate) inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a>>,
    pub(crate) tracing_data: Option<TracingDataTransfer<'a, A>>,
    pub(crate) memory: GpuGKRMemoryTransfer<'a>,
    pub(crate) canonical_top_bits: Option<CanonicalTopBitsTransfer<'a>>,
    pub(crate) external_challenges: ExternalChallengesTransfer<'a>,
}

/// Keepalive returned by `GpuGKRProofTransfer::into_keepalive()`. The proof
/// job holds this for its lifetime so every device allocation, host Arc,
/// and accumulated `Transfer` callback stays alive until `finish()`.
pub(crate) struct GpuGKRProofTransferKeepalive<'a, A: GoodAllocator> {
    _setup: Option<GpuGKRSetupTransfer<'a>>,
    _decoder: Option<DecoderTableTransfer<'a>>,
    _inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a>>,
    _tracing_data: Option<TracingDataTransfer<'a, A>>,
    _memory: GpuGKRMemoryTransfer<'a>,
    _canonical_top_bits: Option<CanonicalTopBitsTransfer<'a>>,
    _external_challenges: ExternalChallengesTransfer<'a>,
    _callbacks: Callbacks<'a>,
}

impl<'a, A: GoodAllocator + 'a> GpuGKRProofTransfer<'a, A> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        setup: Option<GpuGKRSetupTransfer<'a>>,
        decoder: Option<DecoderTableTransfer<'a>>,
        inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a>>,
        tracing_data: Option<TracingDataTransfer<'a, A>>,
        memory: GpuGKRMemoryTransfer<'a>,
        canonical_top_bits_source: &[u32],
        external_challenges_value: GKRExternalChallenges<BF, E4>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let canonical_top_bits = if canonical_top_bits_source.is_empty() {
            None
        } else {
            Some(CanonicalTopBitsTransfer::new(
                canonical_top_bits_source,
                context,
            )?)
        };
        let external_challenges =
            ExternalChallengesTransfer::new(external_challenges_value, context)?;
        let transfer = Transfer::new()?;
        // Every wrapper's device allocation has been made by now (sub-wrapper
        // `new()` calls above + the two `Transfer::new()`-internal events).
        // Record one shared `allocated` event so h2d_stream knows when device
        // memory is ready to be the H2D target.
        transfer.record_allocated(context)?;
        Ok(Self {
            transfer,
            setup,
            decoder,
            inits_and_teardowns,
            tracing_data,
            memory,
            canonical_top_bits,
            external_challenges,
        })
    }

    /// Issue every H2D on `h2d_stream` against the shared `Transfer`, then
    /// record the single `transferred` event the consumer waits on.
    pub(crate) fn schedule(&mut self, context: &ProverContext) -> CudaResult<()> {
        if let Some(setup) = self.setup.as_mut() {
            setup.schedule_transfer(&mut self.transfer, context)?;
        }
        if let Some(decoder) = self.decoder.as_mut() {
            decoder.schedule_transfer(&mut self.transfer, context)?;
        }
        if let Some(it) = self.inits_and_teardowns.as_mut() {
            it.schedule_transfer(&mut self.transfer, context)?;
        }
        if let Some(td) = self.tracing_data.as_mut() {
            td.schedule_transfer(&mut self.transfer, context)?;
        }
        self.memory.schedule_transfer(&mut self.transfer, context)?;
        if let Some(ctb) = self.canonical_top_bits.as_mut() {
            ctb.schedule_transfer(&mut self.transfer, context)?;
        }
        self.external_challenges
            .schedule_transfer(&mut self.transfer, context)?;
        self.transfer.record_transferred(context)
    }

    /// One exec-stream wait on the bundle's single `transferred` event.
    pub(crate) fn ensure_transferred(&self, context: &ProverContext) -> CudaResult<()> {
        self.transfer.ensure_transferred(context)
    }

    pub(crate) fn into_keepalive(self) -> GpuGKRProofTransferKeepalive<'a, A> {
        let Self {
            transfer,
            setup,
            decoder,
            inits_and_teardowns,
            tracing_data,
            memory,
            canonical_top_bits,
            external_challenges,
        } = self;
        GpuGKRProofTransferKeepalive {
            _setup: setup,
            _decoder: decoder,
            _inits_and_teardowns: inits_and_teardowns,
            _tracing_data: tracing_data,
            _memory: memory,
            _canonical_top_bits: canonical_top_bits,
            _external_challenges: external_challenges,
            _callbacks: transfer.into_callbacks(),
        }
    }
}

// ---------------------------------------------------------------------------
// GpuGKRCommitMemoryTransfer
// ---------------------------------------------------------------------------

/// Bundle for `commit_memory_from_transfers()` — same shape as
/// `GpuGKRProofTransfer` but only carrying the pieces the memory-commitment
/// path consumes (decoder, inits_and_teardowns, tracing_data; no setup,
/// memory caps, or challenges).
pub(crate) struct GpuGKRCommitMemoryTransfer<'a, A: GoodAllocator> {
    pub(crate) transfer: Transfer<'a>,
    pub(crate) decoder: Option<DecoderTableTransfer<'a>>,
    pub(crate) inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a>>,
    pub(crate) tracing_data: Option<TracingDataTransfer<'a, A>>,
}

pub(crate) struct GpuGKRCommitMemoryTransferKeepalive<'a, A: GoodAllocator> {
    pub(crate) decoder: Option<DecoderTableTransfer<'a>>,
    pub(crate) inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a>>,
    pub(crate) tracing_data: Option<TracingDataTransfer<'a, A>>,
    _callbacks: Callbacks<'a>,
}

impl<'a, A: GoodAllocator + 'a> GpuGKRCommitMemoryTransfer<'a, A> {
    pub(crate) fn new(
        decoder: Option<DecoderTableTransfer<'a>>,
        inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a>>,
        tracing_data: Option<TracingDataTransfer<'a, A>>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let transfer = Transfer::new()?;
        transfer.record_allocated(context)?;
        Ok(Self {
            transfer,
            decoder,
            inits_and_teardowns,
            tracing_data,
        })
    }

    pub(crate) fn schedule(&mut self, context: &ProverContext) -> CudaResult<()> {
        if let Some(decoder) = self.decoder.as_mut() {
            decoder.schedule_transfer(&mut self.transfer, context)?;
        }
        if let Some(it) = self.inits_and_teardowns.as_mut() {
            it.schedule_transfer(&mut self.transfer, context)?;
        }
        if let Some(td) = self.tracing_data.as_mut() {
            td.schedule_transfer(&mut self.transfer, context)?;
        }
        self.transfer.record_transferred(context)
    }

    pub(crate) fn ensure_transferred(&self, context: &ProverContext) -> CudaResult<()> {
        self.transfer.ensure_transferred(context)
    }

    pub(crate) fn into_keepalive(self) -> GpuGKRCommitMemoryTransferKeepalive<'a, A> {
        let Self {
            transfer,
            decoder,
            inits_and_teardowns,
            tracing_data,
        } = self;
        GpuGKRCommitMemoryTransferKeepalive {
            decoder,
            inits_and_teardowns,
            tracing_data,
            _callbacks: transfer.into_callbacks(),
        }
    }
}
