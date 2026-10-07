// Consolidated H2D bundle for prove() and commit_memory_from_transfers():
// one shared Transfer for every pre-prove H2D piece (setup, decoder,
// inits_and_teardowns, tracing_data, memory caps, top_bits,
// external_challenges), so prove() does a single ensure_transferred.

use std::marker::PhantomData;
use std::sync::Arc;

use era_cudart::result::CudaResult;
use fft::GoodAllocator;

use crate::upstream::{GKRExternalChallenges, NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr::setup::{GpuGKRSetupHost, GpuGKRSetupTransfer};
use gpu_prover_context::transfer::{Transfer, TransferKeepalive};
use gpu_prover_context::ProverContext;
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::memory_transfer::GpuGKRMemoryTransfer;
use gpu_trace::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};

/// Number of `E4` slots needed to hold a `GKRExternalChallenges` value
/// (the linearization-challenge vector + 1 additive part).
pub(crate) const EXTERNAL_CHALLENGES_E4_LEN: usize =
    NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 1;

// ---------------------------------------------------------------------------
// TopBitsTransfer
// ---------------------------------------------------------------------------

/// H2D wrapper for the inits-and-teardowns top-bits transcript prefix, staged
/// through the context's pinned staging buffer on `h2d_stream`.
///
/// Only constructed when the compiled circuit has at least one teardown set
/// (i.e. `top_bits.len() > 0`).
pub(crate) struct TopBitsTransfer<'a> {
    pub(crate) device: DeviceAllocation<u32>,
    _marker: PhantomData<&'a ()>,
}

impl<'a> TopBitsTransfer<'a> {
    pub(crate) fn new(top_bits: &[u32], context: &ProverContext) -> CudaResult<Self> {
        assert!(
            !top_bits.is_empty(),
            "TopBitsTransfer requires at least one top-bit entry",
        );
        let device = context.alloc::<u32>(top_bits.len(), AllocationPlacement::BestFit)?;
        Ok(Self {
            device,
            _marker: PhantomData,
        })
    }
}

// ---------------------------------------------------------------------------
// ExternalChallengesTransfer
// ---------------------------------------------------------------------------

/// H2D wrapper for the GKR external challenges, staged through the context's
/// pinned staging buffer on `h2d_stream` in the flattened
/// linearization-challenges + additive-part E4 layout consumed by
/// `transcript_commit_initial_chunked` and by backward as a device pointer.
///
/// The original Rust-side `GKRExternalChallenges` value is retained in
/// `value` because it is still consumed by forward layout construction and
/// terminal proof assembly. Backward only reads the device-resident copy.
pub(crate) struct ExternalChallengesTransfer<'a> {
    pub(crate) device: DeviceAllocation<E4>,
    pub(crate) value: GKRExternalChallenges<BF, E4>,
    _marker: PhantomData<&'a ()>,
}

impl<'a> ExternalChallengesTransfer<'a> {
    pub(crate) fn new(
        value: GKRExternalChallenges<BF, E4>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let device =
            context.alloc::<E4>(EXTERNAL_CHALLENGES_E4_LEN, AllocationPlacement::BestFit)?;
        Ok(Self {
            device,
            value,
            _marker: PhantomData,
        })
    }

    pub(crate) fn stage_transfer(&mut self, transfer: &mut Transfer<'a>) {
        let challenges = &self.value.permutation_argument_linearization_challenges;
        let flattened: [E4; EXTERNAL_CHALLENGES_E4_LEN] = std::array::from_fn(|i| {
            challenges
                .get(i)
                .copied()
                .unwrap_or(self.value.permutation_argument_additive_part)
        });
        transfer.stage(&flattened, &mut self.device);
    }
}

// ---------------------------------------------------------------------------
// GpuGKRProofTransfer
// ---------------------------------------------------------------------------

/// One bundle for everything `prove()` needs to land on the device before
/// any kernel runs. Owns a single shared `Transfer<'a>`; all per-piece
/// wrappers schedule their H2D against it. `prove()` does a single
/// `ensure_transferred` at the top.
pub struct GpuGKRProofTransfer<'a, A: GoodAllocator> {
    pub(crate) transfer: Transfer<'a>,
    pub(crate) setup: Option<GpuGKRSetupTransfer<'a>>,
    pub(crate) decoder: Option<DecoderTableTransfer<'a>>,
    pub(crate) inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a, A>>,
    pub(crate) tracing_data: Option<TracingDataTransfer<'a, A>>,
    pub(crate) memory: GpuGKRMemoryTransfer<'a>,
    pub(crate) top_bits: Option<TopBitsTransfer<'a>>,
    /// Host copy of the SAME per-circuit inits-and-teardowns top bits staged
    /// in `top_bits` (empty when the circuit has no teardown sets): the global
    /// address window each set holds, or all zeros for TRIVIAL (dummy) unified
    /// chunks. Consumed at scheduling time by the forward plan, backward
    /// blueprints, and terminal proof assembly.
    pub(crate) top_bits_host: Vec<u32>,
    pub(crate) external_challenges: ExternalChallengesTransfer<'a>,
}

/// Host-only keepalive after every device input's last reader is enqueued.
/// Direct-copy setup sources and the Transfer's sources survive to finish().
pub(crate) struct GpuGKRProofTransferKeepalive<'a> {
    pub(super) _setup_host: Option<Arc<GpuGKRSetupHost>>,
    pub(super) _transfer: TransferKeepalive<'a>,
}

impl<'a, A: GoodAllocator + 'a> GpuGKRProofTransfer<'a, A> {
    pub fn new(
        setup: Option<GpuGKRSetupTransfer<'a>>,
        decoder: Option<DecoderTableTransfer<'a>>,
        inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a, A>>,
        tracing_data: Option<TracingDataTransfer<'a, A>>,
        memory: GpuGKRMemoryTransfer<'a>,
        top_bits_source: &[u32],
        external_challenges_value: GKRExternalChallenges<BF, E4>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let top_bits = if top_bits_source.is_empty() {
            None
        } else {
            Some(TopBitsTransfer::new(top_bits_source, context)?)
        };
        let external_challenges =
            ExternalChallengesTransfer::new(external_challenges_value, context)?;
        let transfer = Transfer::new()?;
        // Every device input is allocated by now; h2d_stream waits on this
        // event before the bundle's copies.
        transfer.record_allocated(context)?;
        Ok(Self {
            transfer,
            setup,
            decoder,
            inits_and_teardowns,
            tracing_data,
            memory,
            top_bits,
            top_bits_host: top_bits_source.to_vec(),
            external_challenges,
        })
    }

    /// Issue every H2D on `h2d_stream` against the shared `Transfer`, then
    /// record the single `transferred` event the consumer waits on. Small
    /// inputs are staged first so they share one fill and lead the copies.
    pub fn schedule(&mut self, context: &ProverContext) -> CudaResult<()> {
        self.memory.stage_transfer(&mut self.transfer);
        if let Some(top_bits) = self.top_bits.as_mut() {
            self.transfer
                .stage(&self.top_bits_host, &mut top_bits.device);
        }
        self.external_challenges.stage_transfer(&mut self.transfer);
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
        self.transfer.record_transferred(context)
    }
}
