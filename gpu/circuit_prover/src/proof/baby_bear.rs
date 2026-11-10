use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStreamWaitEventFlags;
use fft::GoodAllocator;
use gpu_core::primitives::context::UnsafeMutAccessor;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr::backward::{GKRBackwardStageSnapshotSink, GpuGKRBackwardScheduledExecution};
use gpu_gkr::forward::{schedule_forward_pass, ForwardOutputSlabTarget, GpuGKRTranscriptHandoff};
use gpu_gkr::setup::GpuGKRForwardSetupHostKeepalive;
use gpu_gkr::GkrPrograms;
use gpu_prover_context::ProverContext;
use std::sync::Arc;

use super::inputs::{GpuGKRProofTransfer, GpuGKRProofTransferKeepalive};
use super::memory_policy::{PartialTreePolicy, ProofMemoryPolicy};
use super::orchestration::stage1_forward::BundleDeviceRefs;
use super::orchestration::{
    prepare_backward_handoff, prepare_challenges_and_forward_setup, prepare_witness_and_commitment,
    schedule_backward_phase, schedule_terminal_proof_assembly, schedule_whir_phase,
    BackwardPhaseResult, ForwardChallengePreparation, ForwardToBackwardHandoff,
    GpuGKRProofJobKeepalive, Stage1WitnessPreparation, WhirPhaseResult,
};
use super::pipeline::{self, ProofPipeline, ProofWork};
use super::{ProofJob, ProofRequest};
use crate::upstream::{
    BaseColumns, BaseCommitmentGeometry, DefaultTreeConstructor, GKRProof, ProverConfig,
};

type BabyBearProof = GKRProof<BF, E4, DefaultTreeConstructor>;
pub type GpuGKRProofJob<'a> = ProofJob<'a, BabyBearProof, GpuGKRProofJobKeepalive<'a>>;

pub struct BabyBearProofRequest<'r, 'a, A: GoodAllocator> {
    programs: &'r Arc<GkrPrograms>,
    config: &'r ProverConfig,
    final_trace_log: u32,
    inputs: GpuGKRProofTransfer<'a, A>,
    memory_policy: ProofMemoryPolicy,
    partial_trees: PartialTreePolicy,
    stage_snapshots: Option<Box<GKRBackwardStageSnapshotSink>>,
}

impl<'r, 'a, A: GoodAllocator + 'a> BabyBearProofRequest<'r, 'a, A> {
    pub fn new(
        programs: &'r Arc<GkrPrograms>,
        config: &'r ProverConfig,
        final_trace_log: u32,
        inputs: GpuGKRProofTransfer<'a, A>,
        memory_policy: ProofMemoryPolicy,
        partial_trees: PartialTreePolicy,
    ) -> Self {
        Self {
            programs,
            config,
            final_trace_log,
            inputs,
            memory_policy,
            partial_trees,
            stage_snapshots: None,
        }
    }
    fn bundle(&self) -> BundleDeviceRefs<'_, 'a, A> {
        BundleDeviceRefs {
            setup: self.inputs.setup.as_ref(),
            decoder: self.inputs.decoder.as_ref(),
            inits_and_teardowns: self.inputs.inits_and_teardowns.as_ref(),
            memory: &self.inputs.memory,
            top_bits_device: self.inputs.top_bits.as_ref(),
            external_challenges_device: &self.inputs.external_challenges.device,
        }
    }
}

impl<A: GoodAllocator> super::sealed::Sealed for BabyBearProofRequest<'_, '_, A> {}
impl<'a, A: GoodAllocator + 'a> ProofRequest for BabyBearProofRequest<'_, 'a, A> {
    type Job = GpuGKRProofJob<'a>;
    fn enqueue(self, context: &ProverContext) -> CudaResult<Self::Job> {
        pipeline::prove(self, context)
    }
    fn collect_stage_snapshots(mut self) -> Self {
        self.stage_snapshots = Some(Box::default());
        self
    }
}

pub(crate) struct Joined<'r, 'a, A: GoodAllocator> {
    request: BabyBearProofRequest<'r, 'a, A>,
    base_geometry: BaseCommitmentGeometry,
    work: ProofWork<'a, BabyBearProof>,
}
pub(crate) struct Committed<'r, 'a, A: GoodAllocator> {
    joined: Joined<'r, 'a, A>,
    witness: Stage1WitnessPreparation,
}
pub(crate) struct Challenged<'r, 'a, A: GoodAllocator> {
    committed: Committed<'r, 'a, A>,
    challenges: ForwardChallengePreparation,
}
pub(crate) struct Gkr<'r, 'a, A: GoodAllocator> {
    committed: Committed<'r, 'a, A>,
    backward: GpuGKRBackwardScheduledExecution,
    forward_setup: GpuGKRForwardSetupHostKeepalive,
    transcript: GpuGKRTranscriptHandoff<E4>,
}
pub(crate) struct Whir<'r, 'a, A: GoodAllocator> {
    gkr: Gkr<'r, 'a, A>,
    output: WhirPhaseResult,
}

impl<'r, 'a, A: GoodAllocator + 'a> ProofPipeline for BabyBearProofRequest<'r, 'a, A> {
    type Joined = Joined<'r, 'a, A>;
    type Committed = Committed<'r, 'a, A>;
    type Challenged = Challenged<'r, 'a, A>;
    type Gkr = Gkr<'r, 'a, A>;
    type Whir = Whir<'r, 'a, A>;
    type Job = GpuGKRProofJob<'a>;

    fn join(self, context: &ProverContext) -> CudaResult<Self::Joined> {
        assert_eq!(
            self.config.trace_len_log2,
            self.programs.compiled_circuit().trace_len.trailing_zeros() as usize,
            "proof config trace length differs from compiled circuit"
        );
        assert_eq!(
            self.final_trace_log as usize, self.config.sumcheck_explicit_output_size_log_2,
            "GKR final trace size differs from configured explicit output size"
        );
        assert!(
            (self.final_trace_log as usize) < self.config.trace_len_log2,
            "GPU forward transcript handoff requires at least one dimension-reduction layer"
        );
        let base_geometry = BaseCommitmentGeometry::from_config(
            self.config,
            BaseColumns::of(self.programs.compiled_circuit()),
        );
        assert_eq!(
            self.config.base_oracles_values_per_leaf().trailing_zeros() as usize,
            self.config.whir_schedule.base_folding_log2()
        );
        self.inputs.transfer.ensure_transferred(context)?;
        let work = ProofWork::new("gkr.proof", context)?;
        context.reset_used_mem_peak();
        Ok(Joined {
            request: self,
            base_geometry,
            work,
        })
    }

    fn witness_commit(
        joined: Self::Joined,
        context: &ProverContext,
    ) -> CudaResult<Self::Committed> {
        let r = &joined.request;
        let witness = prepare_witness_and_commitment::<A>(
            r.programs,
            r.config,
            joined.base_geometry,
            r.final_trace_log,
            &r.config.whir_schedule,
            r.bundle(),
            r.inputs.tracing_data.as_ref(),
            r.memory_policy.witness,
            r.partial_trees,
            context,
        )?;
        Ok(Committed { joined, witness })
    }

    fn challenges(
        committed: Self::Committed,
        context: &ProverContext,
    ) -> CudaResult<Self::Challenged> {
        let r = &committed.joined.request;
        let challenges = prepare_challenges_and_forward_setup(
            r.programs,
            r.config,
            r.bundle(),
            &committed.witness,
            context,
        )?;
        Ok(Challenged {
            committed,
            challenges,
        })
    }

    fn gkr(state: Self::Challenged, context: &ProverContext) -> CudaResult<Self::Gkr> {
        let Challenged {
            mut committed,
            challenges:
                ForwardChallengePreparation {
                    mut forward_setup,
                    d_seed,
                },
        } = state;
        let r = &mut committed.joined.request;
        let w = &mut committed.witness;
        // Preserve the old post-challenge last-use point for these device inputs.
        drop(r.inputs.tracing_data.take());
        drop(r.inputs.inits_and_teardowns.take());
        drop(r.inputs.decoder.take());
        if let Some((geometry, trees)) = r.inputs.memory.take_partial_trees() {
            w.stage1_output
                .memory_trace_holder
                .install_transferred_partial_trees(geometry, trees);
        }
        let output_evaluations_slab = unsafe {
            w.proof_layout
                .output_evaluations_device_mut(w.proof_slab.as_ptr() as *mut u8)
        }
        .map(|(ptr, len)| {
            assert_eq!(
                ptr,
                w.proof_slab.as_ptr() as *mut E4,
                "output_evaluations must be the proof slab prefix for direct forward writes"
            );
            ForwardOutputSlabTarget {
                backing: Arc::clone(&w.proof_slab),
                len,
            }
        });
        let forward_output = schedule_forward_pass(
            r.inputs.setup.as_ref().map(|s| &s.trace_holder),
            w.synthetic_setup_trace_holder.as_ref(),
            &mut w.stage1_output,
            &mut forward_setup,
            &r.inputs.external_challenges.value,
            &r.inputs.top_bits_host,
            r.final_trace_log,
            output_evaluations_slab,
            r.programs,
            r.memory_policy.gkr,
            context,
        )?;
        let ForwardToBackwardHandoff {
            post_forward_handoff_range,
            transcript_handoff,
            backward_state,
            forward_setup_keepalive,
            d_lookup_challenges_for_backward,
            d_seed,
            d_evaluation_point_and_batching,
            top_layer_claim_layout,
            initial_d_claims,
        } = prepare_backward_handoff(
            forward_output,
            forward_setup,
            d_seed,
            r.final_trace_log,
            context,
        )?;
        committed
            .joined
            .work
            .ranges
            .push(post_forward_handoff_range);
        let BackwardPhaseResult { backward_scheduled } = schedule_backward_phase(
            backward_state,
            r.inputs.top_bits_host.clone(),
            Arc::clone(r.programs),
            r.inputs.external_challenges.device.as_ptr(),
            d_seed,
            d_evaluation_point_and_batching,
            initial_d_claims,
            top_layer_claim_layout,
            d_lookup_challenges_for_backward,
            &w.proof_slab,
            &w.proof_layout,
            r.stage_snapshots.as_deref_mut().map(UnsafeMutAccessor::new),
            &mut committed.joined.work.callbacks,
            context,
        )?;
        Ok(Gkr {
            committed,
            backward: backward_scheduled,
            forward_setup: forward_setup_keepalive,
            transcript: transcript_handoff,
        })
    }

    fn whir(mut gkr: Self::Gkr, context: &ProverContext) -> CudaResult<Self::Whir> {
        let r = &mut gkr.committed.joined.request;
        let w = &mut gkr.committed.witness;
        let base_geometry = gkr.committed.joined.base_geometry;
        let batching_pow_bits = r.config.base_round().batching_pow_bits::<BF, E4>(
            r.config.security_level.security_bits(),
            base_geometry.message_size_log2(),
            base_geometry.total_physical_columns(),
        );
        let output = schedule_whir_phase(
            r.programs.compiled_circuit().as_ref(),
            base_geometry,
            &r.config.whir_schedule,
            &mut r.inputs.setup,
            &mut w.synthetic_setup_trace_holder,
            &mut w.stage1_output,
            &mut gkr.backward,
            &w.proof_slab,
            &w.proof_layout,
            batching_pow_bits,
            r.memory_policy,
            context,
        )?;
        Ok(Whir { gkr, output })
    }

    fn readback(state: Self::Whir, context: &ProverContext) -> CudaResult<Self::Job> {
        let Whir {
            gkr:
                Gkr {
                    committed:
                        Committed {
                            joined:
                                Joined {
                                    request,
                                    base_geometry: _,
                                    mut work,
                                },
                            mut witness,
                        },
                    mut backward,
                    forward_setup,
                    transcript,
                },
            output:
                WhirPhaseResult {
                    mut base_layer_claims_scheduled,
                    base_layer_claims_shared_state,
                    whir_scheduled,
                },
        } = state;
        let BabyBearProofRequest {
            programs: _,
            config,
            final_trace_log: _,
            inputs,
            memory_policy: _,
            partial_trees: _,
            stage_snapshots,
        } = request;
        let GpuGKRProofTransfer {
            transfer,
            setup,
            decoder,
            inits_and_teardowns,
            tracing_data,
            memory,
            top_bits,
            top_bits_host,
            external_challenges,
        } = inputs;
        debug_assert!(decoder.is_none() && inits_and_teardowns.is_none() && tracing_data.is_none());
        let proof_handle = UnsafeMutAccessor::new(work.result.as_mut());
        let proof_host_mirror = Some(schedule_terminal_proof_assembly(
            &witness.proof_slab,
            &witness.proof_layout,
            proof_handle,
            config.whir_schedule.clone(),
            base_layer_claims_shared_state,
            external_challenges.value,
            top_bits_host.clone(),
            &mut work.callbacks,
            context,
        )?);
        drop(transcript);
        let stream = context.get_exec_stream();
        {
            let event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
            event.record(stream)?;
            context
                .get_h2d_stream()
                .wait_event(&event, CudaStreamWaitEventFlags::DEFAULT)?;
        }
        work.proof_range.end(stream)?;
        work.ranges.push(work.proof_range);
        drop(witness.synthetic_setup_trace_holder.take());
        backward.release_device_buffers();
        base_layer_claims_scheduled.release_device_buffers();
        drop(witness.proof_slab);
        let is_finished_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
        is_finished_event.record(stream)?;
        let inputs_keepalive = GpuGKRProofTransferKeepalive {
            _setup_host: setup.as_ref().map(|s| Arc::clone(&s.host)),
            _transfer: transfer.into_keepalive(),
        };
        let job = ProofJob {
            is_finished_event,
            callbacks: work.callbacks,
            result: work.result,
            ranges: work.ranges,
            stage_snapshots,
            keepalive: GpuGKRProofJobKeepalive {
                _stage1: witness.stage1_output.into_keepalive(),
                _inputs: inputs_keepalive,
                _forward_setup: forward_setup,
                _backward: backward,
                _base_layer_claims: base_layer_claims_scheduled,
                _whir: whir_scheduled,
                _proof_host_mirror: proof_host_mirror,
            },
        };
        // The original input bindings retired in reverse declaration order after
        // the completion record. Keep that order across consuming phase states.
        drop(external_challenges);
        drop(top_bits);
        drop(memory);
        drop(setup);
        Ok(job)
    }
}
