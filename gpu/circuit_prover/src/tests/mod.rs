use crate::proof::memory_policy::{presets, ProofMemoryPolicy};
use crate::proof::{prove, GpuGKRProofJob};
use crate::test_utils::make_test_context_with_device_allocator_block_log_size;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use fft::Twiddles;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::nvtx::scoped_range;
use gpu_core::primitives::static_host::alloc_static_pinned_box_from_slice;
use gpu_gkr::{
    setup::{GpuGKRSetupHost, GpuGKRSetupTransfer},
    GkrPrograms,
};
use gpu_prover_context::ProverContext;
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::tracing_data::{
    InitsAndTeardownsTransfer, TracingDataHost, TracingDataTransfer, UnrolledTracingDataHost,
};
use gpu_trace::witness::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use gpu_trace::witness::trace::ChunkedTraceHolder;
use gpu_trace::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, InitsAndTeardownsTraceHost, PAGE_SIZE_LOG2,
};

use itertools::Itertools;

use riscv_transpiler::witness::data_structs::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
};
use std::alloc::Global;
use std::path::PathBuf;
use std::sync::Arc;
use worker::Worker;

mod asserts;
mod commit_memory;
mod fixtures;
mod geometry_proof;
mod inits_and_teardowns;
mod lsb_commit_pipeline;
mod memory_policies;
mod proof_matrix;
mod stagewise;

use asserts::*;

use crate::upstream::*;
use fixtures::*;
use prover::tests::gkr::orchestration::canonical_fixtures::CanonicalCircuit;

fn test_artifact_path(relative_path: &str) -> PathBuf {
    let root = std::env::var_os("AB_TEST_ARTIFACT_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("..")
        });
    root.join(relative_path)
}

fn upload_slice_to_device_for_test<T: Copy>(
    values: &[T],
    context: &ProverContext,
) -> DeviceAllocation<T> {
    let mut device = context
        .alloc(values.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut device, values, context.get_exec_stream()).unwrap();
    device
}

fn make_decoder_table_host_for_test(
    witness_gen_data: &[cs::gkr_circuits::ExecutorFamilyDecoderData],
) -> Arc<gpu_core::primitives::static_host::StaticPinnedBox<ExecutorFamilyDecoderData>> {
    let mut data: Vec<_> = witness_gen_data
        .iter()
        .copied()
        .map(ExecutorFamilyDecoderData::from)
        .collect();
    // Delegations carry no decoder lookup, so the delegation fixtures pass an
    // empty slice; the resulting host is never transferred (`create_transfers`
    // gates the decoder transfer on `compiled_circuit.has_decoder_lookup`). A
    // zero-length pinned allocation panics, so materialize one benign default
    // element for that unused path — this keeps harness SETUP from erroring so
    // that only the delegation `prove()` itself is the point that can fail.
    if data.is_empty() {
        data.push(ExecutorFamilyDecoderData::from(
            cs::gkr_circuits::ExecutorFamilyDecoderData::default(),
        ));
    }
    Arc::new(
        alloc_static_pinned_box_from_slice(&data)
            .expect("decoder table should fit in static pinned host memory"),
    )
}

fn make_non_memory_tracing_host_for_test(
    buffer: Vec<NonMemoryOpcodeTracingDataWithTimestamp>,
) -> TracingDataHost<Global> {
    TracingDataHost::Unrolled(UnrolledTracingDataHost::NonMemory(ChunkedTraceHolder {
        chunks: vec![Arc::new(buffer)],
    }))
}

fn make_unified_tracing_host_for_test(
    buffer: Vec<UnifiedOpcodeTracingDataWithTimestamp>,
) -> TracingDataHost<Global> {
    TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(ChunkedTraceHolder {
        chunks: vec![Arc::new(buffer)],
    }))
}

fn make_memory_tracing_host_for_test(
    buffer: Vec<MemoryOpcodeTracingDataWithTimestamp>,
) -> TracingDataHost<Global> {
    TracingDataHost::Unrolled(UnrolledTracingDataHost::Memory(ChunkedTraceHolder {
        chunks: vec![Arc::new(buffer)],
    }))
}

pub(crate) struct BasicUnrolledFixture {
    pub(crate) context: ProverContext,
    pub(crate) circuit_type: CircuitType,
    pub(crate) profile: ProofProfile,
    pub(crate) gkr_programs: Arc<GkrPrograms>,
    pub(crate) compiled_circuit: GKRCircuitArtifact<BF>,
    pub(crate) external_challenges: GKRExternalChallenges<BF, E4>,
    pub(crate) prover_config: ProverConfig,
    pub(crate) final_trace_size_log_2: u32,
    /// GPU setup (preprocessed) trace host. `None` for the standalone
    /// inits-and-teardowns circuit, which has a zero-width setup layout
    /// (`witness_layout.total_width == 0`) and is proven with `setup = None`
    /// (the forward pass uses a synthetic zero-width setup holder). All other
    /// circuits carry a real setup trace.
    pub(crate) gpu_setup_host: Option<Arc<GpuGKRSetupHost>>,
    pub(crate) decoder_table_host:
        Arc<gpu_core::primitives::static_host::StaticPinnedBox<ExecutorFamilyDecoderData>>,
    pub(crate) tracing_data_host: Option<TracingDataHost<Global>>,
    pub(crate) memory_tree_caps: Vec<MerkleTreeCapVarLength>,
    /// Sparse RAM init/teardown trace host. `None` for per-family fixtures
    /// (their memory is fully covered by the per-row shuffle); `Some` for the
    /// unified fixture, which proves the inits-and-teardowns layer.
    pub(crate) inits_and_teardowns_host: Option<InitsAndTeardownsTraceHost<std::alloc::Global>>,
    /// Actual global RAM-set top bits assigned to the fixture's local teardown
    /// slots. `None` uses the canonical contiguous selection for fixtures that
    /// do not need noncontiguous RAM-set rebasing.
    pub(crate) inits_and_teardowns_top_bits: Option<Vec<u32>>,
}

type BasicUnrolledTransfers<'a> = crate::proof::inputs::GpuGKRProofTransfer<'a, Global>;

pub(crate) struct BasicUnrolledProofFixture {
    pub(crate) base: BasicUnrolledFixture,
    pub(crate) committed_proof: GKRProof<BF, E4, DefaultTreeConstructor>,
    pub(crate) committed_proof_bytes: Vec<u8>,
}

impl BasicUnrolledFixture {
    fn create_transfers(&self) -> CudaResult<BasicUnrolledTransfers<'static>> {
        self.create_transfers_for_context(&self.context)
    }

    fn create_transfers_for_context(
        &self,
        context: &ProverContext,
    ) -> CudaResult<BasicUnrolledTransfers<'static>> {
        let setup_transfer = self
            .gpu_setup_host
            .as_ref()
            .map(|host| {
                GpuGKRSetupTransfer::new(Arc::clone(host), self.partial_trees().setup, context)
            })
            .transpose()?;
        let decoder_transfer = if self.compiled_circuit.has_decoder_lookup {
            Some(DecoderTableTransfer::new(
                Arc::clone(&self.decoder_table_host),
                context,
            )?)
        } else {
            None
        };
        let tracing_data_transfer = self
            .tracing_data_host
            .as_ref()
            .map(|host| {
                TracingDataTransfer::new(host.clone(), self.compiled_circuit.trace_len, context)
            })
            .transpose()?;
        let geometry = BaseCommitmentGeometry::from_config(
            &self.prover_config,
            BaseColumns::of(&self.compiled_circuit),
        );
        let memory_transfer_host = Arc::new(
            gpu_trace::trace::memory_cap::GpuGKRMemoryCapHost::from_per_coset_caps_for_geometry(
                &self.memory_tree_caps,
                geometry,
            ),
        );
        let memory_transfer = gpu_trace::trace::memory_cap::GpuGKRMemoryCapTransfer::new(
            memory_transfer_host,
            context,
        )?;

        let inits_and_teardowns_transfer = self
            .inits_and_teardowns_host
            .clone()
            .map(|host| {
                InitsAndTeardownsTransfer::new(
                    Some(host),
                    self.compiled_circuit.memory_layout.teardown_sets.len(),
                    self.compiled_circuit.trace_len,
                    context,
                )
            })
            .transpose()?;

        let top_bits = self
            .inits_and_teardowns_top_bits
            .clone()
            .unwrap_or_else(|| {
                (0..self.compiled_circuit.memory_layout.teardown_sets.len() as u32).collect()
            });
        BasicUnrolledTransfers::new(
            setup_transfer,
            decoder_transfer,
            inits_and_teardowns_transfer,
            tracing_data_transfer,
            memory_transfer,
            &top_bits,
            self.external_challenges,
            context,
        )
    }

    fn schedule_transfers(&self) -> CudaResult<BasicUnrolledTransfers<'static>> {
        let mut transfers = self.create_transfers()?;
        transfers.schedule(&self.context)?;
        Ok(transfers)
    }

    fn prove(
        &self,
        transfers: BasicUnrolledTransfers<'static>,
    ) -> CudaResult<GpuGKRProofJob<'static>> {
        prove(
            crate::proof::BabyBearProofRequest::new(
                &self.gkr_programs,
                &self.prover_config,
                self.final_trace_size_log_2,
                transfers,
                self.memory_policy(),
                self.partial_trees(),
            ),
            &self.context,
        )
    }

    fn memory_policy(&self) -> ProofMemoryPolicy {
        presets::policy(self.circuit_type, self.profile, self.context.get_mem_size())
    }

    fn partial_trees(&self) -> crate::proof::memory_policy::PartialTreePolicy {
        presets::partial_trees(self.circuit_type, self.profile)
    }

    fn schedule_prove(&self) -> CudaResult<GpuGKRProofJob<'static>> {
        self.schedule_prove_with_memory_policy(self.memory_policy())
    }

    fn schedule_prove_with_memory_policy(
        &self,
        policy: ProofMemoryPolicy,
    ) -> CudaResult<GpuGKRProofJob<'static>> {
        let mem_before_inputs = self.context.get_used_mem_current();
        let mut transfers = self.create_transfers()?;

        let h2d_stream = self.context.get_h2d_stream();
        let transfer_range = Range::new("gkr.proof.h2d_transfers")?;
        transfer_range.start(h2d_stream)?;
        transfers.schedule(&self.context)?;
        transfer_range.end(h2d_stream)?;

        let mut proof_job = crate::proof::prove(
            crate::proof::BabyBearProofRequest::new(
                &self.gkr_programs,
                &self.prover_config,
                self.final_trace_size_log_2,
                transfers,
                policy,
                self.partial_trees(),
            ),
            &self.context,
        )?;
        let mem_after_prove = self.context.get_used_mem_current();
        assert_eq!(mem_after_prove, mem_before_inputs,
            "prove() must retire all device reservations, including its input bundle, before finish()");
        proof_job.ranges.insert(0, transfer_range);
        Ok(proof_job)
    }
}

impl BasicUnrolledProofFixture {
    fn assert_proof(&self, proof: &GKRProof<BF, E4, DefaultTreeConstructor>) {
        assert_gkr_proof_structure_for_test(proof, &self.base.prover_config.whir_schedule);
        if self.base.circuit_type == CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) {
            assert_eq!(self.base.compiled_circuit.witness_layout.total_width, 0);
            assert_eq!(self.base.compiled_circuit.generic_lookup_tables_width, 0);
            assert!(self.base.gpu_setup_host.is_none());
            assert!(self.base.tracing_data_host.is_none());
        }
        assert_gkr_proof_eq_for_test(proof, &self.committed_proof);
        assert_eq!(
            proof_fixtures::encode(proof, Vec::new()),
            self.committed_proof_bytes,
            "GPU proof differs from committed file bytes",
        );
    }

    fn schedule_prove(&self) -> CudaResult<GpuGKRProofJob<'static>> {
        self.base.schedule_prove()
    }
}

fn record_test_resources(base: &BasicUnrolledFixture, preparation_peak: usize, checked: usize) {
    if let Some(path) = std::env::var_os("AB_GPU_TEST_RESOURCE_PATH") {
        let proof_peak = base.context.get_used_mem_peak();
        let data = serde_json::json!({
            "circuit_type": format!("{:?}", base.circuit_type),
            "proofs_checked": checked,
            "device_baseline_bytes": base.context.get_used_mem_current(),
            "preparation_device_peak_bytes": preparation_peak,
            "proof_device_peak_bytes": proof_peak,
            "device_peak_bytes": preparation_peak.max(proof_peak),
        });
        std::fs::write(path, serde_json::to_vec_pretty(&data).unwrap()).unwrap();
    }
}

mod fixtures_helpers;
use fixtures_helpers::*;
