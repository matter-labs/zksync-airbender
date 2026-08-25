use crate::proof::{
    admit_dr_tail_before_transfers, construct_after_windowed_backward_preflight,
    preflight_windowed_backward, prove, resolve_backward_execution_strategy,
    DrTailPreflightRequest, GpuGKRProofJob, GpuProveError, GpuProveResult,
};
#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
use crate::proof::{
    schedule_main_acceptance_proof, MainAcceptanceOperation, MainAcceptanceScheduledJob,
};
#[cfg(not(feature = "task8_continuation_differential_test"))]
use crate::test_utils::make_test_context_with_device_allocator_block_log_size;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use fft::{materialize_powers_serial_starting_with_elem, Twiddles};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::nvtx::scoped_range;
use gpu_core::primitives::static_host::alloc_static_pinned_box_from_slice;
use gpu_gkr::{
    setup::{GpuGKRSetupHost, GpuGKRSetupTransfer},
    BackwardExecutionStrategy, DrTailProofPlan, GkrBackwardOptions, GkrPrograms, WindowTailArm,
};
use gpu_prover_context::ProverContext;
#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
use gpu_prover_context::{
    DeviceMemoryHighWaterObserver, PoolMemoryHighWaterReport, PoolMemoryHighWaterSnapshot,
    PoolMemoryUsage,
};
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::memory::commit_memory;
use gpu_trace::trace::tracing_data::{
    DelegationTracingDataDevice, InitsAndTeardownsTransfer, TracingDataDevice, TracingDataHost,
    TracingDataTransfer, UnrolledTracingDataDevice, UnrolledTracingDataHost,
};
use gpu_trace::witness::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use gpu_trace::witness::trace::ChunkedTraceHolder;
use gpu_trace::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, InitsAndTeardownsTraceHost, UnrolledMemoryTraceDevice,
    UnrolledNonMemoryTraceDevice, PAGE_SIZE_LOG2,
};

use itertools::Itertools;

use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, Instruction};
use riscv_transpiler::ir::DecodingOptions;
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{
    Counters, DelegationsAndFamiliesCounters, DelegationsAndUnifiedCounters, RamWithRomRegion,
    ReplayBuffer, SimpleSnapshotter, SimpleTape, State, VM,
};
use riscv_transpiler::witness::data_structs::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use riscv_transpiler::witness::{
    BigintDelegationDestinationHolder, BlakeDelegationDestinationHolder,
    KeccakDelegationDestinationHolder, MemDestinationHolder, MemoryOpcodeTracingDataWithTimestamp,
    NonMemDestinationHolder, NonMemoryOpcodeTracingDataWithTimestamp, UnifiedDestinationHolder,
};
use std::alloc::Global;
#[cfg(feature = "task8_continuation_differential_test")]
use std::cell::RefCell;
use std::path::PathBuf;
use std::sync::Arc;
use worker::Worker;

#[cfg(feature = "task8_continuation_differential_test")]
#[derive(Clone, Copy, Debug)]
struct Task8ConfiguredContext {
    config: gpu_prover_context::ProverContextConfig,
}

#[cfg(feature = "task8_continuation_differential_test")]
thread_local! {
    static TASK8_CONFIGURED_CONTEXT: RefCell<Option<Task8ConfiguredContext>> = const {
        RefCell::new(None)
    };
}

#[cfg(feature = "task8_continuation_differential_test")]
fn make_test_context_with_device_allocator_block_log_size(
    max_device_allocation_blocks_count: usize,
    host_pool_size_mb: usize,
    device_allocator_block_log_size: u32,
) -> ProverContext {
    let mut config = gpu_prover_context::ProverContextConfig {
        allocator_block_log_size: device_allocator_block_log_size,
        max_device_allocation_blocks_count: Some(max_device_allocation_blocks_count),
        ..Default::default()
    };
    let host_block_size = 1usize << config.host_allocator_block_log_size;
    config.host_allocator_blocks_count = (host_pool_size_mb * 1024 * 1024) / host_block_size;
    if config
        .small_allocator_log_chunk_size
        .is_some_and(|log_chunk_size| log_chunk_size >= device_allocator_block_log_size)
    {
        config.small_allocator_log_chunk_size = None;
    }
    TASK8_CONFIGURED_CONTEXT.with(|slot| {
        slot.replace(Some(Task8ConfiguredContext { config }));
    });
    ProverContext::new(&config).unwrap()
}

#[cfg(feature = "task8_continuation_differential_test")]
fn take_task8_configured_context() -> Task8ConfiguredContext {
    TASK8_CONFIGURED_CONTEXT.with(|slot| {
        slot.borrow_mut()
            .take()
            .expect("Task 8 fixture constructor did not record its exact ProverContextConfig")
    })
}

const BASIC_UNROLLED_CPU_PARITY_BINARY_PATH: &str =
    "riscv_transpiler/examples/keccak_f1600/app.bin";
const BASIC_UNROLLED_CPU_PARITY_TEXT_PATH: &str = "riscv_transpiler/examples/keccak_f1600/app.text";
const BASIC_UNROLLED_ADD_SUB_LAYOUT_PATH: &str =
    "cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json";
const JUMP_BRANCH_SLT_LAYOUT_PATH: &str = "cs/compiled_circuits/jump_branch_slt_layout_gkr.json";
const SHIFT_BINOP_LAYOUT_PATH: &str = "cs/compiled_circuits/shift_binop_layout_gkr.json";
const UNSIGNED_MUL_DIV_LAYOUT_PATH: &str = "cs/compiled_circuits/unsigned_mul_div_layout_gkr.json";
const MEM_WORD_ONLY_LAYOUT_PATH: &str = "cs/compiled_circuits/mem_word_only_layout_gkr.json";
const MEM_SUBWORD_ONLY_LAYOUT_PATH: &str = "cs/compiled_circuits/mem_subword_only_layout_gkr.json";

mod asserts;
mod commit_memory;
mod cpu_lde_labeling;
mod fixtures;
mod inits_and_teardowns;
mod lsb_commit_pipeline;
mod proof_matrix;
mod stagewise;

use asserts::*;

use crate::upstream::*;
use fixtures::*;

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

fn read_test_words(relative_path: &str) -> Vec<u32> {
    let bytes = std::fs::read(test_artifact_path(relative_path)).unwrap();
    assert_eq!(bytes.len() % 4, 0);
    bytes
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect()
}

fn deserialize_json_for_test<T: serde::de::DeserializeOwned>(relative_path: &str) -> T {
    let src = std::fs::File::open(test_artifact_path(relative_path)).unwrap();
    serde_json::from_reader(src).unwrap()
}

fn ensure_memory_trace_consistency<F: PrimeField>(
    memory_trace: &GKRMemoryOnlyWitnessTrace<
        F,
        impl std::alloc::Allocator + Clone,
        impl std::alloc::Allocator + Clone,
    >,
    witness_trace: &GKRFullWitnessTrace<
        F,
        impl std::alloc::Allocator + Clone,
        impl std::alloc::Allocator + Clone,
    >,
) {
    assert_eq!(
        memory_trace.column_major_trace.len(),
        witness_trace.column_major_memory_trace.len()
    );
    for (col, from_mem) in memory_trace.column_major_trace.iter().enumerate() {
        let from_wit = &witness_trace.column_major_memory_trace[col];
        assert_eq!(from_mem.len(), from_wit.len());
        for (row, (a, b)) in from_mem.iter().zip(from_wit.iter()).enumerate() {
            assert_eq!(*a, *b, "diverged for column {}, row {}", col, row);
        }
    }
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
    pub(crate) tracing_data_host: TracingDataHost<Global>,
    pub(crate) memory_tree_caps: Vec<MerkleTreeCapVarLength>,
    /// Sparse RAM init/teardown trace host. `None` for per-family fixtures
    /// (their memory is fully covered by the per-row shuffle); `Some` for the
    /// unified fixture, which proves the inits-and-teardowns layer.
    pub(crate) inits_and_teardowns_host: Option<InitsAndTeardownsTraceHost>,
    /// Actual global RAM-set top bits assigned to the fixture's local teardown
    /// slots. `None` uses the canonical contiguous selection for fixtures that
    /// do not need noncontiguous RAM-set rebasing.
    pub(crate) inits_and_teardowns_top_bits: Option<Vec<u32>>,
    /// Closure-assembly metadata captured from the same VM run, consumed by the
    /// unified e2e test to drive the no-filter grand-product
    /// accumulator to ONE. Empty/`None`/default for per-family fixtures.
    pub(crate) unified_register_final_state: [(u32, (u32, u32)); 32],
    pub(crate) unified_final_pc: u32,
    pub(crate) unified_final_timestamp: common_constants::TimestampScalar,
    pub(crate) delegation_grand_product_factors: Vec<E4>,
}

type BasicUnrolledTransfers<'a> = crate::proof::inputs::GpuGKRProofTransfer<'a, Global>;

#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
struct Task8ExactMemoryJob<'context> {
    job: MainAcceptanceScheduledJob<'static, 'context, Global>,
    whole: DeviceMemoryHighWaterObserver<'context>,
    stable_entry: PoolMemoryUsage,
}

#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
struct Task8ExactMemoryOutput {
    proof: GKRProof<BF, E4, DefaultTreeConstructor>,
    proof_time_ms: f32,
    backward: PoolMemoryHighWaterReport,
    backward_peak_window: PoolMemoryHighWaterSnapshot,
    whole: PoolMemoryHighWaterReport,
    whole_peak_window: PoolMemoryHighWaterSnapshot,
    operations: Vec<MainAcceptanceOperation>,
}

#[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
impl Task8ExactMemoryJob<'_> {
    fn finish(self) -> CudaResult<Task8ExactMemoryOutput> {
        let Task8ExactMemoryJob {
            job,
            whole,
            stable_entry,
        } = self;
        let mut finished = job.finish()?;
        let mut whole = whole;
        let whole_peak_window = whole.seal();
        let whole = whole.finish();
        finished
            .operations
            .push(MainAcceptanceOperation::WholeObserverFinished);
        assert_eq!(
            whole.start, stable_entry,
            "Task 8 whole observer did not start at the stable proof entry"
        );
        assert_eq!(
            whole.return_to_entry, whole.start,
            "Task 8 whole observer did not return to the stable proof entry"
        );
        assert_eq!(
            finished.backward.return_to_entry, whole.return_to_entry,
            "Task 8 backward observer return did not match the whole-proof return"
        );
        Ok(Task8ExactMemoryOutput {
            proof: finished.proof,
            proof_time_ms: finished.proof_time_ms,
            backward: finished.backward,
            backward_peak_window: finished.backward_peak_window,
            whole,
            whole_peak_window,
            operations: finished.operations,
        })
    }
}

pub(crate) struct BasicUnrolledProofFixture {
    pub(crate) base: BasicUnrolledFixture,
    pub(crate) expected_cpu_proof: GKRProof<BF, E4, DefaultTreeConstructor>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Task7DrTailArm {
    CompleteNewChain,
    LegacyDiagnostic,
}

impl Task7DrTailArm {
    pub(super) const fn backward_options(self) -> GkrBackwardOptions {
        let dr_production = matches!(self, Self::CompleteNewChain);
        GkrBackwardOptions {
            dr_tail_megakernel: dr_production,
            windowed_r0: true,
            windowed_main_continuations: true,
            windowed_dr: dr_production,
            windowed_dr_continuations: dr_production,
            window_tail: WindowTailArm::Split,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Task7MegakernelCoordinate {
    pub(super) layer_idx: usize,
    pub(super) folding_steps: usize,
    pub(super) entry_round: usize,
    pub(super) canonical_source_count: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Task7ProofOperation {
    ResourcePreflight,
    InitialInputH2d,
    ProveEnqueue,
    FinalSlabD2h,
    ProofAssemblyAfterFinalD2h,
}

const TASK7_EXPECTED_OPERATION_TRACE: [Task7ProofOperation; 5] = [
    Task7ProofOperation::ResourcePreflight,
    Task7ProofOperation::InitialInputH2d,
    Task7ProofOperation::ProveEnqueue,
    Task7ProofOperation::FinalSlabD2h,
    Task7ProofOperation::ProofAssemblyAfterFinalD2h,
];

fn record_task7_operation(trace: &mut Vec<Task7ProofOperation>, operation: Task7ProofOperation) {
    assert_eq!(
        TASK7_EXPECTED_OPERATION_TRACE.get(trace.len()),
        Some(&operation),
        "Task 7 proof operations must preserve the accepted stream order"
    );
    trace.push(operation);
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Task7ExecutionEvidence {
    pub(super) arm: Task7DrTailArm,
    pub(super) strategy: BackwardExecutionStrategy,
    pub(super) megakernel_coordinates: Vec<Task7MegakernelCoordinate>,
    pub(super) operation_trace: Vec<Task7ProofOperation>,
}

impl Task7ExecutionEvidence {
    pub(super) fn assert_complete(&self) {
        assert_eq!(self.strategy, BackwardExecutionStrategy::WindowedR0);
        assert_eq!(self.operation_trace, TASK7_EXPECTED_OPERATION_TRACE);
        match self.arm {
            Task7DrTailArm::CompleteNewChain => {
                assert!(
                    !self.megakernel_coordinates.is_empty(),
                    "production must dispatch at least one admitted DR-tail megakernel"
                );
            }
            Task7DrTailArm::LegacyDiagnostic => assert!(
                self.megakernel_coordinates.is_empty(),
                "the forced whole-layer legacy diagnostic must not dispatch the DR-tail megakernel"
            ),
        }
    }
}

pub(super) struct Task7ProofJob<'context> {
    job: GpuGKRProofJob<'static, 'context, Global>,
    evidence: Task7ExecutionEvidence,
}

impl<'context> Task7ProofJob<'context> {
    pub(super) fn finish(
        mut self,
    ) -> GpuProveResult<(
        GKRProof<BF, E4, DefaultTreeConstructor>,
        f32,
        Task7ExecutionEvidence,
    )> {
        let (proof, proof_time_ms) = self.job.finish()?;
        record_task7_operation(
            &mut self.evidence.operation_trace,
            Task7ProofOperation::ProofAssemblyAfterFinalD2h,
        );
        Ok((proof, proof_time_ms, self.evidence))
    }
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
            .map(|host| GpuGKRSetupTransfer::new(Arc::clone(host), context))
            .transpose()?;
        let decoder_transfer = if self.compiled_circuit.has_decoder_lookup {
            Some(DecoderTableTransfer::new(
                Arc::clone(&self.decoder_table_host),
                context,
            )?)
        } else {
            None
        };
        let tracing_data_transfer = Some(TracingDataTransfer::new(
            self.tracing_data_host.clone(),
            context,
        )?);
        // Memory-cap geometry comes from the setup host when present; the
        // standalone i/t circuit has no setup host, so fall back to the
        // equivalent values carried by the WHIR schedule.
        let (mem_log_lde_factor, mem_log_tree_cap_size) = match self.gpu_setup_host.as_ref() {
            Some(host) => (host.log_lde_factor, host.log_tree_cap_size),
            None => (
                self.prover_config
                    .whir_schedule
                    .base_lde_factor
                    .trailing_zeros(),
                self.prover_config.whir_schedule.cap_size.trailing_zeros(),
            ),
        };
        let memory_transfer_host = Arc::new(
            gpu_trace::trace::memory_transfer::GpuGKRMemoryTransferHost::from_per_coset_caps(
                &self.memory_tree_caps,
                mem_log_lde_factor,
                mem_log_tree_cap_size,
            )?,
        );
        let memory_transfer = gpu_trace::trace::memory_transfer::GpuGKRMemoryTransfer::new(
            memory_transfer_host,
            context,
        )?;

        let inits_and_teardowns_transfer = self
            .inits_and_teardowns_host
            .clone()
            .map(|host| InitsAndTeardownsTransfer::new(host, context))
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

    fn prove<'context>(
        &'context self,
        transfers: BasicUnrolledTransfers<'static>,
    ) -> GpuProveResult<GpuGKRProofJob<'static, 'context, Global>> {
        self.prove_with(transfers, GkrBackwardOptions::default())
    }

    /// Preflights the requested arm, then proves. Every fixture path goes
    /// through here so a windowed run reaches `prove()` the way production
    /// callers do.
    fn prove_with<'context>(
        &'context self,
        transfers: BasicUnrolledTransfers<'static>,
        backward_options: GkrBackwardOptions,
    ) -> GpuProveResult<GpuGKRProofJob<'static, 'context, Global>> {
        let strategy = resolve_backward_execution_strategy(
            &self.gkr_programs,
            &self.prover_config,
            backward_options,
        );
        preflight_windowed_backward(
            &self.gkr_programs,
            strategy,
            backward_options,
            self.final_trace_size_log_2,
        )
        .unwrap();
        prove::<Global>(
            &self.gkr_programs,
            &self.prover_config,
            self.final_trace_size_log_2,
            transfers,
            backward_options,
            None,
            &self.context,
        )
    }

    fn schedule_prove<'context>(
        &'context self,
    ) -> GpuProveResult<GpuGKRProofJob<'static, 'context, Global>> {
        self.schedule_prove_with(GkrBackwardOptions::default())
    }

    fn schedule_prove_with<'context>(
        &'context self,
        backward_options: GkrBackwardOptions,
    ) -> GpuProveResult<GpuGKRProofJob<'static, 'context, Global>> {
        self.schedule_prove_with_prepared(backward_options, None, None)
    }

    fn schedule_prove_with_prepared<'context>(
        &'context self,
        backward_options: GkrBackwardOptions,
        prepared: Option<(BasicUnrolledTransfers<'static>, Option<DrTailProofPlan>)>,
        mut task7_trace: Option<&mut Vec<Task7ProofOperation>>,
    ) -> GpuProveResult<GpuGKRProofJob<'static, 'context, Global>> {
        let (mut transfers, dr_tail_plan) = match prepared {
            Some(prepared) => prepared,
            None => {
                let strategy = resolve_backward_execution_strategy(
                    &self.gkr_programs,
                    &self.prover_config,
                    backward_options,
                );
                let transfers = construct_after_windowed_backward_preflight(
                    &self.gkr_programs,
                    strategy,
                    backward_options,
                    self.final_trace_size_log_2,
                    || self.create_transfers(),
                )
                .unwrap()?;
                (transfers, None)
            }
        };
        let h2d_stream = self.context.get_h2d_stream();
        let transfer_range = Range::new("gkr.proof.h2d_transfers")?;
        transfer_range.start(h2d_stream)?;
        transfers.schedule(&self.context)?;
        transfer_range.end(h2d_stream)?;
        if let Some(trace) = task7_trace.as_deref_mut() {
            record_task7_operation(trace, Task7ProofOperation::InitialInputH2d);
        }

        // Invariant: prove() is balanced — it releases every device allocation
        // it makes (stream-ordered) before returning, so used device memory
        // right after prove() returns equals used device memory right before
        // it was called. The transfers above are allocated before this point
        // and ride on in the job's keepalive, so they appear on both sides.
        let mem_before_prove = self.context.get_used_mem_current();
        let strategy = resolve_backward_execution_strategy(
            &self.gkr_programs,
            &self.prover_config,
            backward_options,
        );
        preflight_windowed_backward(
            &self.gkr_programs,
            strategy,
            backward_options,
            self.final_trace_size_log_2,
        )
        .unwrap();
        if let Some(trace) = task7_trace.as_deref_mut() {
            record_task7_operation(trace, Task7ProofOperation::ProveEnqueue);
        }
        let mut proof_job = prove::<Global>(
            &self.gkr_programs,
            &self.prover_config,
            self.final_trace_size_log_2,
            transfers,
            backward_options,
            dr_tail_plan,
            &self.context,
        )?;
        if let Some(trace) = task7_trace.as_deref_mut() {
            // `prove()` schedules the unique terminal D2H before returning;
            // successful `finish()` below proves its assembly callback ran.
            record_task7_operation(trace, Task7ProofOperation::FinalSlabD2h);
        }
        let mem_after_prove = self.context.get_used_mem_current();
        assert_eq!(
            mem_after_prove,
            mem_before_prove,
            "prove() must release every device allocation it makes: \
             before={mem_before_prove} after={mem_after_prove} \
             net_retained={}",
            mem_after_prove as i64 - mem_before_prove as i64,
        );
        proof_job.ranges.insert(0, transfer_range);
        Ok(proof_job)
    }

    /// Production-shaped Task 7 scheduling: admit the exact DR-tail plan
    /// before constructing the one existing input transfer, then pass that
    /// owned plan into the unchanged `prove()` call graph.
    fn schedule_task7_prove<'context>(
        &'context self,
        arm: Task7DrTailArm,
    ) -> GpuProveResult<Task7ProofJob<'context>> {
        let backward_options = arm.backward_options();
        let strategy = resolve_backward_execution_strategy(
            &self.gkr_programs,
            &self.prover_config,
            backward_options,
        );
        assert_eq!(
            strategy,
            BackwardExecutionStrategy::WindowedR0,
            "Task 7 fixtures must execute the complete windowed main-layer chain"
        );
        let request = DrTailPreflightRequest {
            gkr_programs: &self.gkr_programs,
            strategy,
            options: backward_options,
            final_trace_size_log_2: self.final_trace_size_log_2,
            device_id: era_cudart::device::get_device()?,
            entry: gpu_gkr::DrTailEntrySelection::Portable,
        };
        let mut operation_trace = Vec::with_capacity(TASK7_EXPECTED_OPERATION_TRACE.len());
        let admitted = admit_dr_tail_before_transfers(Some(request), |dr_tail_plan| {
            record_task7_operation(&mut operation_trace, Task7ProofOperation::ResourcePreflight);
            let coordinates = dr_tail_plan
                .as_ref()
                .map(DrTailProofPlan::layers)
                .unwrap_or_default()
                .iter()
                .map(|layer| Task7MegakernelCoordinate {
                    layer_idx: layer.layer_idx(),
                    folding_steps: layer.folding_steps(),
                    entry_round: layer.capacity().entry_round(),
                    canonical_source_count: layer.canonical_source_count(),
                })
                .collect::<Vec<_>>();
            self.create_transfers()
                .map(|transfers| (transfers, dr_tail_plan, coordinates))
        })
        .expect("Task 7 resource preflight must accept before any transfer construction")?;
        let (transfers, dr_tail_plan, megakernel_coordinates) = admitted;
        assert_eq!(
            dr_tail_plan.is_some(),
            matches!(arm, Task7DrTailArm::CompleteNewChain),
            "the selected Task 7 arm and admitted plan must agree"
        );

        let proof_job = self.schedule_prove_with_prepared(
            backward_options,
            Some((transfers, dr_tail_plan)),
            Some(&mut operation_trace),
        )?;
        Ok(Task7ProofJob {
            job: proof_job,
            evidence: Task7ExecutionEvidence {
                arm,
                strategy,
                megakernel_coordinates,
                // This records the production-shaped call graph. It contains
                // exactly the pre-existing initial H2D and proof terminal
                // D2H/callback; Task 7 adds no transfer or callback site.
                operation_trace,
            },
        })
    }

    #[cfg(all(feature = "task8_continuation_differential_test", not(no_cuda)))]
    fn schedule_exact_memory(
        &self,
        options: GkrBackwardOptions,
    ) -> Result<Task8ExactMemoryJob<'_>, GpuProveError> {
        let stable_entry = self.context.get_device_memory_usage();
        let whole = self.context.observe_device_memory_high_water();
        assert_eq!(self.context.get_device_memory_usage(), stable_entry);
        let strategy =
            resolve_backward_execution_strategy(&self.gkr_programs, &self.prover_config, options);
        let mut transfers = construct_after_windowed_backward_preflight(
            &self.gkr_programs,
            strategy,
            options,
            self.final_trace_size_log_2,
            || self.create_transfers(),
        )
        .unwrap()?;
        transfers.schedule(&self.context)?;
        let job = schedule_main_acceptance_proof(
            &self.gkr_programs,
            &self.prover_config,
            self.final_trace_size_log_2,
            transfers,
            options,
            &self.context,
        )?;
        Ok(Task8ExactMemoryJob {
            job,
            whole,
            stable_entry,
        })
    }
}

impl BasicUnrolledProofFixture {
    fn schedule_prove<'context>(
        &'context self,
    ) -> GpuProveResult<GpuGKRProofJob<'static, 'context, Global>> {
        self.base.schedule_prove()
    }

    fn schedule_prove_with<'context>(
        &'context self,
        backward_options: GkrBackwardOptions,
    ) -> GpuProveResult<GpuGKRProofJob<'static, 'context, Global>> {
        self.base.schedule_prove_with(backward_options)
    }

    fn schedule_task7_prove<'context>(
        &'context self,
        arm: Task7DrTailArm,
    ) -> GpuProveResult<Task7ProofJob<'context>> {
        self.base.schedule_task7_prove(arm)
    }
}

// Every field is a shared reference or a small Copy value, so this is
// trivially `Copy`.
#[derive(Clone, Copy)]
struct BasicUnrolledFixtureBuildConfig<'a> {
    binary_path: &'a str,
    text_path: &'a str,
    layout_path: &'a str,
    circuit_type: CircuitType,
    non_determinism_reads: &'a [u32],
    compute_cpu_reference: bool,
    device_allocator_block_log_size: u32,
    security_level: crate::upstream::SecurityLevel,
}

mod fixtures_helpers;
pub(super) use fixtures_helpers::*;

mod unified_fixtures_helpers;
pub(super) use unified_fixtures_helpers::*;
