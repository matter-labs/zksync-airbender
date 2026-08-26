//! Per-circuit symbolic programs used by the GPU GKR interpreters.
//!
//! Forward search is deliberately absent from this module. The searched
//! schedules are committed artifacts embedded in the binary; initialization
//! only lowers the circuit, rejects an artifact mismatch, and compiles the
//! forward, R0, and continuation programs once.

use gpu_core::primitives::field::BF;
use gpu_gkr_compiler::{
    compile_continuations, compile_forward, compile_r0, lower_dr_window_program,
    lower_main_continuation_window_program, lower_window_program, parse_forward_artifact,
    project_dr_window_inputs, ContinuationProgramBundle, DrWindowInputOutput,
    DrWindowInputProjection, DrWindowProgram, ForwardProgramBundle, MainContinuationWindowProgram,
    R0ProgramBundle, WindowFamily, WindowProgram,
};
use gpu_trace::witness::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex, OnceLock};

use crate::backward::{
    derive_dimension_reducing_inputs,
    main_tail::{lower_main_tail_program, MainTailProgram},
    window_dr,
};
use crate::storage_layout::GpuGKRStorageLayout;
use crate::transform::normalize_compiled_circuit_for_gpu;
use crate::upstream::{
    DimensionReducingInputOutput, GKRAddress, GKRCircuitArtifact, OutputType, VirtualSetupPoly,
};

#[derive(Clone)]
pub(crate) struct BackwardLayerPlan {
    pub(crate) inputs: Vec<GKRAddress>,
    pub(crate) claims: Vec<(usize, GKRAddress)>,
}

fn sink_address(sink: &gkr_eval_ir::SinkKind) -> Option<GKRAddress> {
    match *sink {
        gkr_eval_ir::SinkKind::Inner { layer, offset } => {
            Some(GKRAddress::InnerLayer { layer, offset })
        }
        gkr_eval_ir::SinkKind::Cache { layer, offset } => {
            Some(GKRAddress::Cached { layer, offset })
        }
        gkr_eval_ir::SinkKind::Scratch { slot } => Some(GKRAddress::ScratchSpace(slot)),
    }
}

fn bound_window_address(family: WindowFamily, column: usize) -> GKRAddress {
    match family {
        WindowFamily::BaseLayerMemory => GKRAddress::BaseLayerMemory(column),
        WindowFamily::BaseLayerWitness => GKRAddress::BaseLayerWitness(column),
        WindowFamily::Setup => GKRAddress::Setup(column),
        WindowFamily::Scratch => GKRAddress::ScratchSpace(column),
        WindowFamily::LayerOutput { layer, .. } => GKRAddress::InnerLayer {
            layer,
            offset: column,
        },
        WindowFamily::CacheOutput { layer, .. } => GKRAddress::Cached {
            layer,
            offset: column,
        },
        WindowFamily::VirtualSetup { kind } => GKRAddress::VirtualSetup(match kind {
            0 => VirtualSetupPoly::RangeCheck16Bits,
            1 => VirtualSetupPoly::RangeCheckTimestamp,
            2 => VirtualSetupPoly::InitsAndTeardownsLow,
            3 => VirtualSetupPoly::InitsAndTeardownsHigh,
            _ => panic!("unknown virtual setup kind {kind}"),
        }),
    }
}

pub(crate) fn backward_layer_plans(
    dag: &gkr_eval_ir::DagCircuit,
    continuations: &ContinuationProgramBundle,
) -> Vec<BackwardLayerPlan> {
    dag.layers
        .iter()
        .zip(&continuations.layers)
        .map(|(layer, continuation)| {
            let inputs = continuation
                .binding
                .windows
                .iter()
                .flat_map(|window| {
                    window
                        .columns
                        .iter()
                        .map(|column| bound_window_address(window.family, column.column))
                })
                .collect::<std::collections::BTreeSet<_>>()
                .into_iter()
                .collect();
            let claims = layer
                .batching
                .roots
                .iter()
                .enumerate()
                .filter_map(|(offset, root)| {
                    let root = &layer.roots[root.0 as usize];
                    root.claim.as_ref()?;
                    root.materialize.as_ref().map(|sink| {
                        (
                            offset,
                            sink_address(&sink.kind)
                                .expect("main-layer output must have an addressable sink"),
                        )
                    })
                })
                .collect();
            BackwardLayerPlan { inputs, claims }
        })
        .collect()
}

const ADD_SUB: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/add_sub_lui_auipc_mop_schedule_b4_gkr.json");
const BIGINT: &[u8] = include_bytes!(
    "../../../cs/compiled_circuits/bigint_with_extended_control_schedule_b4_gkr.json"
);
const BLAKE2_G: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/blake2_g_function_schedule_b4_gkr.json");
const BLAKE2_EXT: &[u8] = include_bytes!(
    "../../../cs/compiled_circuits/blake2_with_extended_control_schedule_b4_gkr.json"
);
const INITS: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/inits_and_teardowns_schedule_b4_gkr.json");
const JUMP: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/jump_branch_slt_schedule_b4_gkr.json");
const KECCAK: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/keccak_special5_schedule_b4_gkr.json");
const MEM_SUBWORD: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/mem_subword_only_schedule_b4_gkr.json");
const MEM_WORD: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/mem_word_only_schedule_b4_gkr.json");
const SHIFT: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/shift_binop_schedule_b4_gkr.json");
const UNIFIED: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/unified_reduced_machine_schedule_b4_gkr.json");
const UNSIGNED_MUL_DIV: &[u8] =
    include_bytes!("../../../cs/compiled_circuits/unsigned_mul_div_schedule_b4_gkr.json");

fn forward_artifact(circuit_type: CircuitType) -> (&'static [u8], &'static str) {
    match circuit_type {
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
        )) => (ADD_SUB, "add_sub_lui_auipc_mop"),
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::JumpBranchSlt,
        )) => (JUMP, "jump_branch_slt"),
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::MulDivUnsigned,
        )) => (UNSIGNED_MUL_DIV, "unsigned_mul_div"),
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::ShiftBinary,
        )) => (SHIFT, "shift_binop"),
        CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreWordOnly,
        )) => (MEM_WORD, "mem_word_only"),
        CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
        )) => (MEM_SUBWORD, "mem_subword_only"),
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
            (INITS, "inits_and_teardowns")
        }
        CircuitType::Unrolled(UnrolledCircuitType::Unified) => (UNIFIED, "unified_reduced_machine"),
        CircuitType::Delegation(DelegationCircuitType::BigIntWithControl) => {
            (BIGINT, "bigint_with_extended_control")
        }
        CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression) => {
            (BLAKE2_EXT, "blake2_with_extended_control")
        }
        CircuitType::Delegation(DelegationCircuitType::Blake2GFunction) => {
            (BLAKE2_G, "blake2_g_function")
        }
        CircuitType::Delegation(DelegationCircuitType::KeccakSpecial5) => {
            (KECCAK, "keccak_special5")
        }
    }
}

/// The window-3 lowering of every main layer's R0 program.
pub struct WindowProgramBundle {
    pub layers: Vec<WindowProgram>,
}

/// The canonical window-3 lowering of every main-layer continuation program.
#[derive(Debug)]
pub struct MainContinuationWindowProgramBundle {
    pub layers: Vec<MainContinuationWindowProgram>,
}

/// The dealt main-tail program for every main layer.
#[derive(Debug)]
pub struct MainTailProgramBundle {
    pub layers: Vec<MainTailProgram>,
}

/// A window lowering the circuit's shape does not support. Carries the origin
/// the apex crate reports: which circuit, which layer, which resource.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WindowLoweringRejection {
    pub circuit: String,
    pub layer: usize,
    pub resource: String,
}

impl core::fmt::Display for WindowLoweringRejection {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            formatter,
            "windowed R0 lowering rejected for {}/{}: {}",
            self.circuit, self.layer, self.resource
        )
    }
}

impl std::error::Error for WindowLoweringRejection {}

/// One dimension-reducing layer's window-3 R0 program and publication view.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DrWindowLayerProgram {
    layer: usize,
    folding_steps: usize,
    program: DrWindowProgram,
    input_projection: DrWindowInputProjection,
}

impl DrWindowLayerProgram {
    pub(crate) fn new(
        layer: usize,
        folding_steps: usize,
        program: DrWindowProgram,
        input_projection: DrWindowInputProjection,
    ) -> Self {
        Self {
            layer,
            folding_steps,
            program,
            input_projection,
        }
    }

    pub const fn layer(&self) -> usize {
        self.layer
    }

    pub const fn folding_steps(&self) -> usize {
        self.folding_steps
    }

    pub const fn program(&self) -> &DrWindowProgram {
        &self.program
    }

    pub const fn input_projection(&self) -> &DrWindowInputProjection {
        &self.input_projection
    }
}

/// Window-3 R0 programs for every dimension-reducing layer at one final log.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DrWindowProgramBundle {
    final_trace_log: u32,
    layers: BTreeMap<usize, DrWindowLayerProgram>,
}

impl DrWindowProgramBundle {
    pub(crate) fn new(final_trace_log: u32, layers: BTreeMap<usize, DrWindowLayerProgram>) -> Self {
        Self {
            final_trace_log,
            layers,
        }
    }

    pub const fn final_trace_log(&self) -> u32 {
        self.final_trace_log
    }

    pub fn layer(&self, dr_layer: usize) -> Option<&DrWindowLayerProgram> {
        self.layers.get(&dr_layer)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DrWindowLegacyRowSide {
    Input,
    Output,
}

impl DrWindowLegacyRowSide {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Input => "input",
            Self::Output => "output",
        }
    }
}

/// A dimension-reducing window lowering the circuit shape does not support.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DrWindowLoweringRejection {
    circuit: String,
    layer: usize,
    output_type: Option<OutputType>,
    expected_count: Option<usize>,
    actual_count: Option<usize>,
    legacy_row_side: Option<DrWindowLegacyRowSide>,
    resource: String,
}

impl DrWindowLoweringRejection {
    fn lowering(circuit: impl Into<String>, layer: usize, resource: impl Into<String>) -> Self {
        Self {
            circuit: circuit.into(),
            layer,
            output_type: None,
            expected_count: None,
            actual_count: None,
            legacy_row_side: None,
            resource: resource.into(),
        }
    }

    fn legacy_arity(
        circuit: impl Into<String>,
        layer: usize,
        output_type: OutputType,
        side: DrWindowLegacyRowSide,
        expected_count: usize,
        actual_count: usize,
    ) -> Self {
        let circuit = circuit.into();
        Self {
            resource: format!(
                "{output_type:?} {} arity: expected {expected_count}, got {actual_count}",
                side.as_str()
            ),
            circuit,
            layer,
            output_type: Some(output_type),
            expected_count: Some(expected_count),
            actual_count: Some(actual_count),
            legacy_row_side: Some(side),
        }
    }

    pub fn circuit(&self) -> &str {
        &self.circuit
    }

    pub const fn layer(&self) -> usize {
        self.layer
    }

    pub const fn output_type(&self) -> Option<OutputType> {
        self.output_type
    }

    pub const fn expected_count(&self) -> Option<usize> {
        self.expected_count
    }

    pub const fn actual_count(&self) -> Option<usize> {
        self.actual_count
    }

    pub const fn legacy_row_side(&self) -> Option<&'static str> {
        match self.legacy_row_side {
            Some(side) => Some(side.as_str()),
            None => None,
        }
    }

    pub fn resource(&self) -> &str {
        &self.resource
    }
}

impl core::fmt::Display for DrWindowLoweringRejection {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            formatter,
            "dimension-reducing windowed R0 lowering rejected for {}/{}: {}",
            self.circuit, self.layer, self.resource
        )
    }
}

impl std::error::Error for DrWindowLoweringRejection {}

/// A continuation lowering the circuit's shape does not support. Rejections
/// are cached with accepted bundles so repeated preflights are stable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MainContinuationWindowLoweringRejection {
    pub circuit: String,
    pub layer: usize,
    pub resource: String,
}

impl core::fmt::Display for MainContinuationWindowLoweringRejection {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            formatter,
            "main continuation window lowering rejected for {}/{}: {}",
            self.circuit, self.layer, self.resource
        )
    }
}

impl std::error::Error for MainContinuationWindowLoweringRejection {}

/// A main-tail lowering the circuit's shape does not support. Rejections are
/// cached alongside successful bundles, so an enabled arm can never fall back
/// after a later preflight.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MainTailLoweringRejection {
    pub circuit: String,
    pub layer: usize,
    pub resource: String,
}

impl core::fmt::Display for MainTailLoweringRejection {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            formatter,
            "main-tail lowering rejected for {}/{}: {}",
            self.circuit, self.layer, self.resource
        )
    }
}

impl std::error::Error for MainTailLoweringRejection {}

/// Symbolic programs compiled once with the circuit's other precomputations.
///
/// R0 and continuation remain separate compiler products and separate runtime
/// inputs; they intentionally share no policy object.
pub struct GkrPrograms {
    circuit_type: CircuitType,
    compiled_circuit: Arc<GKRCircuitArtifact<BF>>,
    runtime_circuit: Arc<GKRCircuitArtifact<BF>>,
    pub(crate) forward: ForwardProgramBundle,
    pub(crate) r0: R0ProgramBundle,
    pub(crate) continuations: ContinuationProgramBundle,
    pub(crate) backward_layers: Vec<BackwardLayerPlan>,
    /// Lowered on the first windowed proof request, never during compilation:
    /// `GkrPrograms` is built in circuit precomputations, which have no prover
    /// config to select an arm with.
    window: OnceLock<Result<WindowProgramBundle, WindowLoweringRejection>>,
    /// Dimension-reducing programs depend on proof geometry, so one circuit
    /// precomputation may hold accepted or rejected results for several final
    /// trace logs. Values are owned outside the lock through `Arc`.
    dr_window: Mutex<BTreeMap<u32, Result<Arc<DrWindowProgramBundle>, DrWindowLoweringRejection>>>,
    /// Lowered independently from R0 on the first proof whose per-layer plan
    /// selects at least one continuation window.
    main_continuation_window: OnceLock<
        Result<MainContinuationWindowProgramBundle, MainContinuationWindowLoweringRejection>,
    >,
    /// Lowered independently from the continuation-window program on the first
    /// proof that requests the main-tail arm. Success and typed failure are
    /// retained equally.
    main_tail: OnceLock<Result<MainTailProgramBundle, MainTailLoweringRejection>>,
}

impl GkrPrograms {
    pub fn compile(
        circuit_type: CircuitType,
        artifact: Arc<GKRCircuitArtifact<BF>>,
    ) -> Result<Self, String> {
        let runtime_circuit = Arc::new(normalize_compiled_circuit_for_gpu(
            artifact.as_ref().clone(),
        ));
        let dag = gkr_eval_ir::lower_dag(&artifact)?;
        let (bytes, expected_circuit) = forward_artifact(circuit_type);
        let searched = parse_forward_artifact(bytes, "embedded forward GKR schedule")
            .map_err(|error| error.to_string())?;
        if searched.circuit != expected_circuit {
            return Err(format!(
                "embedded forward GKR schedule is for {}, expected {expected_circuit}",
                searched.circuit
            ));
        }
        if searched.budget_buckets != 4 {
            return Err(format!(
                "embedded forward GKR schedule has E4 budget {}, expected 4",
                searched.budget_buckets
            ));
        }
        let forward = compile_forward(&dag, &searched)
            .map_err(|error| format!("forward GKR compile: {error:?}"))?;

        let r0 = compile_r0(&dag).map_err(|error| format!("R0 GKR compile: {error:?}"))?;
        let continuations = compile_continuations(&dag)
            .map_err(|error| format!("continuation GKR compile: {error:?}"))?;
        let backward_layers = backward_layer_plans(&dag, &continuations);

        Ok(Self {
            circuit_type,
            compiled_circuit: artifact,
            runtime_circuit,
            forward,
            r0,
            continuations,
            backward_layers,
            window: OnceLock::new(),
            dr_window: Mutex::new(BTreeMap::new()),
            main_continuation_window: OnceLock::new(),
            main_tail: OnceLock::new(),
        })
    }

    /// Returns `(layer_idx, incoming_claims, replacement_claims)` for every
    /// dimension-reducing layer in backward execution order. This is a
    /// host-only corpus oracle for allocation-lifetime regression tests.
    #[doc(hidden)]
    pub fn dimension_reducing_claim_count_census_for_test(
        &self,
        final_trace_log: u32,
    ) -> Vec<(usize, usize, usize)> {
        let initial_layer = self.runtime_circuit.layers.len();
        let initial_trace_log = self.runtime_circuit.trace_len.trailing_zeros();
        let layers = derive_dimension_reducing_inputs(
            initial_layer,
            &self.runtime_circuit.global_output_map,
            initial_trace_log,
            final_trace_log,
        );
        let mut incoming_addresses = layers
            .iter()
            .next_back()
            .expect("dimension-reducing claim census requires at least one layer")
            .1
            .values()
            .flat_map(|reduced| reduced.output.iter().copied())
            .collect::<std::collections::BTreeSet<_>>();
        let mut census = Vec::with_capacity(layers.len());
        for (layer_idx, layer) in layers.iter().rev() {
            let outputs = layer
                .values()
                .flat_map(|reduced| reduced.output.iter().copied())
                .collect::<std::collections::BTreeSet<_>>();
            assert_eq!(
                outputs, incoming_addresses,
                "layer {layer_idx} outputs must exactly identify device_claims_in",
            );
            let replacement_addresses = layer
                .values()
                .flat_map(|reduced| reduced.inputs.iter().copied())
                .collect::<std::collections::BTreeSet<_>>();
            census.push((
                *layer_idx,
                incoming_addresses.len(),
                replacement_addresses.len(),
            ));
            incoming_addresses = replacement_addresses;
        }
        census
    }

    /// Lower every layer's window program, once per `GkrPrograms`. A rejection
    /// is cached too: a circuit the sectioned lowering cannot express must fail
    /// the same way on every later request, never fall back silently.
    pub fn resolve_window_programs(
        &self,
    ) -> Result<&WindowProgramBundle, &WindowLoweringRejection> {
        self.window
            .get_or_init(|| {
                let circuit = forward_artifact(self.circuit_type).1;
                let mut layers = Vec::with_capacity(self.r0.layers.len());
                for layer in &self.r0.layers {
                    match lower_window_program(layer) {
                        Ok(program) => layers.push(program),
                        Err(error) => {
                            return Err(WindowLoweringRejection {
                                circuit: circuit.to_owned(),
                                layer: layer.layer,
                                resource: error.to_string(),
                            })
                        }
                    }
                }
                Ok(WindowProgramBundle { layers })
            })
            .as_ref()
    }

    /// Whether a windowed proof may be scheduled: the bundle is resolved and
    /// was accepted.
    pub fn window_programs_ready(&self) -> bool {
        matches!(self.window.get(), Some(Ok(_)))
    }

    /// Resolve the dimension-reducing window bundle for one final trace log.
    /// Both accepted bundles and typed rejections are stable cached results.
    pub fn resolve_dr_window_programs(
        &self,
        final_trace_log: u32,
    ) -> Result<Arc<DrWindowProgramBundle>, DrWindowLoweringRejection> {
        {
            let cache = self
                .dr_window
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if let Some(cached) = cache.get(&final_trace_log) {
                return cached.clone();
            }
        }

        let resolved = self.build_dr_window_programs(final_trace_log);
        let mut cache = self
            .dr_window
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        match cache.entry(final_trace_log) {
            std::collections::btree_map::Entry::Occupied(cached) => cached.get().clone(),
            std::collections::btree_map::Entry::Vacant(vacant) => {
                vacant.insert(resolved.clone());
                resolved
            }
        }
    }

    /// Whether this final trace log has a cached, accepted DR window bundle.
    pub fn dr_window_programs_ready(&self, final_trace_log: u32) -> bool {
        let cache = self
            .dr_window
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        matches!(cache.get(&final_trace_log), Some(Ok(_)))
    }

    fn build_dr_window_programs(
        &self,
        final_trace_log: u32,
    ) -> Result<Arc<DrWindowProgramBundle>, DrWindowLoweringRejection> {
        let circuit = forward_artifact(self.circuit_type).1;
        let initial_layer = self.runtime_circuit.layers.len();
        let initial_trace_log = self.runtime_circuit.trace_len.trailing_zeros();
        if final_trace_log > initial_trace_log {
            return Err(DrWindowLoweringRejection::lowering(
                circuit,
                initial_layer,
                format!(
                    "final trace log {final_trace_log} exceeds initial trace log {initial_trace_log}"
                ),
            ));
        }

        let legacy_layers = derive_dimension_reducing_inputs(
            initial_layer,
            &self.runtime_circuit.global_output_map,
            initial_trace_log,
            final_trace_log,
        );
        let layout = GpuGKRStorageLayout::from_artifact_with_tower(
            self.runtime_circuit.as_ref(),
            final_trace_log as usize,
        );
        let mut layers = BTreeMap::new();

        for (layer, legacy_rows) in legacy_layers {
            let rows = adapt_dr_window_rows(circuit, layer, &legacy_rows)?;
            let program = lower_dr_window_program(&rows).map_err(|error| {
                DrWindowLoweringRejection::lowering(circuit, layer, error.to_string())
            })?;
            let input_projection = project_dr_window_inputs(&program, &layout.aliases);
            let folding_steps = layout
                .layers
                .get(layer + 1)
                .map(|output_layout| output_layout.log2_stride as usize)
                .ok_or_else(|| {
                    DrWindowLoweringRejection::lowering(
                        circuit,
                        layer,
                        format!("missing DR output storage layout for layer {}", layer + 1),
                    )
                })?;
            window_dr::validate_dr_window_folding_steps(folding_steps).map_err(|error| {
                DrWindowLoweringRejection::lowering(circuit, layer, error.to_string())
            })?;
            layers.insert(
                layer,
                DrWindowLayerProgram::new(layer, folding_steps, program, input_projection),
            );
        }

        Ok(Arc::new(DrWindowProgramBundle::new(
            final_trace_log,
            layers,
        )))
    }

    /// Lower every layer's continuation program once. A rejection is retained
    /// in the same once-cell, so later calls return the identical failure.
    pub fn resolve_main_continuation_window_programs(
        &self,
    ) -> Result<&MainContinuationWindowProgramBundle, &MainContinuationWindowLoweringRejection>
    {
        self.main_continuation_window
            .get_or_init(|| {
                let circuit = forward_artifact(self.circuit_type).1;
                let mut layers = Vec::with_capacity(self.continuations.layers.len());
                for layer in &self.continuations.layers {
                    match lower_main_continuation_window_program(layer) {
                        Ok(program) => layers.push(program),
                        Err(error) => {
                            return Err(MainContinuationWindowLoweringRejection {
                                circuit: circuit.to_owned(),
                                layer: layer.layer,
                                resource: error.to_string(),
                            });
                        }
                    }
                }
                Ok(MainContinuationWindowProgramBundle { layers })
            })
            .as_ref()
    }

    /// Whether continuation scheduling may begin: the bundle has been resolved
    /// and every layer was accepted.
    pub fn main_continuation_window_programs_ready(&self) -> bool {
        matches!(self.main_continuation_window.get(), Some(Ok(_)))
    }

    /// Lower every layer's static tail program once. A lowering failure remains
    /// in the once-cell, making repeated preflights stable and preventing any
    /// fallback into the scheduling path.
    pub fn resolve_main_tail_programs(
        &self,
    ) -> Result<&MainTailProgramBundle, &MainTailLoweringRejection> {
        self.main_tail
            .get_or_init(|| {
                let circuit = forward_artifact(self.circuit_type).1;
                let mut layers = Vec::with_capacity(self.continuations.layers.len());
                for layer in &self.continuations.layers {
                    match lower_main_tail_program(layer) {
                        Ok(program) => layers.push(program),
                        Err(error) => {
                            return Err(MainTailLoweringRejection {
                                circuit: circuit.to_owned(),
                                layer: layer.layer,
                                resource: error.to_string(),
                            });
                        }
                    }
                }
                Ok(MainTailProgramBundle { layers })
            })
            .as_ref()
    }

    /// Whether main-tail scheduling may begin: the bundle has been resolved and
    /// every layer was accepted.
    pub fn main_tail_programs_ready(&self) -> bool {
        matches!(self.main_tail.get(), Some(Ok(_)))
    }

    /// Seat a rejection in the once-cell so the preflight boundary can be tested
    /// on circuits the real lowering accepts. Returns whether it took effect.
    #[doc(hidden)]
    pub fn reject_window_programs_for_test(&self, rejection: WindowLoweringRejection) -> bool {
        self.window.set(Err(rejection)).is_ok()
    }

    /// Seat a continuation rejection for pre-transfer preflight tests.
    #[doc(hidden)]
    pub fn reject_main_continuation_window_programs_for_test(
        &self,
        rejection: MainContinuationWindowLoweringRejection,
    ) -> bool {
        self.main_continuation_window.set(Err(rejection)).is_ok()
    }

    /// Seat a main-tail rejection for pre-transfer preflight tests.
    #[doc(hidden)]
    pub fn reject_main_tail_programs_for_test(&self, rejection: MainTailLoweringRejection) -> bool {
        self.main_tail.set(Err(rejection)).is_ok()
    }

    pub(crate) fn window_layer(&self, layer: usize) -> &WindowProgram {
        let bundle = self
            .window
            .get()
            .expect("windowed scheduling requires preflight_windowed_backward before prove()")
            .as_ref()
            .expect("windowed scheduling requires an accepted window lowering");
        &bundle.layers[layer]
    }

    #[allow(dead_code)] // The Task 5 binder and Task 6 scheduler consume this accessor.
    pub(crate) fn main_continuation_window_layer(
        &self,
        layer: usize,
    ) -> &MainContinuationWindowProgram {
        let bundle = self
            .main_continuation_window
            .get()
            .expect("continuation scheduling requires preflight_windowed_backward before prove()")
            .as_ref()
            .expect("continuation scheduling requires an accepted continuation lowering");
        &bundle.layers[layer]
    }

    pub fn circuit_type(&self) -> CircuitType {
        self.circuit_type
    }

    pub fn compiled_circuit(&self) -> &Arc<GKRCircuitArtifact<BF>> {
        &self.compiled_circuit
    }

    pub(crate) fn runtime_circuit(&self) -> &Arc<GKRCircuitArtifact<BF>> {
        &self.runtime_circuit
    }

    pub(crate) fn r0_layer(&self, layer: usize) -> &gpu_gkr_compiler::R0LayerProgram {
        &self.r0.layers[layer]
    }

    pub(crate) fn continuation_layer(
        &self,
        layer: usize,
    ) -> &gpu_gkr_compiler::ContinuationLayerProgram {
        &self.continuations.layers[layer]
    }
}

fn adapt_dr_window_rows(
    circuit: &str,
    layer: usize,
    legacy_rows: &BTreeMap<OutputType, DimensionReducingInputOutput>,
) -> Result<BTreeMap<OutputType, DrWindowInputOutput>, DrWindowLoweringRejection> {
    legacy_rows
        .iter()
        .map(|(output_type, legacy)| {
            adapt_dr_window_row(circuit, layer, *output_type, legacy).map(|row| (*output_type, row))
        })
        .collect()
}

fn adapt_dr_window_row(
    circuit: &str,
    layer: usize,
    output_type: OutputType,
    legacy: &DimensionReducingInputOutput,
) -> Result<DrWindowInputOutput, DrWindowLoweringRejection> {
    let inputs = adapt_dr_window_addresses(
        circuit,
        layer,
        output_type,
        DrWindowLegacyRowSide::Input,
        &legacy.inputs,
    )?;
    let outputs = adapt_dr_window_addresses(
        circuit,
        layer,
        output_type,
        DrWindowLegacyRowSide::Output,
        &legacy.output,
    )?;
    Ok(DrWindowInputOutput::new(inputs, outputs))
}

fn adapt_dr_window_addresses(
    circuit: &str,
    layer: usize,
    output_type: OutputType,
    side: DrWindowLegacyRowSide,
    addresses: &[GKRAddress],
) -> Result<[GKRAddress; 2], DrWindowLoweringRejection> {
    let actual_count = addresses.len();
    let fixed: &[GKRAddress; 2] = addresses.try_into().map_err(|_| {
        DrWindowLoweringRejection::legacy_arity(circuit, layer, output_type, side, 2, actual_count)
    })?;
    Ok(*fixed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use gpu_gkr_compiler::{LeanBoundColumn, LeanBoundWindow, LeanSourceBinding};
    use std::collections::BTreeSet;

    #[test]
    fn cpu_windowed_selector_lowers_one_window_program_per_layer() {
        let (programs, layers) =
            crate::backward::compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");
        assert!(!programs.window_programs_ready());
        let bundle = programs.resolve_window_programs().unwrap();
        assert!(layers > 1);
        assert_eq!(bundle.layers.len(), layers);
        for (index, program) in bundle.layers.iter().enumerate() {
            assert_eq!(program.layer, index);
        }
        assert!(programs.window_programs_ready());
    }

    #[test]
    fn bound_inputs_include_cache_and_virtual_setup_sources() {
        let binding = LeanSourceBinding {
            windows: vec![
                LeanBoundWindow {
                    family: WindowFamily::CacheOutput {
                        layer: 2,
                        ext: true,
                    },
                    first_column: 7,
                    columns: vec![LeanBoundColumn {
                        column: 7,
                        source: 0,
                    }],
                },
                LeanBoundWindow {
                    family: WindowFamily::VirtualSetup { kind: 0 },
                    first_column: 0,
                    columns: vec![LeanBoundColumn {
                        column: 0,
                        source: 1,
                    }],
                },
            ],
            source_slots: Vec::new(),
        };
        let inputs: BTreeSet<_> = binding
            .windows
            .iter()
            .flat_map(|window| {
                window
                    .columns
                    .iter()
                    .map(|column| bound_window_address(window.family, column.column))
            })
            .collect();
        assert_eq!(
            inputs,
            BTreeSet::from([
                GKRAddress::Cached {
                    layer: 2,
                    offset: 7
                },
                GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits),
            ])
        );
    }

    #[test]
    fn dr_window_program_legacy_adapter_owns_input_and_output_arity_rejections() {
        let address = |offset| GKRAddress::InnerLayer { layer: 9, offset };
        let context = ("adapter_circuit", 17, OutputType::LookupTimestamps);
        let bad_input = DimensionReducingInputOutput {
            inputs: vec![address(0)],
            output: vec![address(1), address(2)],
        };
        let input_error = adapt_dr_window_row(context.0, context.1, context.2, &bad_input)
            .expect_err("one legacy input must be rejected");
        assert_eq!(input_error.circuit(), context.0);
        assert_eq!(input_error.layer(), context.1);
        assert_eq!(input_error.output_type(), Some(context.2));
        assert_eq!(input_error.expected_count(), Some(2));
        assert_eq!(input_error.actual_count(), Some(1));
        assert_eq!(input_error.legacy_row_side(), Some("input"));

        let bad_output = DimensionReducingInputOutput {
            inputs: vec![address(0), address(1)],
            output: vec![address(2), address(3), address(4)],
        };
        let output_error = adapt_dr_window_row(context.0, context.1, context.2, &bad_output)
            .expect_err("three legacy outputs must be rejected");
        assert_eq!(output_error.circuit(), context.0);
        assert_eq!(output_error.layer(), context.1);
        assert_eq!(output_error.output_type(), Some(context.2));
        assert_eq!(output_error.expected_count(), Some(2));
        assert_eq!(output_error.actual_count(), Some(3));
        assert_eq!(output_error.legacy_row_side(), Some("output"));
    }
}
