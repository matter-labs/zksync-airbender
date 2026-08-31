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
    window: OnceLock<WindowProgramBundle>,
    /// Dimension-reducing programs depend on proof geometry.
    dr_window: Mutex<BTreeMap<u32, Arc<DrWindowProgramBundle>>>,
    /// Lowered independently from R0 on the first proof whose per-layer plan
    /// selects at least one continuation window.
    main_continuation_window: OnceLock<MainContinuationWindowProgramBundle>,
    /// Lowered on the first proof that requests the main-tail arm.
    main_tail: OnceLock<MainTailProgramBundle>,
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

    pub fn resolve_window_programs(&self) -> &WindowProgramBundle {
        self.window.get_or_init(|| WindowProgramBundle {
            layers: self
                .r0
                .layers
                .iter()
                .map(|layer| lower_window_program(layer).unwrap())
                .collect(),
        })
    }

    pub fn window_programs_ready(&self) -> bool {
        self.window.get().is_some()
    }

    pub fn resolve_dr_window_programs(&self, final_trace_log: u32) -> Arc<DrWindowProgramBundle> {
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

    pub fn dr_window_programs_ready(&self, final_trace_log: u32) -> bool {
        let cache = self
            .dr_window
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        cache.contains_key(&final_trace_log)
    }

    fn build_dr_window_programs(&self, final_trace_log: u32) -> Arc<DrWindowProgramBundle> {
        let initial_layer = self.runtime_circuit.layers.len();
        let initial_trace_log = self.runtime_circuit.trace_len.trailing_zeros();
        assert!(final_trace_log <= initial_trace_log);

        let layer_inputs = derive_dimension_reducing_inputs(
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

        for (layer, inputs) in layer_inputs {
            let rows = adapt_dr_window_rows(&inputs);
            let program = lower_dr_window_program(&rows).unwrap();
            let input_projection = project_dr_window_inputs(&program, &layout.aliases);
            let folding_steps = layout
                .layers
                .get(layer + 1)
                .map(|output_layout| output_layout.log2_stride as usize)
                .unwrap();
            window_dr::validate_dr_window_folding_steps(folding_steps).unwrap();
            layers.insert(
                layer,
                DrWindowLayerProgram::new(layer, folding_steps, program, input_projection),
            );
        }

        Arc::new(DrWindowProgramBundle::new(final_trace_log, layers))
    }

    pub fn resolve_main_continuation_window_programs(
        &self,
    ) -> &MainContinuationWindowProgramBundle {
        self.main_continuation_window
            .get_or_init(|| MainContinuationWindowProgramBundle {
                layers: self
                    .continuations
                    .layers
                    .iter()
                    .map(|layer| lower_main_continuation_window_program(layer).unwrap())
                    .collect(),
            })
    }

    pub fn main_continuation_window_programs_ready(&self) -> bool {
        self.main_continuation_window.get().is_some()
    }

    pub fn resolve_main_tail_programs(&self) -> &MainTailProgramBundle {
        self.main_tail.get_or_init(|| MainTailProgramBundle {
            layers: self
                .continuations
                .layers
                .iter()
                .map(lower_main_tail_program)
                .collect(),
        })
    }

    pub fn main_tail_programs_ready(&self) -> bool {
        self.main_tail.get().is_some()
    }

    pub(crate) fn window_layer(&self, layer: usize) -> &WindowProgram {
        let bundle = self
            .window
            .get()
            .expect("windowed scheduling requires preflight_windowed_backward before prove()");
        &bundle.layers[layer]
    }

    pub(crate) fn main_continuation_window_layer(
        &self,
        layer: usize,
    ) -> &MainContinuationWindowProgram {
        let bundle = self
            .main_continuation_window
            .get()
            .expect("continuation scheduling requires preflight_windowed_backward before prove()");
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

    pub(crate) fn continuation_layer(
        &self,
        layer: usize,
    ) -> &gpu_gkr_compiler::ContinuationLayerProgram {
        &self.continuations.layers[layer]
    }
}

fn adapt_dr_window_rows(
    source_rows: &BTreeMap<OutputType, DimensionReducingInputOutput>,
) -> BTreeMap<OutputType, DrWindowInputOutput> {
    source_rows
        .iter()
        .map(|(output_type, source)| (*output_type, adapt_dr_window_row(source)))
        .collect()
}

fn adapt_dr_window_row(source: &DimensionReducingInputOutput) -> DrWindowInputOutput {
    DrWindowInputOutput::new(
        adapt_dr_window_addresses(&source.inputs),
        adapt_dr_window_addresses(&source.output),
    )
}

fn adapt_dr_window_addresses(addresses: &[GKRAddress]) -> [GKRAddress; 2] {
    *<&[GKRAddress; 2]>::try_from(addresses).unwrap()
}
