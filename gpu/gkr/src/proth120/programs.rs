use std::sync::Arc;

use gpu_gkr_compiler::geometry::{validate_proth120, BackwardPrograms, GeometryReport};
use gpu_gkr_compiler::{
    compile_continuations_with_model, compile_forward_with_model, compile_r0_with_model,
    lower_main_continuation_window_program, lower_main_tail_program, parse_forward_artifact,
    ContinuationProgramBundle, ElementModel, FieldTag, ForwardProgramBundle,
    MainContinuationWindowProgram, MainTailProgram, R0WindowProgram,
};
use gpu_trace::witness::circuit_type::CircuitType;

use super::backward::main_continuation_window_manifest::PR_MAIN_CONTINUATION_MASKS;
use super::forward::challenge_banks::ForwardChallengePlan;
use super::forward::desc::PR_FWD_VM_BUCKETS;
use crate::programs::{backward_layer_plans, BackwardLayerPlan};
use crate::storage_layout::GpuGKRStorageLayout;
use crate::transform::normalize_compiled_circuit_for_gpu;
use crate::upstream::{GKRCircuitArtifact, PR};

pub struct GkrProgramsPr {
    pub forward: ForwardProgramBundle,
    pub runtime_circuit: Arc<GKRCircuitArtifact<PR>>,
    pub dag: gkr_eval_ir::DagCircuit,
    pub challenge_plan: ForwardChallengePlan,
    pub r0: Vec<R0WindowProgram>,
    pub continuations: ContinuationProgramBundle,
    pub main_continuation_window: Vec<MainContinuationWindowProgram>,
    pub main_tail: Vec<MainTailProgram>,
    pub geometry: GeometryReport,
    pub(crate) storage_layout: Arc<GpuGKRStorageLayout>,
    pub(crate) backward_layers: Vec<BackwardLayerPlan>,
}

const SCHEDULE: &[u8] = include_bytes!(
    "../../../../cs/compiled_circuits/unified_reduced_machine_schedule_b4_gkr_proth120.json"
);
const _: () = assert!(PR_FWD_VM_BUCKETS == 4);

impl GkrProgramsPr {
    pub fn compile(
        circuit_type: CircuitType,
        artifact: Arc<GKRCircuitArtifact<PR>>,
    ) -> Result<Self, String> {
        assert_eq!(
            circuit_type,
            CircuitType::L1Wrap,
            "Proth120 GKR supports CircuitType::L1Wrap only"
        );
        Self::compile_with_schedule(artifact, SCHEDULE)
    }

    pub(crate) fn compile_with_schedule(
        artifact: Arc<GKRCircuitArtifact<PR>>,
        schedule: &[u8],
    ) -> Result<Self, String> {
        let searched = parse_forward_artifact(schedule, "Proth120 forward schedule")
            .map_err(|error| error.to_string())?;
        assert_eq!(
            searched.field,
            Some(FieldTag::Proth120),
            "Proth120 forward schedule field tag mismatch"
        );
        assert_eq!(
            searched.budget_buckets, PR_FWD_VM_BUCKETS as usize,
            "Proth120 forward schedule bucket budget mismatch"
        );
        assert_eq!(
            searched.circuit, "unified_reduced_machine",
            "Proth120 forward schedule circuit mismatch"
        );
        let runtime_circuit = Arc::new(normalize_compiled_circuit_for_gpu((*artifact).clone()));
        let dag = gkr_eval_ir::lower_dag(&artifact)?;
        let model = ElementModel::PROTH120;
        let forward = compile_forward_with_model(&dag, &searched, model)
            .map_err(|e| format!("Proth120 forward compile: {e:?}"))?;
        let r0 = compile_r0_with_model(&dag, model)
            .map_err(|e| format!("Proth120 R0 compile: {e:?}"))?;
        let continuations = compile_continuations_with_model(&dag, model)
            .map_err(|e| format!("Proth120 continuation compile: {e:?}"))?;
        let main_continuation_window = continuations
            .layers
            .iter()
            .map(lower_main_continuation_window_program)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| format!("Proth120 main continuation: {e}"))?;
        assert!(
            main_continuation_window
                .iter()
                .all(|w| u8::try_from(w.shape.bits())
                    .ok()
                    .is_some_and(|m| PR_MAIN_CONTINUATION_MASKS.contains(&m))),
            "Proth120 main continuation mask is unsupported"
        );
        let main_tail: Vec<MainTailProgram> = continuations
            .layers
            .iter()
            .map(lower_main_tail_program)
            .collect();
        let geometry = validate_proth120(
            &dag,
            &forward,
            &BackwardPrograms {
                r0: &r0,
                continuations: &continuations,
                main_continuation_window: &main_continuation_window,
                main_tail: &main_tail,
            },
            &artifact,
        )
        .map_err(|e| format!("Proth120 native geometry: {e}"))?;
        let challenge_plan = ForwardChallengePlan::new(&dag, &forward, &runtime_circuit);
        let backward_layers = backward_layer_plans(&dag, &continuations);
        let storage_layout = Arc::new(GpuGKRStorageLayout::from_artifact_with_tower(
            &runtime_circuit,
            4,
        ));
        Ok(Self {
            forward,
            runtime_circuit,
            dag,
            challenge_plan,
            r0,
            continuations,
            main_continuation_window,
            main_tail,
            geometry,
            storage_layout,
            backward_layers,
        })
    }
}
