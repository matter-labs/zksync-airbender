use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use gpu_prover_context::ProverContext;

use super::{
    dr_tail_attributes_pr, dr_tail_device_optin_cap_bytes_pr, dr_tail_occupancy_pr,
    set_dr_tail_max_dynamic_smem_bytes_pr,
};
use crate::backward::{
    derive_dimension_reducing_inputs, dim_reducing_slot_index, GpuGKRDimensionReducingLayerSlots,
    GpuGKRDimensionReducingSlotPlan, GKR_DIM_REDUCING_INPUTS_PER_SLOT,
    GKR_DIM_REDUCING_OUTPUTS_PER_SLOT,
};
use crate::proth120::backward::capacity::{
    dr_tail_entry_round_pr, select_capacity_pr, DrTailCapacityDecisionPr, DrTailCapacityRequestPr,
};
use crate::proth120::backward::dr_tail::{PR_DR_TAIL_MAX_REMAINING_ROUNDS, PR_DR_TAIL_MAX_SOURCES};
use crate::proth120::backward::window_dr::{
    compile_dr_window_programs_pr, dr_window_continuation_count_pr, PR_DR_MAX_ENTRY_ROUND,
};
use crate::proth120::programs::GkrProgramsPr;
use crate::upstream::{DimensionReducingInputOutput, GKRAddress, OutputType};
use crate::DrWindowLayerProgram;

pub(crate) const PR_DR_FINAL_TRACE_LOG_2: u32 = 4;
const PR_DR_LAYER_COUNT: usize = 18;
const PR_DR_MIN_FOLDING_STEPS: usize = 4;
const PR_DR_MAX_FOLDING_STEPS: usize = 21;

pub(crate) fn dimension_reducing_slots_pr(
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
) -> GpuGKRDimensionReducingLayerSlots {
    let mut layer_slots = GpuGKRDimensionReducingLayerSlots::default();
    let mut next_batch_exp = 0u16;
    for (output_type, reduced) in layer {
        let inputs: [GKRAddress; GKR_DIM_REDUCING_INPUTS_PER_SLOT] =
            reduced.inputs.clone().try_into().unwrap_or_else(|_| {
                panic!("Proth120 dimension-reducing {output_type:?} expects two inputs")
            });
        let outputs: [GKRAddress; GKR_DIM_REDUCING_OUTPUTS_PER_SLOT] =
            reduced.output.clone().try_into().unwrap_or_else(|_| {
                panic!("Proth120 dimension-reducing {output_type:?} expects two outputs")
            });
        let batch_exp = [next_batch_exp, next_batch_exp + 1];
        next_batch_exp += GKR_DIM_REDUCING_OUTPUTS_PER_SLOT as u16;
        let previous = layer_slots.slots[dim_reducing_slot_index(*output_type)].replace(
            GpuGKRDimensionReducingSlotPlan {
                inputs,
                outputs,
                batch_exp,
            },
        );
        assert!(
            previous.is_none(),
            "Proth120 duplicate dimension-reducing slot for {output_type:?}"
        );
    }
    layer_slots
}

struct DrTailLayerInputPr {
    layer_idx: usize,
    folding_steps: usize,
    canonical_sources: Vec<GKRAddress>,
}

fn dr_tail_layer_inputs_pr(programs: &GkrProgramsPr) -> Vec<DrTailLayerInputPr> {
    let artifact = programs.runtime_circuit.as_ref();
    let trace_log = artifact.trace_len.trailing_zeros() as usize;
    let aliases = &programs.storage_layout.aliases;
    derive_dimension_reducing_inputs(
        artifact.layers.len(),
        &artifact.global_output_map,
        trace_log as u32,
        PR_DR_FINAL_TRACE_LOG_2,
    )
    .into_iter()
    .map(|(layer_idx, layer)| {
        let layer_offset = layer_idx - artifact.layers.len();
        let folding_steps = trace_log
            .checked_sub(layer_offset)
            .and_then(|value| value.checked_sub(1))
            .expect("Proth120 DR folding width underflowed");
        let canonical_sources = dimension_reducing_slots_pr(&layer)
            .input_addresses()
            .map(|address| aliases.get(&address).copied().unwrap_or(address))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        DrTailLayerInputPr {
            layer_idx,
            folding_steps,
            canonical_sources,
        }
    })
    .collect()
}

fn validate_dr_tail_shapes_pr(inputs: &[DrTailLayerInputPr]) {
    assert_eq!(
        inputs.len(),
        PR_DR_LAYER_COUNT,
        "Proth120 DR tail expects {PR_DR_LAYER_COUNT} dimension-reducing layers"
    );
    for input in inputs {
        assert!(
            (PR_DR_MIN_FOLDING_STEPS..=PR_DR_MAX_FOLDING_STEPS).contains(&input.folding_steps),
            "Proth120 DR layer {} folds {} variables, outside {PR_DR_MIN_FOLDING_STEPS}..={PR_DR_MAX_FOLDING_STEPS}",
            input.layer_idx,
            input.folding_steps
        );
        assert!(
            (1..=PR_DR_TAIL_MAX_SOURCES).contains(&input.canonical_sources.len()),
            "Proth120 DR layer {} has {} canonical sources",
            input.layer_idx,
            input.canonical_sources.len()
        );
        let entry_round = dr_tail_entry_round_pr(input.folding_steps);
        assert!(
            entry_round <= PR_DR_MAX_ENTRY_ROUND
                && input.folding_steps - entry_round <= PR_DR_TAIL_MAX_REMAINING_ROUNDS,
            "Proth120 DR layer {} tail entry round {entry_round} is unsupported",
            input.layer_idx
        );
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DrTailLayerPlanPr {
    layer_idx: usize,
    folding_steps: usize,
    canonical_sources: Vec<GKRAddress>,
    capacity: DrTailCapacityDecisionPr,
}

impl DrTailLayerPlanPr {
    pub(crate) fn layer_idx(&self) -> usize {
        self.layer_idx
    }

    pub(crate) fn folding_steps(&self) -> usize {
        self.folding_steps
    }

    pub(crate) fn canonical_sources(&self) -> &[GKRAddress] {
        &self.canonical_sources
    }

    pub(crate) fn capacity(&self) -> DrTailCapacityDecisionPr {
        self.capacity
    }
}

fn plan_dr_tail_layers_pr(
    programs: &GkrProgramsPr,
    static_smem_bytes: usize,
    device_cap_bytes: usize,
) -> Vec<DrTailLayerPlanPr> {
    let inputs = dr_tail_layer_inputs_pr(programs);
    validate_dr_tail_shapes_pr(&inputs);
    inputs
        .into_iter()
        .map(|input| {
            let capacity = select_capacity_pr(DrTailCapacityRequestPr {
                folding_steps: input.folding_steps,
                canonical_sources: input.canonical_sources.len(),
                static_smem_bytes,
                device_cap_bytes,
            });
            DrTailLayerPlanPr {
                layer_idx: input.layer_idx,
                folding_steps: input.folding_steps,
                canonical_sources: input.canonical_sources,
                capacity,
            }
        })
        .collect()
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DrTailProofPlanPr {
    device_id: i32,
    final_trace_log_2: u32,
    static_smem_bytes: usize,
    local_bytes: usize,
    device_cap_bytes: usize,
    max_dynamic_smem_bytes: usize,
    occupancy: Vec<(usize, u32)>,
    layers: Vec<DrTailLayerPlanPr>,
    window_programs: BTreeMap<usize, Arc<DrWindowLayerProgram>>,
}

impl DrTailProofPlanPr {
    pub fn validate_before_enqueue(
        &self,
        programs: &GkrProgramsPr,
        final_trace_log_2: u32,
        context: &ProverContext,
    ) {
        let current = era_cudart::device::get_device()
            .expect("Proth120 DR-tail enqueue must observe the scheduling device");
        assert_eq!(
            current,
            context.get_device_id(),
            "Proth120 proof scheduling must run on the context device"
        );
        assert_eq!(
            context.get_device_id(),
            self.device_id,
            "Proth120 DR-tail plan was admitted on another device"
        );
        assert_eq!(
            final_trace_log_2, self.final_trace_log_2,
            "Proth120 DR-tail plan was admitted for another final trace log"
        );
        let expected =
            plan_dr_tail_layers_pr(programs, self.static_smem_bytes, self.device_cap_bytes);
        assert_eq!(
            self.layers, expected,
            "Proth120 DR-tail plan does not match the programs"
        );
    }

    pub(crate) fn layers(&self) -> &[DrTailLayerPlanPr] {
        &self.layers
    }

    pub(crate) fn layer(&self, layer_idx: usize) -> &DrTailLayerPlanPr {
        self.layers
            .iter()
            .find(|layer| layer.layer_idx == layer_idx)
            .unwrap_or_else(|| panic!("Proth120 DR-tail plan is missing layer {layer_idx}"))
    }

    pub(crate) fn window_program(&self, layer_idx: usize) -> &Arc<DrWindowLayerProgram> {
        self.window_programs.get(&layer_idx).unwrap_or_else(|| {
            panic!("Proth120 DR window program is missing absolute layer {layer_idx}")
        })
    }

    pub(crate) fn cursor(&self) -> DrTailPlanCursorPr<'_> {
        DrTailPlanCursorPr {
            layers: &self.layers,
            consumed: BTreeSet::new(),
        }
    }

    pub(crate) fn admission_record(&self) -> String {
        let layers = self
            .layers
            .iter()
            .map(|layer| {
                format!(
                    "{{\"layer\":{},\"folding_steps\":{},\"sources\":{},\"entry_round\":{},\"global_state_bytes\":{},\"dynamic_smem_bytes\":{}}}",
                    layer.layer_idx,
                    layer.folding_steps,
                    layer.canonical_sources.len(),
                    layer.capacity.entry_round,
                    layer.capacity.global_state_bytes,
                    layer.capacity.dynamic_smem_bytes
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        let occupancy = self
            .occupancy
            .iter()
            .map(|(bytes, blocks)| {
                format!("{{\"dynamic_smem_bytes\":{bytes},\"blocks_per_sm\":{blocks}}}")
            })
            .collect::<Vec<_>>()
            .join(",");
        format!(
            "{{\"device_id\":{},\"final_trace_log_2\":{},\"static_smem_bytes\":{},\"local_bytes\":{},\"device_cap_bytes\":{},\"max_dynamic_smem_bytes\":{},\"occupancy\":[{occupancy}],\"layers\":[{layers}]}}",
            self.device_id,
            self.final_trace_log_2,
            self.static_smem_bytes,
            self.local_bytes,
            self.device_cap_bytes,
            self.max_dynamic_smem_bytes
        )
    }
}

pub(crate) struct DrTailPlanCursorPr<'a> {
    layers: &'a [DrTailLayerPlanPr],
    consumed: BTreeSet<usize>,
}

impl DrTailPlanCursorPr<'_> {
    pub(crate) fn bind(
        &mut self,
        layer_idx: usize,
        folding_steps: usize,
        canonical_sources: &[GKRAddress],
    ) -> DrTailCapacityDecisionPr {
        let planned = self
            .layers
            .iter()
            .find(|planned| planned.layer_idx == layer_idx)
            .unwrap_or_else(|| panic!("Proth120 DR-tail plan is missing layer {layer_idx}"));
        assert_eq!(
            planned.folding_steps, folding_steps,
            "Proth120 DR-tail plan folding steps differ at layer {layer_idx}"
        );
        assert_eq!(
            planned.canonical_sources, canonical_sources,
            "Proth120 DR-tail plan sources differ at layer {layer_idx}"
        );
        assert!(
            self.consumed.insert(layer_idx),
            "Proth120 DR-tail plan layer {layer_idx} bound twice"
        );
        planned.capacity
    }

    pub(crate) fn finish(self) {
        assert_eq!(
            self.consumed.len(),
            self.layers.len(),
            "Proth120 DR-tail plan has unconsumed layers"
        );
    }
}

pub fn preflight_dr_tail_resources_pr(
    programs: &GkrProgramsPr,
    final_trace_size_log_2: u32,
    context: &ProverContext,
) -> DrTailProofPlanPr {
    assert_eq!(
        final_trace_size_log_2, PR_DR_FINAL_TRACE_LOG_2,
        "Proth120 DR tail supports final trace log 4 only"
    );
    validate_dr_tail_shapes_pr(&dr_tail_layer_inputs_pr(programs));
    let device_id = context.get_device_id();
    let current = era_cudart::device::get_device()
        .expect("Proth120 DR-tail admission must observe the scheduling device");
    assert_eq!(
        current, device_id,
        "Proth120 DR-tail admission must run on the context device"
    );
    let attributes =
        dr_tail_attributes_pr().expect("Proth120 DR-tail admission: cudaFuncGetAttributes failed");
    assert_eq!(
        attributes.local_bytes, 0,
        "Proth120 DR-tail kernel spills to local memory"
    );
    let device_cap_bytes = dr_tail_device_optin_cap_bytes_pr(device_id)
        .expect("Proth120 DR-tail admission: shared-memory opt-in query failed");
    let layers = plan_dr_tail_layers_pr(programs, attributes.static_smem_bytes, device_cap_bytes);
    let mut selected: Vec<usize> = layers
        .iter()
        .map(|layer| layer.capacity.dynamic_smem_bytes)
        .collect();
    selected.sort_unstable();
    selected.dedup();
    let max_dynamic = *selected
        .last()
        .expect("Proth120 DR-tail plan has no layers");
    let retained_ceiling = attributes.max_dynamic_smem_bytes.max(max_dynamic);
    set_dr_tail_max_dynamic_smem_bytes_pr(retained_ceiling)
        .expect("Proth120 DR-tail admission: setting the dynamic shared-memory ceiling failed");
    let effective = dr_tail_attributes_pr()
        .expect("Proth120 DR-tail admission: cudaFuncGetAttributes failed")
        .max_dynamic_smem_bytes;
    assert!(
        max_dynamic <= effective,
        "Proth120 DR-tail dynamic shared-memory ceiling was not applied"
    );
    let occupancy = selected
        .into_iter()
        .map(|bytes| {
            let blocks = dr_tail_occupancy_pr(bytes)
                .expect("Proth120 DR-tail admission: occupancy query failed");
            assert_ne!(blocks, 0, "Proth120 DR-tail kernel has zero occupancy");
            (bytes, blocks)
        })
        .collect();
    let window_programs = compile_dr_window_programs_pr(programs, final_trace_size_log_2);
    for layer in &layers {
        let program = window_programs.get(&layer.layer_idx).unwrap_or_else(|| {
            panic!(
                "Proth120 DR window program is missing absolute layer {}",
                layer.layer_idx
            )
        });
        assert_eq!(
            program.folding_steps(),
            layer.folding_steps,
            "Proth120 DR window geometry differs at layer {}",
            layer.layer_idx
        );
        assert_eq!(
            program.input_projection().canonical_sources(),
            layer.canonical_sources.as_slice(),
            "Proth120 DR window projection differs at layer {}",
            layer.layer_idx
        );
        if dr_window_continuation_count_pr(layer.capacity.entry_round) != 0 {
            gpu_gkr_compiler::validate_dr_window_split_ownership(program.input_projection())
                .unwrap_or_else(|error| {
                    panic!(
                        "Proth120 DR continuation split admission at layer {}: {error}",
                        layer.layer_idx
                    )
                });
        }
    }
    DrTailProofPlanPr {
        device_id,
        final_trace_log_2: final_trace_size_log_2,
        static_smem_bytes: attributes.static_smem_bytes,
        local_bytes: attributes.local_bytes,
        device_cap_bytes,
        max_dynamic_smem_bytes: effective,
        occupancy,
        layers,
        window_programs,
    }
}
