mod binding;

pub(crate) use binding::{
    schedule_dr_batch_challenge_table_pr, unwrap_dr_window_pr, DrLayerTranscriptPr,
    DrWindowLayerHookPr, DrWindowRawInputKeepalivePr,
};

#[cfg(test)]
pub(crate) use binding::PR_DR_WINDOW_ARGUMENT_BYTES;

use std::collections::BTreeMap;
use std::sync::Arc;

use gpu_gkr_compiler::{lower_dr_window_program, project_dr_window_inputs};

use crate::backward::window_dr::{validate_dr_window_folding_steps, DrWindowBindError};
use crate::backward::{derive_dimension_reducing_inputs, make_eq_sizes, GkrEqSizes};
use crate::proth120::programs::GkrProgramsPr;
use crate::upstream::{GKRAddress, OutputType};
use crate::DrWindowLayerProgram;

pub(crate) const PR_DR_WINDOW_COORDINATES: usize = 3;
pub(crate) const PR_DR_MAX_ENTRY_ROUND: usize = 15;

pub(crate) fn compile_dr_window_programs_pr(
    programs: &GkrProgramsPr,
    final_trace_log_2: u32,
) -> BTreeMap<usize, Arc<DrWindowLayerProgram>> {
    assert_eq!(
        final_trace_log_2, 4,
        "Proth120 DR window programs support final trace log 4 only"
    );
    let circuit = programs.runtime_circuit.as_ref();
    let initial_trace_log = circuit.trace_len.trailing_zeros();
    let layout = &programs.storage_layout;
    derive_dimension_reducing_inputs(
        circuit.layers.len(),
        &circuit.global_output_map,
        initial_trace_log,
        final_trace_log_2,
    )
    .into_iter()
    .map(|(layer, inputs)| {
        let rows: BTreeMap<OutputType, [GKRAddress; 2]> = inputs
            .iter()
            .map(|(output_type, source)| {
                (
                    *output_type,
                    source
                        .inputs
                        .as_slice()
                        .try_into()
                        .expect("Proth120 DR inputs must be pairs"),
                )
            })
            .collect();
        let program = lower_dr_window_program(&rows).unwrap_or_else(|error| {
            panic!("Proth120 DR window lowering at layer {layer}: {error}")
        });
        let input_projection = project_dr_window_inputs(&program, &layout.aliases);
        let folding_steps = layout
            .layers
            .get(layer + 1)
            .map(|output_layout| output_layout.log2_stride as usize)
            .unwrap_or_else(|| panic!("Proth120 DR layer {layer} has no output layout"));
        validate_dr_window_folding_steps(folding_steps)
            .unwrap_or_else(|error| panic!("Proth120 DR window layer {layer}: {error}"));
        (
            layer,
            Arc::new(DrWindowLayerProgram::new(
                layer,
                folding_steps,
                program,
                input_projection,
            )),
        )
    })
    .collect()
}

pub(crate) fn dr_window_continuation_count_pr(entry_round: usize) -> usize {
    if entry_round == 0 {
        return 0;
    }
    assert!(
        entry_round >= PR_DR_WINDOW_COORDINATES
            && entry_round.is_multiple_of(PR_DR_WINDOW_COORDINATES),
        "Proth120 DR tail entry round {entry_round} is not a window boundary"
    );
    (entry_round - PR_DR_WINDOW_COORDINATES) / PR_DR_WINDOW_COORDINATES
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DrWindowParityPr {
    Even,
    Odd,
}

impl DrWindowParityPr {
    fn index(self) -> usize {
        match self {
            Self::Even => 0,
            Self::Odd => 1,
        }
    }

    fn opposite(self) -> Self {
        match self {
            Self::Even => Self::Odd,
            Self::Odd => Self::Even,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrWindowPassGeometryPr {
    pub(crate) folding_steps: usize,
    pub(crate) start_round: usize,
}

impl DrWindowPassGeometryPr {
    pub(crate) fn new(folding_steps: usize, start_round: usize) -> Result<Self, DrWindowBindError> {
        if start_round < PR_DR_WINDOW_COORDINATES
            || !start_round.is_multiple_of(PR_DR_WINDOW_COORDINATES)
            || start_round + PR_DR_WINDOW_COORDINATES >= folding_steps
        {
            return Err(DrWindowBindError::InvalidContinuationBoundary {
                folding_steps,
                start_round,
            });
        }
        Ok(Self {
            folding_steps,
            start_round,
        })
    }

    fn pass_index(self) -> usize {
        (self.start_round - PR_DR_WINDOW_COORDINATES) / PR_DR_WINDOW_COORDINATES
    }

    pub(crate) fn destination(self) -> DrWindowParityPr {
        if self.pass_index().is_multiple_of(2) {
            DrWindowParityPr::Even
        } else {
            DrWindowParityPr::Odd
        }
    }

    pub(crate) fn reads_raw_storage(self) -> bool {
        self.pass_index() == 0
    }

    pub(crate) fn log2_stride(self) -> u32 {
        (self.folding_steps + 1 - self.start_round) as u32
    }

    pub(crate) fn suffix_folding_steps(self) -> usize {
        self.folding_steps - self.start_round
    }

    pub(crate) fn eq_challenge_offset(self) -> usize {
        self.start_round + PR_DR_WINDOW_COORDINATES
    }

    pub(crate) fn eq_entry_sizes(self) -> GkrEqSizes {
        make_eq_sizes(self.folding_steps - self.eq_challenge_offset())
    }
}

pub(crate) fn plan_dr_window_continuations_pr(
    folding_steps: usize,
    entry_round: usize,
) -> Result<Vec<DrWindowPassGeometryPr>, DrWindowBindError> {
    if !(PR_DR_WINDOW_COORDINATES..=PR_DR_MAX_ENTRY_ROUND).contains(&entry_round)
        || !entry_round.is_multiple_of(PR_DR_WINDOW_COORDINATES)
        || entry_round >= folding_steps
    {
        return Err(DrWindowBindError::InvalidTailEntry { entry_round });
    }
    (PR_DR_WINDOW_COORDINATES..entry_round)
        .step_by(PR_DR_WINDOW_COORDINATES)
        .map(|start_round| DrWindowPassGeometryPr::new(folding_steps, start_round))
        .collect()
}
