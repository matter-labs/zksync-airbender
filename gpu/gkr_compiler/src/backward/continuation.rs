use std::collections::{BTreeSet, HashMap};

use gkr_eval_ir::{DagCircuit, FieldKind, ReadPlace};

use super::common::distill::distill;
use super::common::group::group_coeff_layer;
use super::common::interp::{CoeffResolver, LeanInterpError, interpret_lean_program};
use super::common::lean::{LeanCodecError, LeanProgram, encode_program_atoms, validate_program};
use super::common::lean_bind::{LeanBindError, LeanSourceBinding, bind_lean_sources_with_limits};
use super::common::lower::lower_coeff_layer_traced;
use super::common::model::{CoeffError, CoeffLayer, ProjectionId, TermId};
use super::common::order::{flatten_atoms, order_atoms};
use crate::analysis::build_cross_layer_field_map;
use crate::{
    ContinuationResourceProfile, GpuResourceProfile, ResourceProfileError,
    validate_continuation_profile,
};

const PUBLICATION_DEPTH: u8 = 3;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContinuationProgramBundle {
    pub layers: Vec<ContinuationLayerProgram>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContinuationLayerProgram {
    pub layer: usize,
    pub coefficients: CoeffLayer,
    pub order: Vec<u32>,
    pub program: LeanProgram,
    pub binding: LeanSourceBinding,
}

impl ContinuationLayerProgram {
    pub const fn publication_depth(&self) -> u8 {
        PUBLICATION_DEPTH
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContinuationCompileError {
    Profile(ResourceProfileError),
    Lower {
        layer: usize,
        error: CoeffError,
    },
    Codec {
        layer: usize,
        error: LeanCodecError,
    },
    Bind {
        layer: usize,
        error: LeanBindError,
    },
    OrderCoverage {
        layer: usize,
    },
    Capacity {
        layer: usize,
        resource: &'static str,
        required: usize,
        maximum: usize,
    },
}

impl core::fmt::Display for ContinuationCompileError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for ContinuationCompileError {}

fn order_covers_layer(order: &[TermId], terms: usize) -> bool {
    if order.len() != terms {
        return false;
    }
    let mut seen = vec![false; terms];
    order.iter().all(|id| match seen.get_mut(id.0 as usize) {
        Some(slot) if !*slot => {
            *slot = true;
            true
        }
        _ => false,
    })
}

fn projection_count(layer: &CoeffLayer) -> usize {
    let mut projections = BTreeSet::<ProjectionId>::new();
    for term in &layer.terms {
        term.for_each_projection_use(|projection| {
            projections.insert(projection);
        });
    }
    projections.len()
}

fn require(
    layer: usize,
    resource: &'static str,
    required: usize,
    maximum: usize,
) -> Result<(), ContinuationCompileError> {
    if required > maximum {
        return Err(ContinuationCompileError::Capacity {
            layer,
            resource,
            required,
            maximum,
        });
    }
    Ok(())
}

fn compile_layer(
    layer_index: usize,
    canonical: &gkr_eval_ir::DagLayer,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
    profile: &ContinuationResourceProfile,
) -> Result<ContinuationLayerProgram, ContinuationCompileError> {
    let distilled = distill(canonical, crate::BwdRegime::Ext, cross_fields);
    let (coefficients, trace) =
        lower_coeff_layer_traced(canonical, &distilled).map_err(|error| {
            ContinuationCompileError::Lower {
                layer: layer_index,
                error,
            }
        })?;
    require(
        layer_index,
        "fragment_atoms",
        trace.max_fragment_atoms,
        profile.max_fragment_atoms,
    )?;
    require(
        layer_index,
        "expansion_factor",
        trace.max_expansion_factor,
        profile.max_expansion_factor,
    )?;
    let coefficients =
        group_coeff_layer(coefficients).map_err(|error| ContinuationCompileError::Lower {
            layer: layer_index,
            error,
        })?;
    let atoms = order_atoms(&coefficients);
    let order = flatten_atoms(&coefficients, &atoms);
    if !order_covers_layer(&order, coefficients.terms.len()) {
        return Err(ContinuationCompileError::OrderCoverage { layer: layer_index });
    }
    let program = encode_program_atoms(&coefficients, &atoms).map_err(|error| {
        ContinuationCompileError::Codec {
            layer: layer_index,
            error,
        }
    })?;
    let binding = bind_lean_sources_with_limits(
        &coefficients,
        cross_fields,
        &order,
        PUBLICATION_DEPTH,
        profile.source_window_columns,
        profile.max_source_windows,
    )
    .map_err(|error| ContinuationCompileError::Bind {
        layer: layer_index,
        error,
    })?;
    validate_program(&program, &coefficients).map_err(|error| ContinuationCompileError::Codec {
        layer: layer_index,
        error,
    })?;

    for (resource, required, maximum) in [
        (
            "immediates",
            coefficients.immediates.len(),
            profile.max_immediates,
        ),
        (
            "coefficient_recipes",
            coefficients.coefficients.len(),
            profile.max_coefficient_recipes,
        ),
        ("sources", coefficients.sources.len(), profile.max_sources),
        (
            "projections",
            projection_count(&coefficients),
            profile.max_projections,
        ),
        ("records", program.words.len() / 4, profile.max_records),
        (
            "program_words",
            program.words.len(),
            profile.max_program_words,
        ),
    ] {
        require(layer_index, resource, required, maximum)?;
    }

    Ok(ContinuationLayerProgram {
        layer: layer_index,
        coefficients,
        order: order.into_iter().map(|id| id.0).collect(),
        program,
        binding,
    })
}

pub fn compile_continuations(
    dag: &DagCircuit,
    profile: &GpuResourceProfile,
) -> Result<ContinuationProgramBundle, ContinuationCompileError> {
    validate_continuation_profile(&profile.continuations)
        .map_err(ContinuationCompileError::Profile)?;
    let cross_fields = build_cross_layer_field_map(dag);
    let layers = dag
        .layers
        .iter()
        .enumerate()
        .map(|(layer, canonical)| {
            compile_layer(layer, canonical, &cross_fields, &profile.continuations)
        })
        .collect::<Result<_, _>>()?;
    Ok(ContinuationProgramBundle { layers })
}

pub fn interpret_continuation_program(
    program: &ContinuationLayerProgram,
    row: usize,
    resolver: &impl CoeffResolver,
    k: usize,
) -> Result<(gkr_eval_ir::Ext, gkr_eval_ir::Ext), LeanInterpError> {
    interpret_lean_program(&program.program, &program.coefficients, row, resolver, k)
}
