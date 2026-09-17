//! MAIN R0 endpoint recomputation from input expressions.

use std::collections::HashMap;

use gkr_eval_ir::{DagCircuit, FieldKind, ReadPlace};

use super::common::distill::distill;
use super::common::lean_bind::{bind_lean_sources, LeanBindError, LeanSourceBinding};
use super::common::limits::{LEAN_MAX_COEFFICIENT_RECIPES, LEAN_MAX_SOURCES};
use super::common::model::{CoeffError, CoeffLayer};
use super::common::order::order_terms;
use super::window::{
    lower_r0_window_program, reorder_r0_window_boundaries, WindowLoweringError, WindowShape,
    WINDOW_PROGRAM_WORD_CAP,
};
use super::WindowProgram;
use crate::analysis::build_cross_layer_field_map;

pub(super) struct BoundR0Layer {
    pub layer: usize,
    pub binding: LeanSourceBinding,
    pub coefficients: CoeffLayer,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R0CompileError {
    Window {
        layer: usize,
        error: super::window::WindowLoweringError,
    },
    Lower {
        layer: usize,
        error: CoeffError,
    },
    Bind {
        layer: usize,
        error: LeanBindError,
    },
    Capacity {
        layer: usize,
        resource: &'static str,
        required: usize,
        maximum: usize,
    },
}

impl core::fmt::Display for R0CompileError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for R0CompileError {}

fn compile_layer(
    layer_index: usize,
    canonical: &gkr_eval_ir::DagLayer,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
) -> Result<BoundR0Layer, R0CompileError> {
    let distilled = distill(canonical, crate::BwdRegime::R0, cross_fields);
    let coefficients =
        super::common::lower::lower_coeff_layer(canonical, &distilled).map_err(|error| {
            R0CompileError::Lower {
                layer: layer_index,
                error,
            }
        })?;
    let order = order_terms(&coefficients);
    let binding = bind_lean_sources(&coefficients, cross_fields, &order).map_err(|error| {
        R0CompileError::Bind {
            layer: layer_index,
            error,
        }
    })?;
    for (resource, required, maximum) in [
        (
            "coefficient_recipes",
            coefficients.coefficients.len(),
            LEAN_MAX_COEFFICIENT_RECIPES,
        ),
        ("sources", coefficients.sources.len(), LEAN_MAX_SOURCES),
    ] {
        if required > maximum {
            return Err(R0CompileError::Capacity {
                layer: layer_index,
                resource,
                required,
                maximum,
            });
        }
    }

    Ok(BoundR0Layer {
        layer: layer_index,
        binding,
        coefficients,
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum R0Kernel {
    General3,
    Unit4,
    Tails4,
}

impl R0Kernel {
    pub fn shape_mask(self) -> u16 {
        match self {
            Self::General3 => 0x7f7,
            Self::Unit4 => 0x771,
            Self::Tails4 => 0x7ff,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct R0WindowProgram {
    pub window: WindowProgram,
    /// Index into the window coefficient bank, or None for zero.
    pub scalar_seed: Option<u16>,
    pub kernel: R0Kernel,
    pub partition_candidates: super::window::partition::policy::R0PartitionCandidates,
    #[cfg(test)]
    pub coefficients: super::CoeffLayer,
}

pub fn compile_r0(dag: &DagCircuit) -> Result<Vec<R0WindowProgram>, R0CompileError> {
    let fields = build_cross_layer_field_map(dag);
    dag.layers
        .iter()
        .enumerate()
        .map(|(layer, canonical)| {
            let program = compile_layer(layer, canonical, &fields)?;
            let lower = |tails| {
                lower_r0_window_program(&program, tails)
                    .map_err(|error| R0CompileError::Window { layer, error })
            };
            let (mut window, mut scalar_seed) = lower(false)?;
            // Grouping changes the BF/E4 record counts, so select the launch bound first.
            let sections = window.sections;
            let bf_heavy = u64::from(sections[0]) > 4 * u64::from(sections[3] - sections[0]);
            let kernel = if !bf_heavy {
                R0Kernel::General3
            } else if window.shape.bits() & !R0Kernel::Unit4.shape_mask() == 0 {
                R0Kernel::Unit4
            } else {
                (window, scalar_seed) = lower(true)?;
                if !window.shape.contains(WindowShape::BF_LINEAR_TAIL) {
                    return Err(R0CompileError::Window {
                        layer,
                        error: WindowLoweringError::Encoding(format!(
                            "unsupported BF-heavy shape {:#x}",
                            window.shape.bits()
                        )),
                    });
                }
                R0Kernel::Tails4
            };
            if window.shape.bits() & !kernel.shape_mask() != 0 {
                return Err(R0CompileError::Window {
                    layer,
                    error: WindowLoweringError::Encoding(format!(
                        "shape {:#x} is unsupported by {kernel:?}",
                        window.shape.bits()
                    )),
                });
            }
            if window.words.len() > WINDOW_PROGRAM_WORD_CAP {
                return Err(R0CompileError::Capacity {
                    layer,
                    resource: "window program words",
                    required: window.words.len(),
                    maximum: WINDOW_PROGRAM_WORD_CAP,
                });
            }
            reorder_r0_window_boundaries(&mut window);
            let partition_candidates =
                super::window::partition::policy::R0PartitionCandidates::new(&window)
                    .map_err(|error| R0CompileError::Window { layer, error })?;
            Ok(R0WindowProgram {
                window,
                scalar_seed,
                kernel,
                partition_candidates,
                #[cfg(test)]
                coefficients: program.coefficients,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests;
