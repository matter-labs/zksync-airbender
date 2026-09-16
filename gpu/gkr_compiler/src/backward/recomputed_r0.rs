//! MAIN R0 endpoint recomputation from input expressions. Products contribute
//! both Boolean and infinity cells; these programs require the recomputed executor.
use super::window::{
    lower_recomputed_window_program, reorder_recomputed_window_boundaries, WindowLoweringError,
    WindowShape, WINDOW_PROGRAM_WORD_CAP,
};
use super::{R0CompileError, WindowProgram};
use gkr_eval_ir::DagCircuit;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RecomputedKernel {
    Recomputed3,
    Unit4,
    Tails4,
}

impl RecomputedKernel {
    pub fn shape_mask(self) -> u16 {
        match self {
            Self::Recomputed3 => 0x7f7,
            Self::Unit4 => 0x771,
            Self::Tails4 => 0x7ff,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecomputedR0Layer {
    pub window: WindowProgram,
    /// Index into the window coefficient bank, or None for zero.
    pub scalar_seed: Option<u16>,
    pub kernel: RecomputedKernel,
    #[cfg(test)]
    pub coefficients: super::CoeffLayer,
}

pub fn compile_recomputed_r0(dag: &DagCircuit) -> Result<Vec<RecomputedR0Layer>, R0CompileError> {
    let fields = crate::analysis::build_cross_layer_field_map(dag);
    dag.layers
        .iter()
        .enumerate()
        .map(|(layer, canonical)| {
            let program = super::r0::compile_layer(layer, canonical, &fields)?;
            let lower = |tails| {
                lower_recomputed_window_program(&program, tails)
                    .map_err(|error| R0CompileError::Window { layer, error })
            };
            let (mut window, mut scalar_seed) = lower(false)?;
            // Grouping changes the BF/E4 record counts, so select the launch bound first.
            let sections = window.sections;
            let bf_heavy = u64::from(sections[0]) > 4 * u64::from(sections[3] - sections[0]);
            let kernel = if !bf_heavy {
                RecomputedKernel::Recomputed3
            } else if window.shape.bits() & !RecomputedKernel::Unit4.shape_mask() == 0 {
                RecomputedKernel::Unit4
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
                RecomputedKernel::Tails4
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
            reorder_recomputed_window_boundaries(&mut window);
            Ok(RecomputedR0Layer {
                window,
                scalar_seed,
                kernel,
                #[cfg(test)]
                coefficients: program.coefficients,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests;
