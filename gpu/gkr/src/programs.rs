//! Per-circuit symbolic programs used by the GPU GKR interpreters.
//!
//! Forward search is deliberately absent from this module. The searched
//! schedules are committed artifacts embedded in the binary; initialization
//! only lowers the circuit, rejects an artifact mismatch, and compiles the
//! forward, R0, and continuation programs once.

use std::{collections::BTreeMap, sync::Arc};

use gpu_gkr_compiler::{
    ContinuationProgramBundle, DrWindowInputProjection, DrWindowProgram, WindowFamily,
};

use crate::upstream::{GKRAddress, VirtualSetupPoly};

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

pub(crate) fn bound_window_address(family: WindowFamily, column: usize) -> GKRAddress {
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
    pub(crate) layers: BTreeMap<usize, Arc<DrWindowLayerProgram>>,
}

impl DrWindowProgramBundle {
    pub fn layer(&self, dr_layer: usize) -> Option<&Arc<DrWindowLayerProgram>> {
        self.layers.get(&dr_layer)
    }
}
