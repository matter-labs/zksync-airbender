pub(crate) mod sumcheck_plan;

use std::collections::VecDeque;
use std::sync::Arc;

use gpu_core::primitives::device_tracing::Range;

use super::GpuGKRDimensionReducingBackwardStatePr;
use crate::gkr_address_audit::AddressClass;
use crate::proth120::programs::GkrProgramsPr;
use crate::proth120::proof_layout::ProofLayoutPr;
use crate::upstream::{GKRAddress, PR};
use crate::GpuGKRStorage;

pub(crate) struct MainLayerBackwardStatePr {
    pub(crate) forward_tracing_ranges: Vec<Range>,
    pub(crate) storage: GpuGKRStorage<PR, PR>,
    pub(crate) pending_layers: VecDeque<usize>,
    pub(crate) trace_len: usize,
    pub(crate) programs: Arc<GkrProgramsPr>,
    pub(crate) scratch_last_reader: Option<usize>,
}

pub(crate) fn scratch_last_reader_layer(
    programs: &GkrProgramsPr,
    layout: &ProofLayoutPr,
) -> Option<usize> {
    let circuit = &programs.runtime_circuit;
    (0..circuit.layers.len())
        .filter(|&layer| {
            programs.backward_layers[layer]
                .inputs
                .iter()
                .any(|address| matches!(address, GKRAddress::ScratchSpace(_)))
                || layout
                    .backward_layers
                    .iter()
                    .find(|layout_layer| layout_layer.layer_idx == layer)
                    .is_some_and(|layout_layer| {
                        layout_layer
                            .extra_evaluations_addresses
                            .iter()
                            .any(|address| circuit.scratch_space_mapping.contains_key(address))
                    })
        })
        .min()
}

pub(crate) fn release_scratch_views(storage: &mut GpuGKRStorage<PR, PR>) {
    let Some(scratch) = storage.layers.first_mut().and_then(|layer| {
        layer
            .base_class_backings
            .remove(&AddressClass::ScratchSpace)
    }) else {
        return;
    };
    for layer in &mut storage.layers {
        layer
            .base_field_inputs
            .retain(|_, poly| !Arc::ptr_eq(&poly.backing, &scratch.backing));
    }
}

impl GpuGKRDimensionReducingBackwardStatePr {
    pub(crate) fn into_main_layer_backward_state_pr(
        self,
        inits_and_teardowns_top_bits: &[u32],
        programs: Arc<GkrProgramsPr>,
        layout: &ProofLayoutPr,
    ) -> MainLayerBackwardStatePr {
        assert!(
            self.pending_layers.is_empty(),
            "Proth120 main-layer handoff requires the dimension-reducing layers to be exhausted"
        );
        let circuit = &programs.runtime_circuit;
        assert_eq!(
            inits_and_teardowns_top_bits.len(),
            circuit.memory_layout.teardown_sets.len(),
            "Proth120 inits and teardowns top bits need one entry per teardown set"
        );
        let mut storage = self.storage;
        let scratch_last_reader = scratch_last_reader_layer(&programs, layout);
        if scratch_last_reader.is_none() {
            release_scratch_views(&mut storage);
        }
        MainLayerBackwardStatePr {
            forward_tracing_ranges: self.forward_tracing_ranges,
            storage,
            pending_layers: (0..circuit.layers.len()).rev().collect(),
            trace_len: circuit.trace_len,
            programs: Arc::clone(&programs),
            scratch_last_reader,
        }
    }
}
