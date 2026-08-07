use crate::programs::GkrPrograms;
use crate::setup::GpuGKRForwardSetup;
use crate::stage1::GpuGKRStage1Output;
use gkr_eval_ir::RangeWidth;
use gpu_gkr_compiler::ForwardSpecialStrategy;

#[derive(Clone, Copy, Default)]
pub(super) struct ForwardLookupUsage {
    pub(super) last_generic_mapping_layer: Option<usize>,
    pub(super) last_range_mapping_layer: Option<usize>,
    pub(super) last_timestamp_mapping_layer: Option<usize>,
    pub(super) last_generic_lookup_layer: Option<usize>,
}

pub(super) fn analyze_forward_lookup_usage(programs: &GkrPrograms) -> ForwardLookupUsage {
    let mut usage = ForwardLookupUsage::default();
    for (layer_idx, layer) in programs.forward.layers.iter().enumerate() {
        for descriptor in layer.specials.iter() {
            match descriptor {
                ForwardSpecialStrategy::PeekSingleColumn { width, .. } => {
                    if *width == RangeWidth::Bits16 {
                        usage.last_range_mapping_layer = Some(layer_idx);
                    } else {
                        usage.last_timestamp_mapping_layer = Some(layer_idx);
                    }
                }
                ForwardSpecialStrategy::PeekAggregate { .. }
                | ForwardSpecialStrategy::PeekDecoder { .. } => {
                    usage.last_generic_mapping_layer = Some(layer_idx);
                    usage.last_generic_lookup_layer = Some(layer_idx);
                }
                ForwardSpecialStrategy::PeekSetup => {
                    usage.last_generic_lookup_layer = Some(layer_idx);
                }
                ForwardSpecialStrategy::VirtualSetup { .. }
                | ForwardSpecialStrategy::InitsAndTeardownsTopBits { .. } => {}
            }
        }
    }
    usage
}

pub(super) fn release_forward_lookup_resources_after_layer(
    layer_idx: usize,
    usage: &ForwardLookupUsage,
    stage1: &mut GpuGKRStage1Output,
    forward_setup: &mut GpuGKRForwardSetup,
) {
    if usage.last_generic_mapping_layer == Some(layer_idx) {
        stage1.lookup_mappings.release_generic_family();
    }
    if usage.last_range_mapping_layer == Some(layer_idx) {
        stage1.lookup_mappings.release_range_check_16();
    }
    if usage.last_timestamp_mapping_layer == Some(layer_idx) {
        stage1.lookup_mappings.release_timestamp();
    }
    if usage.last_generic_lookup_layer == Some(layer_idx) {
        forward_setup.release_generic_lookup();
    }
}
