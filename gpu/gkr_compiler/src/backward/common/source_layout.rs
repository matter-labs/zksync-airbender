use std::collections::HashMap;

use gkr_eval_ir::{read_place_field, FieldKind, ReadPlace, VirtualSetupKind};

use super::model::CoeffSource;
use super::source::OriginLeaf;

/// Logical backing identity used by the backward source-window binder.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum WindowFamily {
    BaseLayerMemory,
    BaseLayerWitness,
    Setup,
    Scratch,
    LayerOutput { layer: usize, ext: bool },
    CacheOutput { layer: usize, ext: bool },
    VirtualSetup { kind: u8 },
}

fn virtual_setup_tag(kind: &VirtualSetupKind) -> u8 {
    match kind {
        VirtualSetupKind::RangeCheck16Bits => 0,
        VirtualSetupKind::RangeCheckTimestamp => 1,
        VirtualSetupKind::InitsAndTeardownsLow => 2,
        VirtualSetupKind::InitsAndTeardownsHigh => 3,
    }
}

fn backing_field(
    place: &ReadPlace,
    source: &CoeffSource,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
) -> FieldKind {
    read_place_field(place)
        .or_else(|| cross_fields.get(place).copied())
        .unwrap_or(source.field)
}

pub(crate) fn window_family(
    source: &CoeffSource,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
) -> (WindowFamily, usize) {
    match &source.origin {
        OriginLeaf::VirtualSetup { kind } => (
            WindowFamily::VirtualSetup {
                kind: virtual_setup_tag(kind),
            },
            0,
        ),
        OriginLeaf::Read(place) => {
            let ext = backing_field(place, source, cross_fields) == FieldKind::Ext;
            match *place {
                ReadPlace::BaseLayerMemory { column } => (WindowFamily::BaseLayerMemory, column),
                ReadPlace::BaseLayerWitness { column } => (WindowFamily::BaseLayerWitness, column),
                ReadPlace::Setup { column } => (WindowFamily::Setup, column),
                ReadPlace::Scratch { slot } => (WindowFamily::Scratch, slot),
                ReadPlace::LayerOutput { layer, offset } => {
                    (WindowFamily::LayerOutput { layer, ext }, offset)
                }
                ReadPlace::CacheOutput { layer, offset } => {
                    (WindowFamily::CacheOutput { layer, ext }, offset)
                }
            }
        }
    }
}
