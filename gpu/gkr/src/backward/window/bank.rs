//! Binds window coefficient banks and final publications.

use gpu_gkr_compiler::WindowFamily;

use crate::{
    backward::{record_active_eq_slot_fold, GkrEqSizes},
    upstream::{GKRAddress, ReadPlace, VirtualSetupKind, VirtualSetupPoly},
};

pub(crate) fn family_read_place(family: WindowFamily, column: usize) -> Option<ReadPlace> {
    match family {
        WindowFamily::BaseLayerMemory => Some(ReadPlace::BaseLayerMemory { column }),
        WindowFamily::BaseLayerWitness => Some(ReadPlace::BaseLayerWitness { column }),
        WindowFamily::Setup => Some(ReadPlace::Setup { column }),
        WindowFamily::Scratch => Some(ReadPlace::Scratch { slot: column }),
        WindowFamily::LayerOutput { layer, .. } => Some(ReadPlace::LayerOutput {
            layer,
            offset: column,
        }),
        WindowFamily::CacheOutput { layer, .. } => Some(ReadPlace::CacheOutput {
            layer,
            offset: column,
        }),
        WindowFamily::VirtualSetup { .. } => None,
    }
}

pub(crate) fn virtual_setup_poly_address(kind: VirtualSetupKind) -> GKRAddress {
    GKRAddress::VirtualSetup(match kind {
        VirtualSetupKind::RangeCheck16Bits => VirtualSetupPoly::RangeCheck16Bits,
        VirtualSetupKind::RangeCheckTimestamp => VirtualSetupPoly::RangeCheckTimestamp,
        VirtualSetupKind::InitsAndTeardownsLow => VirtualSetupPoly::InitsAndTeardownsLow,
        VirtualSetupKind::InitsAndTeardownsHigh => VirtualSetupPoly::InitsAndTeardownsHigh,
    })
}

pub(crate) fn drained_eq_sizes(mut eq_sizes: GkrEqSizes, rounds: u8) -> GkrEqSizes {
    for _ in 0..rounds {
        record_active_eq_slot_fold(&mut eq_sizes);
    }
    eq_sizes
}
