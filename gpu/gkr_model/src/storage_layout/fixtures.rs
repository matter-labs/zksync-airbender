//! Test-support layout construction consumed by `gpu_circuit_prover`'s
//! GPU-storage integration tests (no CUDA / real artifact required here).

use std::collections::BTreeMap;

use crate::address_audit::AddressClass;
use crate::upstream::GKRAddress;

use super::types::{FieldType, GpuGKRLayerLayout, GpuGKRStorageLayout, StorageSlot};

/// Builds a small hand-crafted layout: layer 0 holds 2 base polys (slot
/// `ThisLayerInnerLayerWrite`) + 2 ext polys (slot `ThisLayerCachedWrite`),
/// trace_len 4. Exposed (`#[doc(hidden)]`) only so `gpu_circuit_prover`'s GPU-storage
/// integration tests can build a deterministic layout without a real artifact.
#[doc(hidden)]
pub fn handcrafted_layout(
    base_addr_a: GKRAddress,
    base_addr_b: GKRAddress,
    ext_addr_a: GKRAddress,
    ext_addr_b: GKRAddress,
) -> GpuGKRStorageLayout {
    let trace_len = 4usize;
    let log2_stride = trace_len.trailing_zeros();
    let mut index = BTreeMap::new();
    index.insert(
        base_addr_a,
        (
            AddressClass::ThisLayerInnerLayerWrite,
            FieldType::Base,
            0u32,
        ),
    );
    index.insert(
        base_addr_b,
        (
            AddressClass::ThisLayerInnerLayerWrite,
            FieldType::Base,
            1u32,
        ),
    );
    index.insert(
        ext_addr_a,
        (AddressClass::ThisLayerCachedWrite, FieldType::Ext, 0u32),
    );
    index.insert(
        ext_addr_b,
        (AddressClass::ThisLayerCachedWrite, FieldType::Ext, 1u32),
    );
    let mut slot_poly_counts = BTreeMap::new();
    slot_poly_counts.insert(
        StorageSlot {
            class: AddressClass::ThisLayerInnerLayerWrite,
            field: FieldType::Base,
        },
        2u32,
    );
    slot_poly_counts.insert(
        StorageSlot {
            class: AddressClass::ThisLayerCachedWrite,
            field: FieldType::Ext,
        },
        2u32,
    );
    GpuGKRStorageLayout {
        trace_len,
        artifact_log2_stride: log2_stride,
        layers: vec![GpuGKRLayerLayout {
            index,
            slot_poly_counts,
            log2_stride,
        }],
        aliases: BTreeMap::new(),
        scratch_space_mapping_rev: BTreeMap::new(),
    }
}
