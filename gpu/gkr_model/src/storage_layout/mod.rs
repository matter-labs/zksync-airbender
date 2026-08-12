//! CPU-only storage layout for the GKR backward path.
//!
//! Walks a `cs::gkr_compiler::GKRCircuitArtifact` and produces, per storage
//! layer, a deterministic `(slot, FieldType, poly_idx)` mapping for every
//! `GKRAddress` that has a poly *living* at that layer. The 8-slot taxonomy
//! is shared with `gkr_address_audit`:
//!
//! - slots 0..2 are layer-0 read sources (BaseLayerWitness, BaseLayerMemory,
//!   Setup + VirtualSetup) and are externally backed by trace holders.
//! - slots 5..6 are this-layer write targets (Cached and InnerLayer) and are
//!   the freshly-allocated consolidated backings.
//! - slot 7 is layer-0 ScratchSpace, externally backed by `stage1`.
//! - slots 3..4 are kernel-side aliases for prev-layer slots 5/6 — never
//!   populated in the storage layout.
//!
//! The layout is the data structure every compact-`u16` descriptor builder
//! consults to encode `(ptr_idx, poly_idx)` against the per-launch pointer
//! table.
//!
//! Submodules split by concern: [`types`] (the data model), [`construct`]
//! (build from an artifact), [`alias`] (`CopyIn*Field` alias resolution),
//! [`tower`] (dim-reducing tower layers), [`fixtures`] (hand-crafted
//! test-support layout). This file is the facade: it keeps
//! `storage_layout::{FieldType, StorageSlot, GpuGKRLayerLayout,
//! GpuGKRStorageLayout, address_storage_layer, handcrafted_layout}` public
//! paths stable for `gpu_circuit_prover`'s `gkr` facade re-export.

mod alias;
mod construct;
mod fixtures;
mod tower;
mod types;

pub use construct::address_storage_layer;
pub use types::{FieldType, GpuGKRLayerLayout, GpuGKRStorageLayout, StorageSlot};

#[doc(hidden)]
pub use fixtures::handcrafted_layout;

#[cfg(test)]
mod tests;
