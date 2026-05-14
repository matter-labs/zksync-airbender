use std::collections::BTreeMap;
use std::ptr::null;
use std::sync::Arc;

use era_cudart::result::CudaResult;

use super::gkr_address_audit::AddressClass;
use super::storage_layout::FieldType;
#[cfg(test)]
use super::tests::{
    alloc_device_and_schedule_upload, alloc_host_and_schedule_copy,
    GpuSumcheckRound0DeviceLaunchDescriptors, GpuSumcheckRound0HostLaunchDescriptors,
    GpuSumcheckRound0ScheduledLaunchDescriptors,
};
use super::{
    ConsolidatedBaseFoldingBacking, ConsolidatedFoldingBacking,
    GpuBaseFieldPolyIntermediateFoldingStorage, GpuBaseFieldPolySource,
    GpuBaseFieldPolySourceAfterOneFoldingPlan, GpuBaseFieldPolySourceAfterTwoFoldingsPlan,
    GpuBaseFieldSourceKind, GpuExtensionFieldPolyContinuingSourcePlan,
    GpuExtensionFieldPolyInitialSource, GpuExtensionFieldPolyIntermediateFoldingStorage,
    GpuGKRStorage, GpuSumcheckRound0LaunchDescriptors, GpuSumcheckRound1PreparedStorage,
    GpuSumcheckRound2PreparedStorage, GpuSumcheckRound3AndBeyondPreparedStorage,
};
use crate::allocator::tracker::AllocationPlacement;
#[cfg(test)]
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, ProverContext};
use crate::upstream::{Field, GKRAddress, GKRInputs};

impl<B: 'static, E: Field> GpuGKRStorage<B, E> {
    /// Pre-allocate the per-(layer, AddressClass) ext-intermediate-folding
    /// backings for a layer. Called once per layer at the start of
    /// dim-reducing prep, before any `prepare_for_sumcheck_round_*` call.
    ///
    /// `addresses` is the set of `GKRAddress`es that will be passed as
    /// `inputs_in_extension` to dim-reducing rounds at this layer (union over
    /// all blueprints, placeholders excluded). The storage layout
    /// (`Self::layout`) determines each address's `(class, poly_idx)`; this
    /// method allocates one Arc per class, sized = `class_poly_count *
    /// per_poly_size`, and the poly's offset within its class's Arc is
    /// `poly_idx * per_poly_size` — aligned with `ext_class_backings` so a u16
    /// source descriptor's poly_idx round-trips between the two for the
    /// round-1 dual-source-record cache half.
    ///
    /// Tower layers are covered via `from_artifact_with_tower`, so the
    /// caller can rely on every dim-reducing input address (artifact or tower)
    /// resolving through the layout. The only no-op path is "no layout set",
    /// which is restricted to test code.
    pub(crate) fn register_dim_reducing_inputs_for_layer(
        &mut self,
        layer: usize,
        addresses: &std::collections::BTreeSet<GKRAddress>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        if addresses.is_empty() {
            return Ok(());
        }
        let layout = match self.layout.as_ref() {
            Some(l) => l.clone(),
            None => return Ok(()),
        };
        let n_layers = self.layers.len();
        let layer_storage = self.layers.get_mut(layer).unwrap_or_else(|| {
            panic!(
                "register_dim_reducing_inputs_for_layer called for layer {layer} but storage has only {n_layers} layers"
            )
        });
        if layer_storage.intermediate_folding_consolidated.is_some() {
            // Single call site (`prepare_layer_from_blueprints`) — bail loudly
            // on a second call rather than silently merging or reallocating.
            panic!(
                "register_dim_reducing_inputs_for_layer called twice for layer {layer}; the prep flow must call it exactly once per layer",
            );
        }

        // Group addresses by class via the storage layout, validate uniform
        // per-poly size, and confirm all are ext-typed.
        let mut addrs_by_class: BTreeMap<AddressClass, Vec<GKRAddress>> = BTreeMap::new();
        let mut per_poly_size: Option<usize> = None;
        for addr in addresses.iter() {
            let (_canonical_layer, class, field, _poly_idx) =
                layout.lookup(layer, addr).unwrap_or_else(|| {
                    panic!(
                        "dim-reducing input {addr:?} missing from storage layout at layer {layer}"
                    )
                });
            assert_eq!(
                field,
                FieldType::Ext,
                "dim-reducing input {addr:?} must be ext-typed (got {field:?})",
            );
            addrs_by_class.entry(class).or_default().push(*addr);
            let len = layer_storage
                .extension_field_inputs
                .get(addr)
                .unwrap_or_else(|| {
                    panic!("dim-reducing input {addr:?} missing from ext storage at layer {layer}")
                })
                .len();
            match per_poly_size {
                None => per_poly_size = Some(len),
                Some(p) => assert_eq!(
                    len, p,
                    "dim-reducing inputs at layer {layer} have non-uniform sizes (first={p}, {addr:?}={len}); consolidation requires uniform per-poly size",
                ),
            }
        }
        let per_poly_size = per_poly_size.expect("non-empty addresses verified above");
        assert!(
            per_poly_size.is_power_of_two() && per_poly_size > 2,
            "per_poly_size {per_poly_size} must be a power of two greater than 2"
        );

        // Allocate one backing per class, sized to mirror ext_class_backings'
        // capacity for that class. poly_idx within the backing is the same as
        // the layout's per-class poly_idx — wasted slots for non-dim-reducing
        // polys are bounded by the audit's GKR_MAX_POLYS_PER_SLOT ceiling.
        let mut per_class = BTreeMap::new();
        let mut poly_index = BTreeMap::new();
        for (class, addrs) in addrs_by_class {
            let count = addrs.len();
            assert!(
                count > 0,
                "class {class:?} ext poly count must be positive at layer {layer}"
            );
            let total_size = count * per_poly_size;
            let backing = Arc::new(context.alloc::<E>(total_size, AllocationPlacement::Top)?);
            per_class.insert(class, backing);
            for (idx, addr) in addrs.into_iter().enumerate() {
                assert!(
                    idx <= u16::MAX as usize,
                    "ext cache poly index {idx} exceeds u16"
                );
                poly_index.insert(addr, idx as u16);
            }
        }
        layer_storage.intermediate_folding_consolidated = Some(ConsolidatedFoldingBacking {
            per_class,
            poly_index,
            per_poly_size,
        });
        Ok(())
    }

    /// Pre-allocate per-(layer, AddressClass) consolidated folding backings
    /// for the main-layer flat path's base-field input set. Mirrors
    /// `register_dim_reducing_inputs_for_layer` but operates on base-field
    /// addresses.
    ///
    /// `addresses` includes both real and virtual base-field inputs. Real
    /// inputs route through the layout's per-class index. `VirtualSetup`
    /// polys have no layout slot — they get a separate per-class Arc
    /// (`virtual_per_class`), with a deterministic poly_idx assignment
    /// (`virtual_index`). After this call, every base address in the set
    /// has a consolidated cache slot pre-allocated; subsequent
    /// `materialize_base_folding_buffer` calls slice views into it.
    pub(crate) fn register_flat_base_folding_for_layer(
        &mut self,
        layer: usize,
        addresses: &std::collections::BTreeSet<GKRAddress>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        if addresses.is_empty() {
            return Ok(());
        }
        let layout = match self.layout.as_ref() {
            Some(l) => l.clone(),
            None => return Ok(()),
        };
        let n_layers = self.layers.len();
        if !(layer < n_layers) {
            panic!(
                "register_flat_base_folding_for_layer called for layer {layer} but storage has only {n_layers} layers"
            );
        }
        if self.layers[layer]
            .intermediate_base_folding_consolidated
            .is_some()
        {
            // Single call site (`prepare_layer_from_blueprints`) — bail loudly
            // on a second call rather than silently merging or reallocating.
            panic!(
                "register_flat_base_folding_for_layer called twice for layer {layer}; the prep flow must call it exactly once per layer",
            );
        }

        // Walk addresses, splitting into real (layout-indexed) and virtual
        // (`VirtualSetup`) sets. Validate uniform per-poly size for real polys
        // (they're tracked in `base_field_inputs` at the address's canonical
        // storage layer — for `ScratchSpace`, that is layer 0, not the
        // requesting `layer`); for virtuals, fall back to the layer's
        // `base_trace_len` proxy since they have no real backing.
        let mut addrs_by_class: BTreeMap<AddressClass, Vec<GKRAddress>> = BTreeMap::new();
        let mut per_poly_size: Option<usize> = None;
        let mut virtuals_by_class: BTreeMap<AddressClass, Vec<GKRAddress>> = BTreeMap::new();
        for addr in addresses.iter() {
            if matches!(addr, GKRAddress::VirtualSetup(_)) {
                let class = match addr {
                    GKRAddress::VirtualSetup(_) => AddressClass::Setup,
                    _ => unreachable!(),
                };
                virtuals_by_class.entry(class).or_default().push(*addr);
                continue;
            }
            let (_canonical_layer, class, field, _poly_idx) = layout
                .lookup(layer, addr)
                .unwrap_or_else(|| {
                    panic!(
                        "flat base-folding input {addr:?} missing from storage layout at layer {layer}"
                    )
                });
            assert_eq!(
                field,
                FieldType::Base,
                "flat base-folding input {addr:?} must be base-typed (got {field:?})",
            );
            addrs_by_class.entry(class).or_default().push(*addr);
            // Look up size at the address's canonical storage layer. For
            // base-field addresses whose canonical layer differs from
            // `layer` (e.g. `ScratchSpace(K)` whose poly lives at layer 0
            // but is consumed by a kernel at layer L > 0), the per-poly
            // size is the same as the requesting layer's polys (uniform
            // hypercube length), but it is only registered in the
            // canonical layer's `base_field_inputs`.
            let storage_layer = match addr {
                GKRAddress::BaseLayerWitness(_)
                | GKRAddress::BaseLayerMemory(_)
                | GKRAddress::Setup(_)
                | GKRAddress::ScratchSpace(_) => 0usize,
                GKRAddress::Cached { layer, .. } | GKRAddress::InnerLayer { layer, .. } => *layer,
                _ => layer,
            };
            let storage_layer = if self.layers.get(storage_layer).is_some() {
                storage_layer
            } else {
                layer
            };
            let len = self
                .layers
                .get(storage_layer)
                .and_then(|s| s.base_field_inputs.get(addr))
                .or_else(|| self.layers[layer].base_field_inputs.get(addr))
                .unwrap_or_else(|| {
                    panic!(
                        "flat base-folding input {addr:?} missing from base storage at layer {layer} (also checked canonical layer {storage_layer})"
                    )
                })
                .len();
            match per_poly_size {
                None => per_poly_size = Some(len),
                Some(p) => assert_eq!(
                    len, p,
                    "flat base-folding inputs at layer {layer} have non-uniform sizes (first={p}, {addr:?}={len}); consolidation requires uniform per-poly size",
                ),
            }
        }
        // If only virtuals were present we still need a per-poly size; use
        // `base_trace_len` (matches the per-poly path's allocation).
        let base_poly_size = match per_poly_size {
            Some(p) => p,
            None => self.base_trace_len(),
        };
        assert!(
            base_poly_size.is_power_of_two() && base_poly_size > 4,
            "base_poly_size {base_poly_size} must be a power of two greater than 4"
        );
        let cache_per_poly_size = base_poly_size / 2;

        let layer_storage = self.layers.get_mut(layer).expect("checked above");

        // Real-poly backings: one Arc per class, sized to the layout's class
        // count. poly_idx within the Arc matches the layout's per-class
        // poly_idx (mirrors `base_class_backings`), so the kernel-side
        // resolver can recover both the read source and the cache view
        // through the same index value.
        let mut per_class = BTreeMap::new();
        let mut real_index = BTreeMap::new();
        for (class, addrs) in addrs_by_class {
            let count = addrs.len();
            assert!(
                count > 0,
                "class {class:?} base poly count must be positive at layer {layer}"
            );
            let total_size = count * cache_per_poly_size;
            let backing = Arc::new(context.alloc::<E>(total_size, AllocationPlacement::Top)?);
            per_class.insert(class, backing);
            for (idx, addr) in addrs.into_iter().enumerate() {
                assert!(
                    idx <= u16::MAX as usize,
                    "base cache poly index {idx} exceeds u16"
                );
                real_index.insert(addr, idx as u16);
            }
        }

        // Virtual-poly backings: one Arc per class with virtuals, sized to
        // the count of distinct virtual addresses at that class. Sequential
        // poly_idx per class.
        let mut virtual_per_class: BTreeMap<AddressClass, Arc<DeviceAllocation<E>>> =
            BTreeMap::new();
        let mut virtual_index: BTreeMap<GKRAddress, u16> = BTreeMap::new();
        for (class, addrs) in virtuals_by_class {
            let count = addrs.len();
            let total_size = count * cache_per_poly_size;
            let backing = Arc::new(context.alloc::<E>(total_size, AllocationPlacement::Top)?);
            virtual_per_class.insert(class, backing);
            for (idx, addr) in addrs.into_iter().enumerate() {
                assert!(
                    idx <= u16::MAX as usize,
                    "virtual poly index {idx} exceeds u16 range",
                );
                virtual_index.insert(addr, idx as u16);
            }
        }

        layer_storage.intermediate_base_folding_consolidated =
            Some(ConsolidatedBaseFoldingBacking {
                per_class,
                real_index,
                virtual_per_class,
                virtual_index,
                per_poly_size: cache_per_poly_size,
            });
        Ok(())
    }

    fn round_input_layer(address: GKRAddress) -> usize {
        match address {
            GKRAddress::Cached { layer, .. } => layer,
            GKRAddress::InnerLayer { layer, .. } => layer,
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..)
            | GKRAddress::ScratchSpace(..) => 0,
        }
    }

    fn round_output_layer(address: GKRAddress) -> usize {
        match address {
            GKRAddress::BaseLayerMemory(..)
            | GKRAddress::BaseLayerWitness(..)
            | GKRAddress::Setup(..)
            | GKRAddress::VirtualSetup(..) => unreachable!(),
            GKRAddress::Cached { .. } => unreachable!(),
            // ScratchSpace outputs (e.g. rewritten MaxQuadratic outputs from
            // `transform::normalize_compiled_circuit_for_gpu`) live at layer 0
            // alongside trace columns.
            GKRAddress::ScratchSpace(..) => 0,
            GKRAddress::InnerLayer { layer, .. } => layer,
        }
    }

    /// Materialize the per-poly base-field folding buffer for `poly` at
    /// `layer`. Slices a view into the per-(layer, AddressClass) consolidated
    /// backing when `register_flat_base_folding_for_layer` has run for this
    /// layer. Layout-indexed (real) addresses use `per_class`;
    /// `VirtualSetup` polys use `virtual_per_class` keyed by
    /// `virtual_index[poly]`. Falls back to a fresh per-poly Arc if no
    /// consolidated backing exists for this layer (test-only path).
    fn materialize_base_folding_buffer(
        &self,
        layer: usize,
        poly: GKRAddress,
        base_poly_len: usize,
        context: &ProverContext,
    ) -> CudaResult<GpuBaseFieldPolyIntermediateFoldingStorage<E>> {
        if let Some(consolidated) = self.layers[layer]
            .intermediate_base_folding_consolidated
            .as_ref()
        {
            let cache_per_poly_size = base_poly_len / 2;
            assert_eq!(
                consolidated.per_poly_size, cache_per_poly_size,
                "consolidated base-folding backing per-poly size {} mismatches required cache size {} at layer {layer}",
                consolidated.per_poly_size, cache_per_poly_size,
            );
            // Real (layout-indexed) addresses route through `per_class`.
            if let Some(layout) = self.layout.as_ref() {
                if let Some((_canonical_layer, class, _field, _poly_idx_in_class)) =
                    layout.lookup(layer, &poly)
                {
                    if let Some(backing) = consolidated.per_class.get(&class) {
                        let cache_idx = consolidated.real_index.get(&poly).copied().unwrap_or_else(|| {
                            panic!(
                                "consolidated base-folding missing dense cache index for {poly:?} at layer {layer}"
                            )
                        });
                        let offset = cache_idx as usize * consolidated.per_poly_size;
                        return Ok(GpuBaseFieldPolyIntermediateFoldingStorage::from_arc(
                            Arc::clone(backing),
                            offset,
                            base_poly_len,
                        ));
                    }
                }
            }
            // Virtual addresses: look up the virtual poly_idx, then slice into
            // `virtual_per_class[class]`.
            if let Some(&virt_poly_idx) = consolidated.virtual_index.get(&poly) {
                let class = match poly {
                    GKRAddress::VirtualSetup(_) => AddressClass::Setup,
                    _ => panic!(
                        "consolidated base-folding virtual_index has non-VirtualSetup entry {poly:?} at layer {layer}"
                    ),
                };
                let backing = consolidated.virtual_per_class.get(&class).unwrap_or_else(|| {
                    panic!(
                        "consolidated base-folding has virtual_index for {poly:?} but no Arc for class {class:?} at layer {layer}"
                    )
                });
                let offset = virt_poly_idx as usize * consolidated.per_poly_size;
                return Ok(GpuBaseFieldPolyIntermediateFoldingStorage::from_arc(
                    Arc::clone(backing),
                    offset,
                    base_poly_len,
                ));
            }
            // Address not registered for consolidation at this layer (e.g.
            // a virtual poly that wasn't in the blueprint set passed to
            // `register_flat_base_folding_for_layer`). Fall through to the
            // per-poly lazy path. This shouldn't happen in production paths
            // — production callers pass the full input set to register —
            // but the test/unit paths still rely on it.
        }
        GpuBaseFieldPolyIntermediateFoldingStorage::new_for_base_poly_size(base_poly_len, context)
    }

    fn plan_base_source_for_round_1(
        &mut self,
        poly: GKRAddress,
        request_layer: usize,
        context: &ProverContext,
    ) -> CudaResult<GpuBaseFieldPolySourceAfterOneFoldingPlan<B, E>> {
        // Cache lives at the requesting sumcheck layer, NOT at the source
        // poly's canonical storage layer. For trace-holder / scratch
        // sources whose canonical layer is 0, the per-layer-L sumcheck
        // owns the intermediate folding buffer and registers it with
        // `register_flat_base_folding_for_layer` at layer L.
        let cache_layer = request_layer;
        let sumcheck_step = 1;
        let (base_poly_len, base_poly_ptr, source_kind) =
            if let Some(source_kind) = GpuBaseFieldSourceKind::from_address(poly) {
                (self.base_trace_len(), null(), source_kind)
            } else {
                let poly = self.get_base_poly_for_address(poly).expect("must exist");
                (poly.len(), poly.as_ptr(), GpuBaseFieldSourceKind::Real)
            };

        if !self.layers[cache_layer]
            .intermediate_storage_for_folder_base_field_inputs
            .contains_key(&poly)
        {
            let buffer =
                self.materialize_base_folding_buffer(cache_layer, poly, base_poly_len, context)?;
            self.layers[cache_layer]
                .intermediate_storage_for_folder_base_field_inputs
                .insert(poly, (0, buffer));
        }

        let (last_used_for_layer, buffer) = self.layers[cache_layer]
            .intermediate_storage_for_folder_base_field_inputs
            .get_mut(&poly)
            .expect("must be present");
        let this_layer_start = buffer.initial_pointer();
        let first_access = if *last_used_for_layer >= sumcheck_step {
            false
        } else {
            *last_used_for_layer = sumcheck_step;
            true
        };

        Ok(GpuBaseFieldPolySourceAfterOneFoldingPlan {
            base_layer_half_size: base_poly_len / 2,
            next_layer_size: base_poly_len / 4,
            base_input_start: base_poly_ptr,
            this_layer_cache_start: this_layer_start,
            first_access,
            source_kind,
        })
    }

    fn plan_base_source_for_round_2(
        &mut self,
        poly: GKRAddress,
        request_layer: usize,
        context: &ProverContext,
    ) -> CudaResult<GpuBaseFieldPolySourceAfterTwoFoldingsPlan<B, E>> {
        let cache_layer = request_layer;
        let sumcheck_step = 2;
        let (base_poly_len, base_poly_ptr, source_kind) =
            if let Some(source_kind) = GpuBaseFieldSourceKind::from_address(poly) {
                (self.base_trace_len(), null(), source_kind)
            } else {
                let poly = self.get_base_poly_for_address(poly).expect("must exist");
                (poly.len(), poly.as_ptr(), GpuBaseFieldSourceKind::Real)
            };

        if !self.layers[cache_layer]
            .intermediate_storage_for_folder_base_field_inputs
            .contains_key(&poly)
        {
            let buffer =
                self.materialize_base_folding_buffer(cache_layer, poly, base_poly_len, context)?;
            self.layers[cache_layer]
                .intermediate_storage_for_folder_base_field_inputs
                .insert(poly, (1, buffer));
        }

        let (last_used_for_layer, buffer) = self.layers[cache_layer]
            .intermediate_storage_for_folder_base_field_inputs
            .get_mut(&poly)
            .expect("must be present");
        assert!(
            *last_used_for_layer >= sumcheck_step - 1,
            "base folding storage for {:?} advanced only through step {}, but step {} was requested",
            poly,
            *last_used_for_layer,
            sumcheck_step
        );
        let this_layer_start = buffer.initial_pointer();

        let first_access = if *last_used_for_layer >= sumcheck_step {
            false
        } else {
            *last_used_for_layer = sumcheck_step;
            true
        };

        Ok(GpuBaseFieldPolySourceAfterTwoFoldingsPlan {
            base_input_start: base_poly_ptr,
            this_layer_cache_start: this_layer_start,
            base_layer_half_size: base_poly_len / 2,
            base_quarter_size: base_poly_len / 4,
            next_layer_size: base_poly_len / 8,
            first_access,
            source_kind,
        })
    }

    fn plan_base_source_for_rounds_3_and_beyond(
        &mut self,
        poly: GKRAddress,
        request_layer: usize,
        sumcheck_step: usize,
    ) -> GpuExtensionFieldPolyContinuingSourcePlan<E> {
        assert!(sumcheck_step >= 3);

        let cache_layer = request_layer;
        let (last_used_for_layer, buffer) = self.layers[cache_layer]
            .intermediate_storage_for_folder_base_field_inputs
            .get_mut(&poly)
            .expect("must be present");
        assert!(
            *last_used_for_layer >= sumcheck_step - 1,
            "base folding storage for {:?} advanced only through step {}, but step {} was requested",
            poly,
            *last_used_for_layer,
            sumcheck_step
        );
        let (previous_layer_start, this_layer_start) =
            buffer.pointers_for_sumcheck_accessor_step(sumcheck_step);
        let this_layer_size = buffer.size_after_two_folds >> (sumcheck_step - 2);
        let next_layer_size = this_layer_size / 2;

        let first_access = if *last_used_for_layer >= sumcheck_step {
            false
        } else {
            *last_used_for_layer = sumcheck_step;
            true
        };

        GpuExtensionFieldPolyContinuingSourcePlan {
            previous_layer_start,
            this_layer_start,
            this_layer_size,
            next_layer_size,
            first_access,
        }
    }

    fn plan_ext_source_for_rounds_1_and_beyond(
        &mut self,
        poly: GKRAddress,
        sumcheck_step: usize,
        context: &ProverContext,
    ) -> CudaResult<GpuExtensionFieldPolyContinuingSourcePlan<E>> {
        assert!(sumcheck_step >= 1);

        let layer = Self::ext_poly_layer(poly).expect("must be present");

        if sumcheck_step == 1
            && !self.layers[layer]
                .intermediate_storage_for_folder_extension_field_inputs
                .contains_key(&poly)
        {
            let poly_ref = self.layers[layer]
                .extension_field_inputs
                .get(&poly)
                .expect("must be present");
            let size = poly_ref.len();
            let input_pointer = poly_ref.as_ptr();
            let mut buffer = if self.layers[layer]
                .intermediate_folding_consolidated
                .is_some()
            {
                let layout = self
                    .layout
                    .as_ref()
                    .expect("storage layout required for consolidated folding lookup")
                    .clone();
                let (_canonical_layer, class, _field, _poly_idx_in_class) = layout
                    .lookup(layer, &poly)
                    .unwrap_or_else(|| {
                        panic!(
                            "dim-reducing input {poly:?} missing from storage layout at layer {layer}"
                        )
                    });
                let consolidated = self.layers[layer]
                    .intermediate_folding_consolidated
                    .as_ref()
                    .expect("checked above");
                assert_eq!(
                    consolidated.per_poly_size, size,
                    "consolidated folding backing per-poly size {} mismatches input poly len {} at layer {layer}",
                    consolidated.per_poly_size, size,
                );
                let backing = consolidated.per_class.get(&class).unwrap_or_else(|| {
                    panic!(
                        "dim-reducing input {poly:?} class {class:?} missing from consolidated folding backing at layer {layer}"
                    )
                });
                let cache_idx = consolidated
                    .poly_index
                    .get(&poly)
                    .copied()
                    .unwrap_or_else(|| {
                        panic!(
                        "dim-reducing input {poly:?} missing dense cache index at layer {layer}"
                    )
                    });
                let offset = cache_idx as usize * consolidated.per_poly_size;
                GpuExtensionFieldPolyIntermediateFoldingStorage::from_arc(
                    Arc::clone(backing),
                    offset,
                    size,
                )
            } else {
                GpuExtensionFieldPolyIntermediateFoldingStorage::new_for_extension_poly_size(
                    size, context,
                )?
            };
            let buffer_pointer = buffer.pointer_for_sumcheck_after_one_fold();

            self.layers[layer]
                .intermediate_storage_for_folder_extension_field_inputs
                .insert(poly, (1, buffer));

            Ok(GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start: input_pointer,
                this_layer_start: buffer_pointer,
                this_layer_size: size / 2,
                next_layer_size: size / 4,
                first_access: true,
            })
        } else {
            let (last_used_for_layer, buffer) = self.layers[layer]
                .intermediate_storage_for_folder_extension_field_inputs
                .get_mut(&poly)
                .expect("must be present");
            assert!(
                *last_used_for_layer >= sumcheck_step - 1,
                "extension folding storage for {:?} advanced only through step {}, but step {} was requested",
                poly,
                *last_used_for_layer,
                sumcheck_step
            );
            let (previous_layer_start, this_layer_start) =
                buffer.pointer_for_sumcheck_continuation(sumcheck_step);
            let this_layer_size = buffer.size_after_one_fold >> (sumcheck_step - 1);
            let next_layer_size = this_layer_size / 2;

            let first_access = if *last_used_for_layer >= sumcheck_step {
                false
            } else {
                *last_used_for_layer = sumcheck_step;
                true
            };

            Ok(GpuExtensionFieldPolyContinuingSourcePlan {
                previous_layer_start,
                this_layer_start,
                this_layer_size,
                next_layer_size,
                first_access,
            })
        }
    }

    pub(crate) fn get_for_sumcheck_round_0(
        &self,
        inputs: &GKRInputs,
    ) -> GpuSumcheckRound0LaunchDescriptors<B, E> {
        let mut storage = GpuSumcheckRound0LaunchDescriptors::default();

        for input in inputs.inputs_in_base.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .base_field_inputs
                    .push(GpuBaseFieldPolySource::empty());
            } else {
                storage
                    .base_field_inputs
                    .push(self.get_base_source_for_round_0(*input));
            }
        }

        for input in inputs.inputs_in_extension.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .extension_field_inputs
                    .push(GpuExtensionFieldPolyInitialSource::empty());
            } else {
                let layer = Self::round_input_layer(*input);
                let source = self.layers[layer]
                    .extension_field_inputs
                    .get(input)
                    .unwrap_or_else(|| {
                        panic!(
                            "Polynomial with address {:?} is missing from input sources for extension field polys",
                            input
                        )
                    });
                storage.extension_field_inputs.push(source.accessor());
            }
        }

        for output in inputs.outputs_in_base.iter() {
            if *output == GKRAddress::placeholder() {
                storage
                    .base_field_outputs
                    .push(GpuBaseFieldPolySource::empty());
            } else {
                let layer = Self::round_output_layer(*output);
                let source = self.layers[layer]
                    .base_field_inputs
                    .get(output)
                    .unwrap_or_else(|| {
                        panic!(
                            "Polynomial with address {:?} is missing from output sources for base field polys",
                            output
                        )
                    });
                storage.base_field_outputs.push(source.accessor());
            }
        }

        for output in inputs.outputs_in_extension.iter() {
            if *output == GKRAddress::placeholder() {
                storage
                    .extension_field_outputs
                    .push(GpuExtensionFieldPolyInitialSource::empty());
            } else {
                let layer = Self::round_output_layer(*output);
                let source = self.layers[layer]
                    .extension_field_inputs
                    .get(output)
                    .unwrap_or_else(|| {
                        panic!(
                            "Polynomial with address {:?} is missing from output sources for extension field polys",
                            output
                        )
                    });
                storage.extension_field_outputs.push(source.accessor());
            }
        }

        storage
    }

    #[cfg(test)]
    pub(crate) fn schedule_upload_for_sumcheck_round_0(
        &self,
        inputs: &GKRInputs,
        context: &ProverContext,
    ) -> CudaResult<GpuSumcheckRound0ScheduledLaunchDescriptors<B, E>> {
        let host_values = self.get_for_sumcheck_round_0(inputs);
        let mut callbacks = Callbacks::new();
        let host = GpuSumcheckRound0HostLaunchDescriptors {
            base_field_inputs: alloc_host_and_schedule_copy(
                context,
                &mut callbacks,
                host_values.base_field_inputs,
            ),
            extension_field_inputs: alloc_host_and_schedule_copy(
                context,
                &mut callbacks,
                host_values.extension_field_inputs,
            ),
            base_field_outputs: alloc_host_and_schedule_copy(
                context,
                &mut callbacks,
                host_values.base_field_outputs,
            ),
            extension_field_outputs: alloc_host_and_schedule_copy(
                context,
                &mut callbacks,
                host_values.extension_field_outputs,
            ),
        };
        let device = GpuSumcheckRound0DeviceLaunchDescriptors {
            base_field_inputs: alloc_device_and_schedule_upload(context, &host.base_field_inputs)?,
            extension_field_inputs: alloc_device_and_schedule_upload(
                context,
                &host.extension_field_inputs,
            )?,
            base_field_outputs: alloc_device_and_schedule_upload(
                context,
                &host.base_field_outputs,
            )?,
            extension_field_outputs: alloc_device_and_schedule_upload(
                context,
                &host.extension_field_outputs,
            )?,
        };

        Ok(GpuSumcheckRound0ScheduledLaunchDescriptors {
            callbacks,
            host,
            device,
        })
    }

    pub(crate) fn prepare_for_sumcheck_round_1(
        &mut self,
        inputs: &GKRInputs,
        request_layer: usize,
        context: &ProverContext,
    ) -> CudaResult<GpuSumcheckRound1PreparedStorage<B, E>> {
        let mut storage = GpuSumcheckRound1PreparedStorage {
            base_field_inputs: Vec::new(),
            extension_field_inputs: Vec::new(),
        };
        for input in inputs.inputs_in_base.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .base_field_inputs
                    .push(GpuBaseFieldPolySourceAfterOneFoldingPlan::empty());
            } else {
                storage
                    .base_field_inputs
                    .push(self.plan_base_source_for_round_1(*input, request_layer, context)?);
            }
        }
        for input in inputs.inputs_in_extension.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .extension_field_inputs
                    .push(GpuExtensionFieldPolyContinuingSourcePlan::empty());
            } else {
                storage
                    .extension_field_inputs
                    .push(self.plan_ext_source_for_rounds_1_and_beyond(*input, 1, context)?);
            }
        }

        Ok(storage)
    }

    pub(crate) fn prepare_for_sumcheck_round_2(
        &mut self,
        inputs: &GKRInputs,
        request_layer: usize,
        context: &ProverContext,
    ) -> CudaResult<GpuSumcheckRound2PreparedStorage<B, E>> {
        let mut storage = GpuSumcheckRound2PreparedStorage {
            base_field_inputs: Vec::new(),
            extension_field_inputs: Vec::new(),
        };
        for input in inputs.inputs_in_base.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .base_field_inputs
                    .push(GpuBaseFieldPolySourceAfterTwoFoldingsPlan::empty());
            } else {
                storage
                    .base_field_inputs
                    .push(self.plan_base_source_for_round_2(*input, request_layer, context)?);
            }
        }
        for input in inputs.inputs_in_extension.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .extension_field_inputs
                    .push(GpuExtensionFieldPolyContinuingSourcePlan::empty());
            } else {
                storage
                    .extension_field_inputs
                    .push(self.plan_ext_source_for_rounds_1_and_beyond(*input, 2, context)?);
            }
        }

        Ok(storage)
    }

    pub(crate) fn prepare_for_sumcheck_round_3_and_beyond(
        &mut self,
        inputs: &GKRInputs,
        request_layer: usize,
        sumcheck_step: usize,
        context: &ProverContext,
    ) -> CudaResult<GpuSumcheckRound3AndBeyondPreparedStorage<E>> {
        assert!(sumcheck_step >= 3);

        let mut storage = GpuSumcheckRound3AndBeyondPreparedStorage {
            base_field_inputs: Vec::new(),
            extension_field_inputs: Vec::new(),
        };
        for input in inputs.inputs_in_base.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .base_field_inputs
                    .push(GpuExtensionFieldPolyContinuingSourcePlan::empty());
            } else {
                storage
                    .base_field_inputs
                    .push(self.plan_base_source_for_rounds_3_and_beyond(
                        *input,
                        request_layer,
                        sumcheck_step,
                    ));
            }
        }
        for input in inputs.inputs_in_extension.iter() {
            if *input == GKRAddress::placeholder() {
                storage
                    .extension_field_inputs
                    .push(GpuExtensionFieldPolyContinuingSourcePlan::empty());
            } else {
                storage
                    .extension_field_inputs
                    .push(self.plan_ext_source_for_rounds_1_and_beyond(
                        *input,
                        sumcheck_step,
                        context,
                    )?);
            }
        }

        Ok(storage)
    }
}
