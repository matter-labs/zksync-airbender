use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;

use super::recompute_plan::RecomputePlan;
use super::vm::lower::{lower_desc, FwdVmInputs, LoweredFwdVm, ResolvedColumn};
use super::vm::production_bind::{arg_derived_e4_value, resolve_storage_column};
use crate::setup::GpuGKRForwardSetup;
use crate::stage1::{GpuGKRLookupMappings, GpuGKRStage1Output};
use crate::storage_layout::{address_storage_layer, FieldType};
use crate::upstream::{GKRAddress, GKRExternalChallenges};
use crate::{GkrPrograms, GpuBaseFieldPoly, GpuExtensionFieldPoly, GpuGKRStorage};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub enum GkrMemoryPolicy {
    #[default]
    Materialize,
    Recompute {
        /// Omit value layers L1 through L[value_layers], except required carries.
        value_layers: usize,
        /// Omit caches C0 through C[cache_layers - 1], except required carries.
        cache_layers: usize,
    },
}

impl GkrMemoryPolicy {
    pub fn candidates() -> impl Iterator<Item = Self> {
        std::iter::once(Self::Materialize).chain((0..=2).flat_map(|value_layers| {
            (0..=3)
                .filter(move |&cache_layers| value_layers != 0 || cache_layers != 0)
                .map(move |cache_layers| Self::Recompute {
                    value_layers,
                    cache_layers,
                })
        }))
    }
}

pub(crate) struct ForwardReplay {
    plan: Arc<RecomputePlan>,
    mappings: GpuGKRLookupMappings,
    table: Option<DeviceAllocation<E4>>,
    decoder_fill: Arc<DeviceAllocation<E4>>,
    external: GKRExternalChallenges<BF, E4>,
    top_bits: Vec<u32>,
    blocks: u32,
}

pub(super) struct TemporaryColumns {
    _base: Option<DeviceAllocation<BF>>,
    _ext: Option<DeviceAllocation<E4>>,
    columns: BTreeMap<GKRAddress, ResolvedColumn>,
}

impl TemporaryColumns {
    fn new(
        plan: &RecomputePlan,
        addresses: &BTreeSet<GKRAddress>,
        rows: usize,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let base_count = addresses
            .iter()
            .filter(|a| plan.fields[a] == FieldType::Base)
            .count();
        let ext_count = addresses.len() - base_count;
        let base = (base_count != 0)
            .then(|| context.alloc::<BF>(base_count * rows, AllocationPlacement::Top))
            .transpose()?;
        let ext = (ext_count != 0)
            .then(|| context.alloc::<E4>(ext_count * rows, AllocationPlacement::Top))
            .transpose()?;
        let mut columns = BTreeMap::new();
        let mut indexes = [0, 0];
        for &address in addresses {
            let is_e4 = plan.fields[&address] == FieldType::Ext;
            let (matrix_base, size) = if is_e4 {
                (ext.as_ref().unwrap().as_ptr() as *mut u8, size_of::<E4>())
            } else {
                (base.as_ref().unwrap().as_ptr() as *mut u8, size_of::<BF>())
            };
            let index = &mut indexes[usize::from(is_e4)];
            let stride_bytes =
                u32::try_from(rows * size).expect("temporary column stride fits u32");
            let ptr = unsafe { matrix_base.add(*index * rows * size) };
            *index += 1;
            columns.insert(
                address,
                ResolvedColumn {
                    is_e4,
                    ptr,
                    matrix_base,
                    stride_bytes,
                },
            );
        }
        Ok(Self {
            _base: base,
            _ext: ext,
            columns,
        })
    }

    fn mark_descriptor(&self, lowered: &mut LoweredFwdVm) {
        let is_temporary = |base: *mut u8| {
            self.columns.values().any(|c| {
                let offset = (base as usize).wrapping_sub(c.matrix_base as usize);
                offset
                    < if c.is_e4 {
                        self._ext.as_ref().unwrap().len() * size_of::<E4>()
                    } else {
                        self._base.as_ref().unwrap().len() * size_of::<BF>()
                    }
            })
        };
        for (i, &base) in lowered.desc.source_base.iter().enumerate() {
            if is_temporary(base) {
                lowered.desc.temporary_source_mask |= 1 << i;
            }
        }
        for (i, &base) in lowered.desc.dst_base.iter().enumerate() {
            if is_temporary(base) {
                lowered.desc.temporary_dst_mask |= 1 << i;
            }
        }
    }
}

fn allocate_columns(
    storage: &mut GpuGKRStorage<BF, E4>,
    plan: &RecomputePlan,
    addresses: &BTreeSet<GKRAddress>,
    rows: usize,
    placement: AllocationPlacement,
    context: &ProverContext,
) -> CudaResult<()> {
    let mut groups = BTreeMap::<_, Vec<_>>::new();
    for &address in addresses {
        assert!(
            resolve_storage_column(storage, address).is_none(),
            "recomputed destination already exists: {address:?}"
        );
        groups
            .entry((address_storage_layer(address), plan.fields[&address]))
            .or_default()
            .push(address);
    }
    for ((layer, field), addresses) in groups {
        match field {
            FieldType::Base => {
                let backing = Arc::new(context.alloc(addresses.len() * rows, placement)?);
                for (column, address) in addresses.into_iter().enumerate() {
                    storage.insert_base_field_at_layer(
                        layer,
                        address,
                        GpuBaseFieldPoly::from_arc(backing.clone(), column * rows, rows),
                    );
                }
            }
            FieldType::Ext => {
                let backing = Arc::new(context.alloc(addresses.len() * rows, placement)?);
                for (column, address) in addresses.into_iter().enumerate() {
                    storage.insert_extension_at_layer(
                        layer,
                        address,
                        GpuExtensionFieldPoly::from_arc(backing.clone(), column * rows, rows),
                    );
                }
            }
        }
    }
    for (&alias, &canonical) in &plan.aliases {
        if resolve_storage_column(storage, alias).is_some() {
            continue;
        }
        let layer = address_storage_layer(alias);
        if layer >= storage.layers.len() {
            continue;
        }
        if let Some(value) = storage.try_get_base_poly(canonical).cloned() {
            storage.insert_base_field_at_layer(layer, alias, value);
        } else if let Some(value) = storage.try_get_ext_poly(canonical).cloned() {
            storage.insert_extension_at_layer(layer, alias, value);
        }
    }
    Ok(())
}

impl ForwardReplay {
    pub(super) fn prepare(
        programs: &GkrPrograms,
        storage: &mut GpuGKRStorage<BF, E4>,
        stage1: &mut GpuGKRStage1Output,
        setup: &mut GpuGKRForwardSetup,
        external: &GKRExternalChallenges<BF, E4>,
        top_bits: &[u32],
        policy: GkrMemoryPolicy,
        context: &ProverContext,
    ) -> CudaResult<(Self, LoweredFwdVm, TemporaryColumns)> {
        let plan = programs.recompute_plan(
            storage
                .layout
                .as_ref()
                .expect("recomputation storage layout"),
            policy,
        );
        let count = programs.runtime_circuit().trace_len;
        let blocks = (context.get_device_properties().sm_count as u32 * 11)
            .min((count as u32).div_ceil(128));
        for layer in 0..programs.forward.layers.len() {
            super::hydrate_scratch_space_layer(layer, programs.runtime_circuit(), stage1, storage);
        }
        storage
            .layers
            .resize_with(programs.forward.layers.len() + 1, Default::default);
        allocate_columns(
            storage,
            &plan,
            &plan.retained,
            count,
            AllocationPlacement::Top,
            context,
        )?;
        let inputs = super::vm::production_bind::production_header(stage1, setup, count, top_bits);
        let temporary = plan.temporary(
            programs.forward.layers.len(),
            &plan.retained,
            &plan.retained,
        );
        let workspace = TemporaryColumns::new(&plan, &temporary, blocks as usize * 128, context)?;
        let destinations = plan.retained.union(&temporary).copied().collect();
        let layers = plan.filtered_layers(&programs.forward.layers, &destinations);
        let resolve = |address| {
            let canonical = plan.canonical(address);
            workspace
                .columns
                .get(&canonical)
                .copied()
                .or_else(|| resolve_storage_column(storage, canonical))
        };
        let challenge = |r: &_| arg_derived_e4_value(external, r).unwrap_or_else(|e| panic!("{e}"));
        let mut lowered = lower_desc(&layers, &inputs, &resolve, &challenge)
            .unwrap_or_else(|e| panic!("streaming forward binding: {e:?}"));
        workspace.mark_descriptor(&mut lowered);
        let replay = Self {
            plan,
            mappings: std::mem::take(&mut stage1.lookup_mappings),
            table: setup.take_generic_lookup(),
            decoder_fill: setup.decoder_fill_owner(),
            external: external.clone(),
            top_bits: top_bits.to_vec(),
            blocks,
        };
        Ok((replay, lowered, workspace))
    }

    pub fn blocks(&self) -> u32 {
        self.blocks
    }

    pub fn schedule(
        &self,
        layer: usize,
        programs: &GkrPrograms,
        storage: &mut GpuGKRStorage<BF, E4>,
        lookup: &DeviceSlice<E4>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let missing: BTreeSet<_> = self.plan.backward[layer]
            .iter()
            .copied()
            .filter(|&a| resolve_storage_column(storage, a).is_none())
            .collect();
        if missing.is_empty() {
            return Ok(());
        }
        let range = Range::new("gkr.backward.recompute")?;
        range.start(context.get_exec_stream())?;
        let end = self
            .plan
            .writes
            .iter()
            .rposition(|writes| !writes.is_disjoint(&missing))
            .expect("missing backward source has a forward producer")
            + 1;
        let count = programs.runtime_circuit().trace_len;
        let resident: BTreeSet<_> = self
            .plan
            .fields
            .keys()
            .copied()
            .filter(|&a| resolve_storage_column(storage, a).is_some())
            .collect();
        let (layers, temporary) =
            self.plan
                .replay_layers(&programs.forward.layers[..end], &resident, &missing);
        let workspace =
            TemporaryColumns::new(&self.plan, &temporary, self.blocks as usize * 128, context)?;
        // Keep replayed inputs below the tail so dropping outputs extends the
        // same free range needed by the next replay.
        allocate_columns(
            storage,
            &self.plan,
            &missing,
            count,
            AllocationPlacement::Bottom,
            context,
        )?;
        let m = &self.mappings;
        let inputs = FwdVmInputs {
            mapping_arena: [
                m.has_generic_family()
                    .then(|| m.generic_family().as_ptr())
                    .unwrap_or(std::ptr::null()),
                m.has_range_check_16()
                    .then(|| m.range_check_16().as_ptr())
                    .unwrap_or(std::ptr::null()),
                m.has_timestamp()
                    .then(|| m.timestamp().as_ptr())
                    .unwrap_or(std::ptr::null()),
            ],
            decoder_mapping_col: m.has_decoder.then(|| {
                u16::try_from(m.num_generic_sets).expect("decoder mapping column fits u16")
            }),
            table: self.table.as_ref().map_or(std::ptr::null(), |t| t.as_ptr()),
            table_len: self.table.as_ref().map_or(0, |t| t.len() as u32),
            count: count as u32,
            inits_and_teardowns_top_bits: &self.top_bits,
        };
        let resolve = |address| {
            let canonical = self.plan.canonical(address);
            workspace
                .columns
                .get(&canonical)
                .copied()
                .or_else(|| resolve_storage_column(storage, canonical))
        };
        let challenge =
            |r: &_| arg_derived_e4_value(&self.external, r).unwrap_or_else(|e| panic!("{e}"));
        let mut lowered = lower_desc(&layers, &inputs, &resolve, &challenge)
            .unwrap_or_else(|e| panic!("forward replay binding: {e:?}"));
        workspace.mark_descriptor(&mut lowered);
        super::vm::production_bind::stage_replay_constants(
            &lowered,
            &lookup[1..2],
            &self.decoder_fill,
            context,
        )?;
        super::vm::launch_fwd_vm_streaming(&lowered.desc, self.blocks, context)?;
        range.end(context.get_exec_stream())?;
        Ok(())
    }
}
