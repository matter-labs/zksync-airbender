use era_cudart::result::CudaResult;

use crate::prover::gkr::GpuGKRStorage;

use super::super::kernels::*;
use super::super::{compact, flat};
use super::blueprints::{
    build_main_layer_kernel_blueprints_static, resolve_main_layer_auxiliary_challenge,
    resolve_main_layer_constraint_metadata, summarize_main_layer_constraint_metadata_source,
    PreparedMainLayerKernelStaticData,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::cub::device_reduce::{get_reduce_temp_storage_bytes, Reduce, ReduceOperation};
use crate::ops::cub::CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::ProverContext;
use crate::primitives::field::BF;
use crate::upstream::{Field, FieldExtension, GKRAddress};

impl<E: Field + FieldExtension<BF>> GpuGKRMainLayerBackwardState<E> {
    pub(crate) fn storage(&self) -> &GpuGKRStorage<BF, E> {
        &self.storage
    }

    pub(crate) fn purge_up_to_layer(&mut self, layer: usize) {
        self.storage.purge_up_to_layer(layer);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::prover::gkr::backward) struct FlatContinuationLaunchSizes {
    pub(super) fold_stride: u32,
    pub(super) next_layer_size: u32,
}

impl FlatContinuationLaunchSizes {
    pub(in crate::prover::gkr::backward) fn from_sizes(
        fold_stride: usize,
        next_layer_size: usize,
    ) -> Self {
        assert!(
            fold_stride <= u32::MAX as usize && next_layer_size <= u32::MAX as usize,
            "flat continuation: fold sizes overflow u32 (fold_stride={fold_stride}, next_layer_size={next_layer_size})",
        );
        Self {
            fold_stride: fold_stride as u32,
            next_layer_size: next_layer_size as u32,
        }
    }

    fn from_acc_size(acc_size: usize) -> Self {
        Self::from_sizes(acc_size, acc_size)
    }
}

#[allow(dead_code)]
#[derive(Clone, Copy, Debug)]
pub(in crate::prover::gkr::backward) struct FlatContinuationSizeCheck {
    pub(in crate::prover::gkr::backward) sizes: Option<FlatContinuationLaunchSizes>,
    pub(in crate::prover::gkr::backward) has_sources: bool,
    pub(in crate::prover::gkr::backward) consistent: bool,
}

impl FlatContinuationSizeCheck {
    pub(in crate::prover::gkr::backward) fn empty() -> Self {
        Self {
            sizes: None,
            has_sources: false,
            consistent: true,
        }
    }

    pub(super) fn resolve(&self, acc_size: usize) -> Option<FlatContinuationLaunchSizes> {
        if !self.consistent {
            return None;
        }
        Some(
            self.sizes
                .unwrap_or_else(|| FlatContinuationLaunchSizes::from_acc_size(acc_size)),
        )
    }
}

impl<E: Field + FieldExtension<BF> + Reduce> GpuGKRMainLayerBackwardState<E> {
    fn prepare_layer_from_blueprints(
        &mut self,
        layer_idx: usize,
        blueprints: Vec<GpuGKRMainLayerKernelBlueprint<E>>,
        batch_challenge_base: Option<E>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRMainLayerSumcheckLayerPlan<E>> {
        let folding_steps = self.trace_len.trailing_zeros() as usize;
        assert!(
            blueprints.len() <= GKR_BACKWARD_MAX_KERNELS_PER_LAYER,
            "fused main-layer backward supports at most {} kernels per layer, got {}",
            GKR_BACKWARD_MAX_KERNELS_PER_LAYER,
            blueprints.len()
        );

        let mut round0_descriptors = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round0_descriptors.push(self.storage.get_for_sumcheck_round_0(&blueprint.inputs));
        }

        // Pre-allocate consolidated folding backings per
        // `(layer, AddressClass)` so per-blueprint
        // `prepare_for_sumcheck_round_*` calls slice views into them
        // instead of allocating per-poly. Round-1+ compact kernel-arg
        // encoding indexes into these Arcs via a u16 source descriptor +
        // per-launch bases table.
        //
        // - Base inputs route through `register_flat_base_folding_for_layer`.
        //   `VirtualSetup` polys are excluded — no layout slot; they fall
        //   back to per-poly allocation.
        // - Ext inputs route through `register_dim_reducing_inputs_for_layer`
        //   (same consolidation shape used by the dim-reducing path; the
        //   function name carries over for main-layer artifact layers).
        let flat_base_inputs: std::collections::BTreeSet<GKRAddress> = blueprints
            .iter()
            .flat_map(|bp| bp.inputs.inputs_in_base.iter().copied())
            .filter(|addr| *addr != GKRAddress::placeholder())
            .collect();
        self.storage
            .register_flat_base_folding_for_layer(layer_idx, &flat_base_inputs, context)?;
        let flat_ext_inputs: std::collections::BTreeSet<GKRAddress> = blueprints
            .iter()
            .flat_map(|bp| bp.inputs.inputs_in_extension.iter().copied())
            .filter(|addr| *addr != GKRAddress::placeholder())
            .collect();
        if !flat_ext_inputs.is_empty() {
            self.storage.register_dim_reducing_inputs_for_layer(
                layer_idx,
                &flat_ext_inputs,
                context,
            )?;
        }

        let mut round1_prepared_all = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round1_prepared_all.push(self.storage.prepare_for_sumcheck_round_1(
                &blueprint.inputs,
                layer_idx,
                context,
            )?);
        }

        let mut round2_prepared_all = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round2_prepared_all.push(self.storage.prepare_for_sumcheck_round_2(
                &blueprint.inputs,
                layer_idx,
                context,
            )?);
        }

        let mut round3_prepared_all = Vec::with_capacity(blueprints.len());
        round3_prepared_all.resize_with(blueprints.len(), Vec::new);
        for step in 3..folding_steps {
            for (prepared_for_kernel, blueprint) in
                round3_prepared_all.iter_mut().zip(blueprints.iter())
            {
                let prepared = self.storage.prepare_for_sumcheck_round_3_and_beyond(
                    &blueprint.inputs,
                    layer_idx,
                    step,
                    context,
                )?;
                prepared_for_kernel.push(GpuGKRMainLayerRound3Prepared { step, prepared });
            }
        }

        let mut static_data = Vec::with_capacity(blueprints.len());
        let mut kernel_plans = Vec::with_capacity(blueprints.len());
        for (
            (((blueprint, round0_descriptors_for_kernel), round1_prepared), round2_prepared),
            round3_and_beyond_prepared,
        ) in blueprints
            .into_iter()
            .zip(round0_descriptors.iter().cloned())
            .zip(round1_prepared_all.into_iter())
            .zip(round2_prepared_all.into_iter())
            .zip(round3_prepared_all.into_iter())
        {
            let auxiliary_challenge = if batch_challenge_base.is_some() {
                resolve_main_layer_auxiliary_challenge(
                    blueprint.auxiliary_challenge_source,
                    self.lookup_additive_challenge,
                )
            } else {
                match blueprint.auxiliary_challenge_source {
                    GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(value) => value,
                    GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive => E::ZERO,
                }
            };
            let constraint_metadata = if batch_challenge_base.is_some() {
                resolve_main_layer_constraint_metadata(blueprint.constraint_metadata_source.clone())
            } else {
                match blueprint.constraint_metadata_source.as_ref() {
                    None => None,
                    Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata)) => {
                        Some(metadata.clone())
                    }
                    Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(_)) => None,
                }
            };
            let constraint_metadata_summary = summarize_main_layer_constraint_metadata_source(
                blueprint.constraint_metadata_source.as_ref(),
            );
            static_data.push(PreparedMainLayerKernelStaticData {
                kind: blueprint.kind,
                auxiliary_challenge,
                constraint_metadata: constraint_metadata.clone(),
                round0_descriptors: round0_descriptors_for_kernel,
            });
            kernel_plans.push(GpuGKRMainLayerKernelPlan {
                kind: blueprint.kind,
                inputs: blueprint.inputs,
                batch_challenge_offset: blueprint.batch_challenge_offset,
                batch_challenge_count: blueprint.batch_challenge_count,
                batch_challenges: blueprint.batch_challenges,
                auxiliary_challenge_source: blueprint.auxiliary_challenge_source,
                constraint_metadata_source: blueprint.constraint_metadata_source,
                constraint_metadata_summary,
                round1_prepared,
                round2_prepared,
                round3_and_beyond_prepared,
            });
        }

        // Build the flat round 0 plan in compact form directly. The builder
        // resolves each gate's source pointers against the per-(layer, class)
        // consolidated storage backings and emits packed `u16` source
        // descriptors as it walks the gates.
        let flat_round0_template_compact: Option<compact::FlatRound0BuildPlan<E>> = {
            let gates: Vec<_> = static_data
                .iter()
                .zip(kernel_plans.iter())
                .map(|(sd, kp)| flat::PreparedGateForFlatPlan {
                    kind: sd.kind,
                    round0: &sd.round0_descriptors,
                    batch_challenge_power_offset: kp.batch_challenge_offset as u32,
                    constraint_source: kp.constraint_metadata_source.as_ref(),
                })
                .collect();
            Some(flat::build_flat_round0_plan(&gates, &self.storage))
        };

        // Compile one inline descriptor for the round-0 eval-recipes launch.
        let mut recipe_callbacks = Callbacks::new();
        let (flat_recipe_desc, flat_recipe_count, flat_coeff_device_buf, flat_use_constant) =
            if let Some(ref plan) = flat_round0_template_compact {
                let total = plan.total_coefficients();
                if total > 0 {
                    let compiled = flat::compile_recipes_for_device(&plan.recipes);
                    let use_constant = !self.is_delegation || layer_idx != 0;
                    if use_constant {
                        assert!(
                            total <= flat::FLAT_ROUND0_CONST_MAX,
                            "flat round 0: {} coefficients exceeds __constant__ limit of {}",
                            total,
                            flat::FLAT_ROUND0_CONST_MAX,
                        );
                    }
                    let coeff_buf = if use_constant {
                        None // eval_recipes writes directly to __constant__ symbol
                    } else {
                        Some(context.alloc(total, AllocationPlacement::BestFit)?)
                    };
                    (
                        Some(compiled.desc),
                        compiled.num_recipes,
                        coeff_buf,
                        use_constant,
                    )
                } else {
                    (None, 0, None, true)
                }
            } else {
                (None, 0, None, true)
            };
        // Restored — no diagnostic override

        let max_acc_size = self.trace_len / 2;
        let reduction_temp_storage_bytes =
            get_reduce_temp_storage_bytes::<E>(ReduceOperation::Sum, max_acc_size as i32)?;
        let round_scratch = GpuGKRMainLayerRoundScratch {
            claim_point: context.alloc(folding_steps + 1, AllocationPlacement::Top)?,
            eq_high_groups: context.alloc(
                GKR_EQ_MAX_HIGH_GROUPS * GKR_EQ_GROUP_TABLE_LEN,
                AllocationPlacement::Top,
            )?,
            eq_low_group: context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)?,
            accumulator: context.alloc(max_acc_size * 2, AllocationPlacement::Top)?,
            reduction_output: context.alloc(2, AllocationPlacement::Top)?,
            reduction_temp_storage: context
                .alloc_with_extra_alignment::<u8, CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2>(
                    reduction_temp_storage_bytes,
                    AllocationPlacement::Top,
                )?,
        };

        // --- Build flat continuation plan for rounds 1+ ---
        let (
            flat_continuation_plan,
            flat_continuation_per_step_sources,
            flat_cont_recipe_desc,
            flat_cont_recipe_count,
            cont_recipe_callbacks,
        ) = self.build_flat_continuation_artifacts(
            &static_data,
            &kernel_plans,
            folding_steps,
            layer_idx,
            context,
        )?;
        recipe_callbacks.extend(cont_recipe_callbacks);

        let flat_round1_desc =
            Self::build_flat_round1_desc(flat_continuation_plan.as_ref(), &kernel_plans);
        let flat_round2_desc =
            Self::build_flat_round2_desc(flat_continuation_plan.as_ref(), &kernel_plans);

        // Compact descriptors: each fused builder takes the static desc +
        // plan + storage and produces the compact unified desc in one pass
        // (source pointers resolve to compact `(slot, poly_idx)` records
        // and term/tile/fold metadata builds inline). The consolidated
        // per-(layer, class) base-folding backings cover the base side;
        // `intermediate_folding_consolidated` covers the ext side.
        let flat_round1_unified_desc_compact = if let (Some(ref r1_desc), Some(plan)) =
            (&flat_round1_desc, flat_continuation_plan.as_ref())
        {
            Some(compact::build_flat_round1_unified_desc::<E>(
                r1_desc,
                plan,
                &self.storage,
            ))
        } else {
            None
        };
        let flat_round2_unified_desc_compact = if let (Some(ref r2_desc), Some(plan)) =
            (&flat_round2_desc, flat_continuation_plan.as_ref())
        {
            Some(compact::build_flat_round2_unified_desc::<E>(
                r2_desc,
                plan,
                &self.storage,
            ))
        } else {
            None
        };
        let flat_continuation_unified_descs_compact: Vec<(
            usize,
            Box<compact::GpuFlatContinuationUnifiedDesc>,
        )> = if let Some(ref plan) = flat_continuation_plan {
            flat_continuation_per_step_sources
                .iter()
                .map(|(step, sources)| {
                    let compact =
                        compact::build_flat_continuation_unified_desc(sources, plan, &self.storage);
                    (*step, compact)
                })
                .collect()
        } else {
            Vec::new()
        };

        if std::env::var("GPU_PROVER_DUMP_FLAT_PLAN").is_ok() {
            flat::dump_flat_round1_plan(
                layer_idx,
                flat_round1_desc.as_deref(),
                flat_continuation_plan.as_ref(),
                &kernel_plans,
            );
        }

        Ok(GpuGKRMainLayerSumcheckLayerPlan {
            layer_idx,
            trace_len: self.trace_len,
            folding_steps,
            batch_challenge_base,
            lookup_multiplicative_challenge: self.lookup_multiplicative_challenge,
            lookup_additive_challenge: self.lookup_additive_challenge,
            external_challenges_flat: {
                let mut values = self
                    .external_challenges
                    .permutation_argument_linearization_challenges
                    .to_vec();
                values.push(self.external_challenges.permutation_argument_additive_part);
                values
            },
            kernel_plans,
            round0_descriptors,
            flat_round0_template_compact,
            flat_recipe_desc,
            flat_recipe_count,
            flat_coeff_device_buf,
            flat_use_constant,
            flat_continuation_plan,
            flat_cont_recipe_desc,
            flat_cont_recipe_count,
            flat_continuation_unified_descs_compact,
            flat_round1_unified_desc_compact,
            flat_round2_unified_desc_compact,
            round_scratch,
            recipe_upload_callbacks: recipe_callbacks,
            batch_challenge_base_override_ptr: None,
            eq_layout: GkrEqLayoutCompact::zeroed(),
        })
    }

    /// Build round-1 fused-source data from the continuation plan and round 1 prepared storage.
    fn build_flat_round1_desc(
        plan: Option<&flat::FlatContinuationBuildPlan<E>>,
        kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
    ) -> Option<Box<flat::Round1FusedSources>> {
        use flat::{
            GpuFlatBaseAfterOneSourceEntry, GpuFlatContinuingSourceEntry, Round1FusedSources,
            FLAT_CONT_EXT_SOURCE_BIT, FLAT_CONT_MAX_BASE_SOURCES, FLAT_CONT_MAX_EXT_SOURCES,
        };

        let plan = plan?;
        let mut desc = Box::new(Round1FusedSources::default());

        // Build a key→source index map using round3 prepared cache pointers (same as plan).
        let round3_prepared = kernel_plans
            .iter()
            .map(|kp| {
                kp.round3_and_beyond_prepared
                    .iter()
                    .find(|r| r.step == 3)
                    .unwrap_or_else(|| panic!("missing round 3 prepared for step 3"))
            })
            .collect::<Vec<_>>();
        let mut key_map: std::collections::HashMap<(usize, bool), u32> =
            std::collections::HashMap::new();
        for assignment in &plan.source_assignments {
            let r3 = round3_prepared[assignment.gate_idx];
            let cache_ptr = if assignment.is_ext {
                r3.prepared.extension_field_inputs[assignment.input_idx].this_layer_start as usize
            } else {
                r3.prepared.base_field_inputs[assignment.input_idx].this_layer_start as usize
            };
            let key = (cache_ptr, assignment.is_ext);
            if let Some(prev) = key_map.insert(key, assignment.source_table_idx) {
                debug_assert_eq!(
                    prev, assignment.source_table_idx,
                    "flat round1: inconsistent source index for key"
                );
            }
        }

        // Aggregate first_access across *all* gate inputs that map to the same source table idx.
        let mut source_first_access = vec![false; plan.term_desc.num_sources as usize];
        for (gate_idx, kp) in kernel_plans.iter().enumerate() {
            let r3 = round3_prepared[gate_idx];
            for (input_idx, src) in kp.round1_prepared.base_field_inputs.iter().enumerate() {
                let key = (
                    r3.prepared.base_field_inputs[input_idx].this_layer_start as usize,
                    false,
                );
                if let Some(&idx) = key_map.get(&key) {
                    if src.first_access {
                        source_first_access[idx as usize] = true;
                    }
                }
            }
            for (input_idx, src) in kp.round1_prepared.extension_field_inputs.iter().enumerate() {
                let key = (
                    r3.prepared.extension_field_inputs[input_idx].this_layer_start as usize,
                    true,
                );
                if let Some(&idx) = key_map.get(&key) {
                    if src.first_access {
                        source_first_access[idx as usize] = true;
                    }
                }
            }
        }

        // Populate sources. Base sources come from round1_prepared, ext sources from round1_prepared.
        // Source assignments map (gate_idx, is_ext, input_idx) → source_table_idx.
        // For round 1/2, the source index encoding uses the high bit:
        //   base → low indices (unchanged), ext → high bit set.
        // We need to remap: the continuation plan assigned indices into a single flat array,
        // but round 1/2 use split arrays with the high-bit tag.
        let mut base_count = 0u32;
        let mut ext_count = 0u32;
        const UNASSIGNED: u16 = u16::MAX;
        // Map from continuation source_table_idx → round1 tagged index.
        let mut idx_remap = vec![UNASSIGNED; plan.term_desc.num_sources as usize];

        for assignment in &plan.source_assignments {
            let remap_slot = &mut idx_remap[assignment.source_table_idx as usize];
            if *remap_slot != UNASSIGNED {
                debug_assert_eq!(
                    (*remap_slot & FLAT_CONT_EXT_SOURCE_BIT) != 0,
                    assignment.is_ext,
                    "flat round1: inconsistent base/ext mapping for source {}",
                    assignment.source_table_idx,
                );
                continue;
            }
            let kp = &kernel_plans[assignment.gate_idx];
            let combined_first_access = source_first_access[assignment.source_table_idx as usize];
            if assignment.is_ext {
                let src = &kp.round1_prepared.extension_field_inputs[assignment.input_idx];
                let tagged_idx = ext_count as u16 | FLAT_CONT_EXT_SOURCE_BIT;
                assert!(
                    (ext_count as usize) < FLAT_CONT_MAX_EXT_SOURCES,
                    "flat round1: ext source overflow ({ext_count} >= {FLAT_CONT_MAX_EXT_SOURCES})",
                );
                *remap_slot = tagged_idx;
                desc.ext_sources[ext_count as usize] = GpuFlatContinuingSourceEntry {
                    previous_layer_start: if combined_first_access {
                        src.previous_layer_start as *const u8
                    } else {
                        std::ptr::null()
                    },
                    this_layer_cache_start: src.this_layer_start as *mut u8,
                };
                ext_count += 1;
            } else {
                let src = &kp.round1_prepared.base_field_inputs[assignment.input_idx];
                let tagged_idx = base_count as u16;
                assert!(
                    (base_count as usize) < FLAT_CONT_MAX_BASE_SOURCES,
                    "flat round1: base source overflow ({base_count} >= {FLAT_CONT_MAX_BASE_SOURCES})",
                );
                *remap_slot = tagged_idx;
                desc.base_sources[base_count as usize] = GpuFlatBaseAfterOneSourceEntry {
                    base_layer_half_size: src.base_layer_half_size,
                    next_layer_size: src.next_layer_size,
                    base_input_start: src.base_input_start as *const u8,
                    this_layer_cache_start: src.this_layer_cache_start as *mut u8,
                    first_access: combined_first_access,
                    source_kind: src.source_kind,
                };
                base_count += 1;
            }
        }
        desc.num_base_sources = base_count;
        desc.num_ext_sources = ext_count;
        desc.idx_remap = idx_remap;

        Some(desc)
    }

    /// Build round-2 fused-source data from the continuation plan and round 2 prepared storage.
    fn build_flat_round2_desc(
        plan: Option<&flat::FlatContinuationBuildPlan<E>>,
        kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
    ) -> Option<Box<flat::Round2FusedSources>> {
        use flat::{
            GpuFlatBaseAfterTwoSourceEntry, GpuFlatContinuingSourceEntry, Round2FusedSources,
            FLAT_CONT_EXT_SOURCE_BIT, FLAT_CONT_MAX_BASE_SOURCES, FLAT_CONT_MAX_EXT_SOURCES,
        };

        let plan = plan?;
        let mut desc = Box::new(Round2FusedSources::default());

        // Build a key→source index map using round3 prepared cache pointers (same as plan).
        let round3_prepared = kernel_plans
            .iter()
            .map(|kp| {
                kp.round3_and_beyond_prepared
                    .iter()
                    .find(|r| r.step == 3)
                    .unwrap_or_else(|| panic!("missing round 3 prepared for step 3"))
            })
            .collect::<Vec<_>>();
        let mut key_map: std::collections::HashMap<(usize, bool), u32> =
            std::collections::HashMap::new();
        for assignment in &plan.source_assignments {
            let r3 = round3_prepared[assignment.gate_idx];
            let cache_ptr = if assignment.is_ext {
                r3.prepared.extension_field_inputs[assignment.input_idx].this_layer_start as usize
            } else {
                r3.prepared.base_field_inputs[assignment.input_idx].this_layer_start as usize
            };
            let key = (cache_ptr, assignment.is_ext);
            if let Some(prev) = key_map.insert(key, assignment.source_table_idx) {
                debug_assert_eq!(
                    prev, assignment.source_table_idx,
                    "flat round2: inconsistent source index for key"
                );
            }
        }

        // Aggregate first_access across *all* gate inputs that map to the same source table idx.
        let mut source_first_access = vec![false; plan.term_desc.num_sources as usize];
        for (gate_idx, kp) in kernel_plans.iter().enumerate() {
            let r3 = round3_prepared[gate_idx];
            for (input_idx, src) in kp.round2_prepared.base_field_inputs.iter().enumerate() {
                let key = (
                    r3.prepared.base_field_inputs[input_idx].this_layer_start as usize,
                    false,
                );
                if let Some(&idx) = key_map.get(&key) {
                    if src.first_access {
                        source_first_access[idx as usize] = true;
                    }
                }
            }
            for (input_idx, src) in kp.round2_prepared.extension_field_inputs.iter().enumerate() {
                let key = (
                    r3.prepared.extension_field_inputs[input_idx].this_layer_start as usize,
                    true,
                );
                if let Some(&idx) = key_map.get(&key) {
                    if src.first_access {
                        source_first_access[idx as usize] = true;
                    }
                }
            }
        }

        let mut base_count = 0u32;
        let mut ext_count = 0u32;
        const UNASSIGNED: u16 = u16::MAX;
        let mut idx_remap = vec![UNASSIGNED; plan.term_desc.num_sources as usize];

        for assignment in &plan.source_assignments {
            let remap_slot = &mut idx_remap[assignment.source_table_idx as usize];
            if *remap_slot != UNASSIGNED {
                debug_assert_eq!(
                    (*remap_slot & FLAT_CONT_EXT_SOURCE_BIT) != 0,
                    assignment.is_ext,
                    "flat round2: inconsistent base/ext mapping for source {}",
                    assignment.source_table_idx,
                );
                continue;
            }
            let kp = &kernel_plans[assignment.gate_idx];
            let combined_first_access = source_first_access[assignment.source_table_idx as usize];
            if assignment.is_ext {
                let src = &kp.round2_prepared.extension_field_inputs[assignment.input_idx];
                let tagged_idx = ext_count as u16 | FLAT_CONT_EXT_SOURCE_BIT;
                assert!(
                    (ext_count as usize) < FLAT_CONT_MAX_EXT_SOURCES,
                    "flat round2: ext source overflow ({ext_count} >= {FLAT_CONT_MAX_EXT_SOURCES})",
                );
                *remap_slot = tagged_idx;
                desc.ext_sources[ext_count as usize] = GpuFlatContinuingSourceEntry {
                    previous_layer_start: if combined_first_access {
                        src.previous_layer_start as *const u8
                    } else {
                        std::ptr::null()
                    },
                    this_layer_cache_start: src.this_layer_start as *mut u8,
                };
                ext_count += 1;
            } else {
                let src = &kp.round2_prepared.base_field_inputs[assignment.input_idx];
                let tagged_idx = base_count as u16;
                assert!(
                    (base_count as usize) < FLAT_CONT_MAX_BASE_SOURCES,
                    "flat round2: base source overflow ({base_count} >= {FLAT_CONT_MAX_BASE_SOURCES})",
                );
                *remap_slot = tagged_idx;
                desc.base_sources[base_count as usize] = GpuFlatBaseAfterTwoSourceEntry {
                    base_input_start: src.base_input_start as *const u8,
                    this_layer_cache_start: src.this_layer_cache_start as *mut u8,
                    base_layer_half_size: src.base_layer_half_size,
                    base_quarter_size: src.base_quarter_size,
                    next_layer_size: src.next_layer_size,
                    first_access: combined_first_access,
                    source_kind: src.source_kind,
                };
                base_count += 1;
            }
        }
        desc.num_base_sources = base_count;
        desc.num_ext_sources = ext_count;
        desc.idx_remap = idx_remap;

        Some(desc)
    }

    /// Build flat continuation artifacts for round 3+ kernel dispatch.
    #[allow(clippy::type_complexity)]
    fn build_flat_continuation_artifacts(
        &self,
        _static_data: &[PreparedMainLayerKernelStaticData<E>],
        kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
        folding_steps: usize,
        _layer_idx: usize,
        _context: &ProverContext,
    ) -> CudaResult<(
        Option<flat::FlatContinuationBuildPlan<E>>,
        Vec<(
            usize,
            Box<[flat::GpuFlatContinuingSourceEntry; flat::FLAT_CONT_MAX_SOURCES]>,
        )>,
        Option<Box<crate::prover::gkr::eval_recipes::GpuFlatRecipeEvalDesc>>,
        usize,
        Callbacks<'static>,
    )> {
        use flat::{
            build_flat_continuation_plan, compile_recipes_for_device, GpuFlatContinuingSourceEntry,
            PreparedGateForFlatContinuationPlan, FLAT_CONT_CONST_MAX, FLAT_CONT_MAX_SOURCES,
        };

        // Use the first round 3 step's prepared storage to build the term arrays.
        // The term structure (which gates reference which sources) is the same across steps;
        // only the source pointers change per step.
        let first_step = 3;
        let gates: Vec<_> = kernel_plans
            .iter()
            .enumerate()
            .map(|(gate_idx, kp)| {
                let round3 = kp
                    .round3_and_beyond_prepared
                    .iter()
                    .find(|r| r.step == first_step)
                    .unwrap_or_else(|| panic!("missing round 3 prepared for step {first_step}"));
                PreparedGateForFlatContinuationPlan {
                    kind: kp.kind,
                    gate_idx,
                    base_inputs: &round3.prepared.base_field_inputs,
                    ext_inputs: &round3.prepared.extension_field_inputs,
                    batch_challenge_power_offset: kp.batch_challenge_offset as u32,
                    constraint_source: kp.constraint_metadata_source.as_ref(),
                }
            })
            .collect();
        let plan = build_flat_continuation_plan(&gates);
        let total = plan.total_coefficients();
        if total == 0 {
            return Ok((Some(plan), vec![], None, 0, Callbacks::new()));
        }

        // Compile one inline descriptor for the continuation eval-recipes launch.
        let compiled = compile_recipes_for_device(&plan.recipes);
        let cont_recipe_callbacks = Callbacks::new();
        assert!(
            total <= FLAT_CONT_CONST_MAX,
            "flat continuation: {} coefficients exceeds __constant__ limit of {}",
            total,
            FLAT_CONT_CONST_MAX,
        );

        // Build a key→source index map using round3 prepared cache pointers (same as plan).
        let round3_prepared = kernel_plans
            .iter()
            .map(|kp| {
                kp.round3_and_beyond_prepared
                    .iter()
                    .find(|r| r.step == first_step)
                    .unwrap_or_else(|| panic!("missing round 3 prepared for step {first_step}"))
            })
            .collect::<Vec<_>>();
        let mut key_map: std::collections::HashMap<(usize, bool), u32> =
            std::collections::HashMap::new();
        for assignment in &plan.source_assignments {
            let r3 = round3_prepared[assignment.gate_idx];
            let cache_ptr = if assignment.is_ext {
                r3.prepared.extension_field_inputs[assignment.input_idx].this_layer_start as usize
            } else {
                r3.prepared.base_field_inputs[assignment.input_idx].this_layer_start as usize
            };
            let key = (cache_ptr, assignment.is_ext);
            if let Some(prev) = key_map.insert(key, assignment.source_table_idx) {
                debug_assert_eq!(
                    prev, assignment.source_table_idx,
                    "flat round3: inconsistent source index for key"
                );
            }
        }

        // Build per-step source tables.
        let mut per_step_sources: Vec<(
            usize,
            Box<[GpuFlatContinuingSourceEntry; FLAT_CONT_MAX_SOURCES]>,
        )> = Vec::new();
        for step in first_step..folding_steps {
            let mut sources: Box<[GpuFlatContinuingSourceEntry; FLAT_CONT_MAX_SOURCES]> =
                Box::new([GpuFlatContinuingSourceEntry::default(); FLAT_CONT_MAX_SOURCES]);
            let mut source_first_access = vec![false; plan.term_desc.num_sources as usize];
            for (gate_idx, kp) in kernel_plans.iter().enumerate() {
                let round3 = kp
                    .round3_and_beyond_prepared
                    .iter()
                    .find(|r| r.step == step)
                    .unwrap_or_else(|| panic!("missing round 3 prepared for step {step}"));
                let r3_key = round3_prepared[gate_idx];
                for (input_idx, src) in round3.prepared.base_field_inputs.iter().enumerate() {
                    let key = (
                        r3_key.prepared.base_field_inputs[input_idx].this_layer_start as usize,
                        false,
                    );
                    if let Some(&idx) = key_map.get(&key) {
                        if src.first_access {
                            source_first_access[idx as usize] = true;
                        }
                    }
                }
                for (input_idx, src) in round3.prepared.extension_field_inputs.iter().enumerate() {
                    let key = (
                        r3_key.prepared.extension_field_inputs[input_idx].this_layer_start as usize,
                        true,
                    );
                    if let Some(&idx) = key_map.get(&key) {
                        if src.first_access {
                            source_first_access[idx as usize] = true;
                        }
                    }
                }
            }
            // Populate source entries for this step.
            for assignment in &plan.source_assignments {
                let round3 = kernel_plans[assignment.gate_idx]
                    .round3_and_beyond_prepared
                    .iter()
                    .find(|r| r.step == step)
                    .unwrap_or_else(|| panic!("missing round 3 prepared for step {step}"));
                let src_plan = if assignment.is_ext {
                    &round3.prepared.extension_field_inputs[assignment.input_idx]
                } else {
                    &round3.prepared.base_field_inputs[assignment.input_idx]
                };
                let combined_first_access =
                    source_first_access[assignment.source_table_idx as usize];
                sources[assignment.source_table_idx as usize] = GpuFlatContinuingSourceEntry {
                    previous_layer_start: if combined_first_access {
                        src_plan.previous_layer_start as *const u8
                    } else {
                        std::ptr::null()
                    },
                    this_layer_cache_start: src_plan.this_layer_start as *mut u8,
                };
            }
            per_step_sources.push((step, sources));
        }

        Ok((
            Some(plan),
            per_step_sources,
            Some(compiled.desc),
            compiled.num_recipes,
            cont_recipe_callbacks,
        ))
    }

    /// Test-only twin of [`prepare_next_layer_static`] that binds the
    /// per-layer batch challenge and lookup challenges directly into the
    /// kernel blueprints (the static form defers them).
    #[cfg(test)]
    pub(crate) fn prepare_next_layer(
        &mut self,
        batch_challenge_base: E,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRMainLayerSumcheckLayerPlan<E>>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };

        assert!(self.trace_len.is_power_of_two());
        let folding_steps = self.trace_len.trailing_zeros() as usize;
        assert!(folding_steps >= 4);

        let blueprints = super::super::tests::build_main_layer_kernel_blueprints(
            &layer,
            layer_idx,
            &self.storage,
            &self.external_challenges,
            &self.inits_and_teardowns_top_bits,
            self.inits_and_teardowns_address_high_bits_shift,
            batch_challenge_base,
            self.lookup_multiplicative_challenge,
            self.lookup_additive_challenge,
            self.num_base_layer_memory_polys,
            self.num_base_layer_witness_polys,
        );
        let plan = self.prepare_layer_from_blueprints(
            layer_idx,
            blueprints,
            Some(batch_challenge_base),
            context,
        )?;
        Ok(Some(plan))
    }

    pub(crate) fn prepare_next_layer_static(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRMainLayerSumcheckLayerPlan<E>>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };

        assert!(self.trace_len.is_power_of_two());
        let folding_steps = self.trace_len.trailing_zeros() as usize;
        assert!(folding_steps >= 4);

        let blueprints = build_main_layer_kernel_blueprints_static(
            &layer,
            layer_idx,
            &|addr| {
                // Universally base-field address kinds (trace-holder /
                // scratch / setup) classify as base regardless of which
                // logical layer the kernel runs at; the layout-driven
                // storage path (and forward-pass scratch hydration)
                // populates them at canonical layer 0 / their `layer`
                // field, not at the requesting `layer_idx`. Without
                // this, a `CopyIn{Base,Extension}Field` whose input got
                // rewritten to `ScratchSpace(K)` by
                // `normalize_compiled_circuit_for_gpu` would fall into
                // the ExtCopy branch and panic in
                // `get_for_sumcheck_round_0`'s extension lookup at line
                // 1973 (the value lives in `base_field_inputs`).
                if matches!(
                    addr,
                    GKRAddress::BaseLayerWitness(_)
                        | GKRAddress::BaseLayerMemory(_)
                        | GKRAddress::Setup(_)
                        | GKRAddress::ScratchSpace(_)
                ) {
                    return true;
                }
                self.storage.layers[layer_idx]
                    .base_field_inputs
                    .contains_key(addr)
            },
            &self.external_challenges,
            &self.inits_and_teardowns_top_bits,
            self.inits_and_teardowns_address_high_bits_shift,
            self.num_base_layer_memory_polys,
            self.num_base_layer_witness_polys,
        );
        Ok(Some(self.prepare_layer_from_blueprints(
            layer_idx, blueprints, None, context,
        )?))
    }
}
