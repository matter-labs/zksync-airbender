use std::sync::Arc;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;

use crate::{GpuBaseFieldSourceKind, GpuGKRStorage};

use super::super::kernels::*;
use super::super::{compact, flat};
use super::blueprints::{
    build_main_layer_kernel_blueprints_static, summarize_main_layer_constraint_metadata_source,
    PreparedMainLayerKernelStaticData,
};
use crate::upstream::{Field, FieldExtension, GKRAddress};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::BF;
use gpu_core::primitives::static_host::{alloc_static_pinned_box_uninit, StaticPinnedBox};
use gpu_cub::cub::device_reduce::{get_reduce_temp_storage_bytes, Reduce, ReduceOperation};
use gpu_cub::cub::CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2;
use gpu_prover_context::ProverContext;

/// H2D-upload a descriptor's overflowing term/tile tables into device buffers on
/// `exec_stream`. The copies precede all continuation kernels (which
/// launch later on the same stream). The pinned host sources are captured by a
/// keepalive callback scheduled onto `callbacks` (threaded into the
/// finish-retained keepalive bundle), so they outlive the async copies even
/// though the layer plan itself may drop right after scheduling. The returned
/// `FlatTermDeviceBuffers` owns the device allocations (stream-ordered drop) and
/// exposes the `GpuFlatTermTables` device pointers for the `_devptr_terms_`
/// kernels. Contents are bit-identical to the inline arrays.
fn upload_flat_term_tables(
    tables: &compact::FlatTermTablesHost,
    context: &ProverContext,
    callbacks: &mut Callbacks<'static>,
) -> CudaResult<FlatTermDeviceBuffers> {
    let stream = context.get_exec_stream();

    let terms_host = {
        let mut h = alloc_static_pinned_box_uninit::<flat::GpuFlatUnifiedTerm>(tables.terms.len())?;
        h.copy_from_slice(&tables.terms);
        Arc::new(h)
    };
    let tto_host = {
        let mut h = alloc_static_pinned_box_uninit::<u16>(tables.tile_term_offsets.len())?;
        h.copy_from_slice(&tables.tile_term_offsets);
        Arc::new(h)
    };
    let tfo_host = {
        let mut h = alloc_static_pinned_box_uninit::<u16>(tables.tile_fold_offsets.len())?;
        h.copy_from_slice(&tables.tile_fold_offsets);
        Arc::new(h)
    };

    let mut terms_dev = context
        .alloc::<flat::GpuFlatUnifiedTerm>(tables.terms.len(), AllocationPlacement::BestFit)?;
    let mut tto_dev =
        context.alloc::<u16>(tables.tile_term_offsets.len(), AllocationPlacement::BestFit)?;
    let mut tfo_dev =
        context.alloc::<u16>(tables.tile_fold_offsets.len(), AllocationPlacement::BestFit)?;

    memory_copy_async(&mut terms_dev, terms_host.as_ref(), stream)?;
    memory_copy_async(&mut tto_dev, tto_host.as_ref(), stream)?;
    memory_copy_async(&mut tfo_dev, tfo_host.as_ref(), stream)?;

    // Keep the pinned host sources alive until the copies complete. The closure
    // owns the Arcs (captured by move); the `let _ = &..` body is a no-op that
    // keeps it a `Fn`. It fires after the copies on the same stream and is
    // dropped with the keepalive bundle at finish (post-drain).
    let keepalive = (terms_host, tto_host, tfo_host);
    callbacks.schedule(
        move || {
            let _ = &keepalive;
        },
        stream,
    )?;

    let term_tables = compact::GpuFlatTermTables {
        terms: terms_dev.as_ptr(),
        tile_term_offsets: tto_dev.as_ptr(),
        tile_fold_offsets: tfo_dev.as_ptr(),
    };
    Ok(FlatTermDeviceBuffers {
        terms: terms_dev,
        tile_term_offsets: tto_dev,
        tile_fold_offsets: tfo_dev,
        tables: term_tables,
    })
}

/// Stage one recipe-eval table for H2D upload on `stream`. Returns the pinned
/// host source (kept for keepalive) and its device buffer. An empty table gets a
/// 1-element placeholder device buffer and no host copy: the `_devptr`
/// eval-recipes kernels never index an empty table (a 0-count prefactor group or
/// 0-monomial immediate is skipped before any load), so the placeholder is never
/// dereferenced. `alloc_static_pinned_box_uninit` requires a non-empty length, so
/// the empty case must skip it.
type StagedRecipeTable<T> = (Option<Arc<StaticPinnedBox<T>>>, DeviceAllocation<T>);

fn stage_recipe_table<T: Copy>(
    src: &[T],
    context: &ProverContext,
    stream: &era_cudart::stream::CudaStream,
) -> CudaResult<StagedRecipeTable<T>> {
    if src.is_empty() {
        return Ok((None, context.alloc::<T>(1, AllocationPlacement::BestFit)?));
    }
    let mut host = alloc_static_pinned_box_uninit::<T>(src.len())?;
    host.copy_from_slice(src);
    let host = Arc::new(host);
    let mut dev = context.alloc::<T>(src.len(), AllocationPlacement::BestFit)?;
    memory_copy_async(&mut dev, host.as_ref(), stream)?;
    Ok((Some(host), dev))
}

/// H2D-upload a compiled recipe descriptor's overflowing recipe/term/immediate
/// tables into device buffers on `exec_stream`. Mirrors
/// `upload_flat_term_tables`: pinned host sources are async-copied to device
/// buffers, then retained by a keepalive callback until the copies complete (the
/// layer plan itself may drop right after scheduling). The returned
/// `RecipeEvalDeviceBuffers` owns the device allocations (stream-ordered drop)
/// and exposes the `GpuFlatRecipeEvalDescDevptr` device pointers for the
/// `_devptr` eval-recipes kernels. Contents are bit-identical to the inline arrays.
fn upload_recipe_eval_arrays(
    arrays: &crate::eval_recipes::RecipeEvalHostArrays,
    context: &ProverContext,
    callbacks: &mut Callbacks<'static>,
) -> CudaResult<RecipeEvalDeviceBuffers> {
    use crate::eval_recipes::GpuFlatRecipeEvalDescDevptr;
    let stream = context.get_exec_stream();

    let (headers_host, headers_dev) = stage_recipe_table(&arrays.headers, context, stream)?;
    let (terms_host, terms_dev) = stage_recipe_table(&arrays.terms, context, stream)?;
    let (irec_host, irec_dev) = stage_recipe_table(&arrays.immediate_recipes, context, stream)?;
    let (imon_host, imon_dev) = stage_recipe_table(&arrays.immediate_monomials, context, stream)?;

    // Keep the pinned host sources alive until the copies complete (same pattern
    // as `upload_flat_term_tables`). Empty arrays contributed no host buffer.
    let keepalive = (headers_host, terms_host, irec_host, imon_host);
    callbacks.schedule(
        move || {
            let _ = &keepalive;
        },
        stream,
    )?;

    let desc = GpuFlatRecipeEvalDescDevptr {
        headers: headers_dev.as_ptr(),
        terms: terms_dev.as_ptr(),
        immediate_recipes: irec_dev.as_ptr(),
        immediate_monomials: imon_dev.as_ptr(),
    };
    Ok(RecipeEvalDeviceBuffers {
        headers: headers_dev,
        terms: terms_dev,
        immediate_recipes: irec_dev,
        immediate_monomials: imon_dev,
        desc,
    })
}

impl<E: Field + FieldExtension<BF>> GpuGKRMainLayerBackwardState<E> {
    pub fn storage(&self) -> &GpuGKRStorage<BF, E> {
        &self.storage
    }
    #[doc(hidden)]
    pub fn storage_mut(&mut self) -> &mut GpuGKRStorage<BF, E> {
        &mut self.storage
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::backward) struct FlatContinuationLaunchSizes {
    pub(super) fold_stride: u32,
    pub(super) next_layer_size: u32,
}

impl FlatContinuationLaunchSizes {
    pub(in crate::backward) fn from_sizes(fold_stride: usize, next_layer_size: usize) -> Self {
        assert!(
            fold_stride <= u32::MAX as usize && next_layer_size <= u32::MAX as usize,
            "flat continuation: fold sizes overflow u32 (fold_stride={fold_stride}, next_layer_size={next_layer_size})",
        );
        Self {
            fold_stride: fold_stride as u32,
            next_layer_size: next_layer_size as u32,
        }
    }

    pub(super) fn from_acc_size(acc_size: usize) -> Self {
        Self::from_sizes(2 * acc_size, acc_size)
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

        let mut static_data = Vec::with_capacity(blueprints.len());
        let mut kernel_plans = Vec::with_capacity(blueprints.len());
        for (blueprint, round0_descriptors_for_kernel) in blueprints
            .into_iter()
            .zip(round0_descriptors.iter().cloned())
        {
            let constraint_metadata_summary = summarize_main_layer_constraint_metadata_source(
                blueprint.constraint_metadata_source.as_ref(),
            );
            static_data.push(PreparedMainLayerKernelStaticData {
                kind: blueprint.kind,
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
            });
        }

        // Build the flat round 0 plan in compact form directly. The builder
        // resolves each gate's source pointers against the per-(layer, class)
        // consolidated storage backings and emits packed `u16` source
        // descriptors as it walks the gates.
        let flat_round0_template_compact: Option<compact::FlatRound0BuildPlan> = {
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

        // Compile one descriptor for the round-0 eval-recipes launch.
        let mut recipe_callbacks = Callbacks::new();
        let (
            flat_recipe_desc,
            flat_recipe_desc_device,
            flat_recipe_count,
            flat_coeff_device_buf,
            flat_use_constant,
        ) = if let Some(ref plan) = flat_round0_template_compact {
            let total = plan.total_coefficients();
            if total > 0 {
                let compiled = flat::compile_recipes_for_device(&plan.recipes);
                // Use the __constant__ coefficient symbol only when the
                // coefficient count actually fits it; otherwise fall back to
                // the device-buffer path (`coeff_loader_ptr`) so large
                // delegations (keccak_special5, bigint) whose round-0
                // coefficient count exceeds FLAT_CONST_MAX can still prove.
                // The pre-existing delegation-layer-0 exclusion is preserved.
                // Circuits that fit keep the perf-preferred __constant__/LDC
                // broadcast placement.
                let use_constant =
                    (!self.is_delegation || layer_idx != 0) && total <= flat::FLAT_CONST_MAX;
                if use_constant {
                    assert!(
                        total <= flat::FLAT_CONST_MAX,
                        "flat round 0: {} coefficients exceeds __constant__ limit of {}",
                        total,
                        flat::FLAT_CONST_MAX,
                    );
                }
                let coeff_buf = if use_constant {
                    None // eval_recipes writes directly to __constant__ symbol
                } else {
                    Some(context.alloc(total, AllocationPlacement::BestFit)?)
                };
                // When the recipe/term/immediate tables overflow the
                // inline `GpuFlatRecipeEvalDesc` caps (e.g. bigint's 3006 recipes),
                // upload them to device buffers and dispatch the `_devptr`
                // eval-recipes kernel; otherwise keep the inline descriptor. This
                // is independent of the `use_constant` coefficient-placement choice.
                let (recipe_desc, recipe_desc_device) =
                    if let Some(ref arrays) = compiled.device_arrays {
                        (
                            None,
                            Some(upload_recipe_eval_arrays(
                                arrays,
                                context,
                                &mut recipe_callbacks,
                            )?),
                        )
                    } else {
                        (Some(compiled.desc), None)
                    };
                (
                    recipe_desc,
                    recipe_desc_device,
                    compiled.num_recipes,
                    coeff_buf,
                    use_constant,
                )
            } else {
                (None, None, 0, None, true)
            }
        } else {
            (None, None, 0, None, true)
        };

        let max_acc_size = self.trace_len / 2;
        let reduction_temp_storage_bytes =
            get_reduce_temp_storage_bytes::<E>(ReduceOperation::Sum, max_acc_size as i32)?;
        let partials_len = super::super::kernels::max_partials_len(max_acc_size);
        let partials = context.alloc(partials_len, AllocationPlacement::Top)?;
        let round_scratch = GpuGKRMainLayerRoundScratch {
            eq_low_group: context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)?,
            accumulator: context.alloc(max_acc_size * 2, AllocationPlacement::Top)?,
            reduction_output: context.alloc(2, AllocationPlacement::Top)?,
            reduction_temp_storage: context
                .alloc_with_extra_alignment::<u8, CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2>(
                    reduction_temp_storage_bytes,
                    AllocationPlacement::Top,
                )?,
            partials,
        };

        // --- Build flat continuation plan for rounds 1+ ---
        let (
            flat_continuation_plan,
            flat_cont_recipe_desc,
            flat_cont_recipe_desc_device,
            flat_cont_recipe_count,
            cont_recipe_callbacks,
            flat_cont_coeff_device_buf,
            flat_cont_use_constant,
        ) = self.build_flat_continuation_artifacts(
            &static_data,
            &kernel_plans,
            folding_steps,
            layer_idx,
            context,
        )?;
        recipe_callbacks.extend(cont_recipe_callbacks);

        let flat_round1_desc = Self::build_flat_round1_desc(
            flat_continuation_plan.as_ref(),
            &kernel_plans,
            &self.storage,
        );
        let flat_round2_desc = Self::build_flat_round2_desc(
            flat_continuation_plan.as_ref(),
            &kernel_plans,
            &self.storage,
        );
        let round1_stride = (self.trace_len / 2).trailing_zeros();
        let round2_stride = (self.trace_len / 4).trailing_zeros();

        // Build structural compact descriptors. Their destination slots are
        // rebound to round-local arenas immediately before each launch.
        // Each unified-desc builder returns `(inline_desc, Option<term tables>)`.
        // `Some` means the term/tile count overflows the inline __grid_constant__
        // cap → device-terms path: derive the `_devptr` companion desc
        // and H2D-upload the term/tile tables into device buffers.
        let mut flat_round1_terms_device = None;
        let flat_round1_unified_desc_compact = if let (Some(ref r1_desc), Some(plan)) =
            (&flat_round1_desc, flat_continuation_plan.as_ref())
        {
            let (desc, tables) = compact::build_flat_round1_unified_desc::<E>(
                r1_desc,
                plan,
                &self.storage,
                compact::FoldingArenaBinding::new(1usize as *const u8, round1_stride),
                compact::FoldingArenaBinding::new(2usize as *const u8, round1_stride),
            );
            if let Some(tables) = tables {
                let devptr = Box::new(desc.to_devptr());
                let bufs = upload_flat_term_tables(&tables, context, &mut recipe_callbacks)?;
                flat_round1_terms_device = Some((devptr, bufs));
            }
            Some(desc)
        } else {
            None
        };
        let mut flat_round2_terms_device = None;
        let flat_round2_unified_desc_compact = if let (Some(ref r2_desc), Some(plan)) =
            (&flat_round2_desc, flat_continuation_plan.as_ref())
        {
            let (desc, tables) = compact::build_flat_round2_unified_desc::<E>(
                r2_desc,
                plan,
                &self.storage,
                compact::FoldingArenaBinding::new(1usize as *const u8, round1_stride),
                compact::FoldingArenaBinding::new(2usize as *const u8, round2_stride),
            );
            if let Some(tables) = tables {
                let devptr = Box::new(desc.to_devptr());
                let bufs = upload_flat_term_tables(&tables, context, &mut recipe_callbacks)?;
                flat_round2_terms_device = Some((devptr, bufs));
            }
            Some(desc)
        } else {
            None
        };
        let mut flat_continuation_terms_device: Vec<(
            usize,
            Box<compact::GpuFlatContinuationUnifiedDescDevptr>,
            FlatTermDeviceBuffers,
        )> = Vec::new();
        let flat_continuation_unified_descs_compact: Vec<(
            usize,
            Box<compact::GpuFlatContinuationUnifiedDesc>,
        )> = if let Some(ref plan) = flat_continuation_plan {
            let mut out = Vec::with_capacity(folding_steps.saturating_sub(3));
            for step in 3..folding_steps {
                let (desc, tables) = compact::build_flat_continuation_unified_desc(plan);
                if let Some(tables) = tables {
                    let devptr = Box::new(desc.to_devptr());
                    let bufs = upload_flat_term_tables(&tables, context, &mut recipe_callbacks)?;
                    flat_continuation_terms_device.push((step, devptr, bufs));
                }
                out.push((step, desc));
            }
            out
        } else {
            Vec::new()
        };

        // Coupling: the `_devptr_terms_` kernels always read
        // coefficients from the device buffer (never __constant__), so any
        // term-device descriptor forces the continuation coefficient path to
        // device too. When coefficients already overflowed, this is a no-op
        // (the buffer + `false` flag are already set).
        let any_terms_device = flat_round1_terms_device.is_some()
            || flat_round2_terms_device.is_some()
            || !flat_continuation_terms_device.is_empty();
        let (flat_cont_use_constant, flat_cont_coeff_device_buf) =
            if any_terms_device && flat_cont_use_constant {
                let total = flat_continuation_plan
                    .as_ref()
                    .map(|p| p.total_coefficients())
                    .unwrap_or(0);
                (
                    false,
                    Some(context.alloc(total, AllocationPlacement::BestFit)?),
                )
            } else {
                (flat_cont_use_constant, flat_cont_coeff_device_buf)
            };

        if std::env::var("GPU_PROVER_DUMP_FLAT_PLAN").is_ok() {
            flat::dump_flat_round1_plan(
                layer_idx,
                flat_round1_desc.as_deref(),
                flat_continuation_plan.as_ref(),
                &kernel_plans,
            );
        }

        let mut folding_evaluation_sources = std::collections::BTreeMap::new();
        if let Some(plan) = flat_continuation_plan.as_ref() {
            let canonicalize = |address: GKRAddress| {
                self.storage
                    .layout
                    .as_ref()
                    .and_then(|layout| layout.aliases.get(&address))
                    .copied()
                    .unwrap_or(address)
            };
            let mut source_indices = std::collections::HashMap::new();
            for assignment in &plan.source_assignments {
                let address = if assignment.is_ext {
                    kernel_plans[assignment.gate_idx].inputs.inputs_in_extension
                        [assignment.input_idx]
                } else {
                    kernel_plans[assignment.gate_idx].inputs.inputs_in_base[assignment.input_idx]
                };
                source_indices.insert(
                    (canonicalize(address), assignment.is_ext),
                    assignment.source_table_idx as u16,
                );
            }
            let logicalize = |address| {
                self.storage
                    .layout
                    .as_ref()
                    .map(|layout| {
                        crate::transform::logical_protocol_address(
                            address,
                            &layout.scratch_space_mapping_rev,
                        )
                    })
                    .unwrap_or(address)
            };
            for kernel in &kernel_plans {
                for (address, is_ext) in kernel
                    .inputs
                    .inputs_in_base
                    .iter()
                    .map(|address| (*address, false))
                    .chain(
                        kernel
                            .inputs
                            .inputs_in_extension
                            .iter()
                            .map(|address| (*address, true)),
                    )
                {
                    if address == GKRAddress::placeholder() {
                        continue;
                    }
                    if let Some(&source_idx) = source_indices.get(&(canonicalize(address), is_ext))
                    {
                        folding_evaluation_sources.insert(logicalize(address), source_idx);
                    }
                }
            }
        }

        // All storage resolution (compact descriptors + round0..round3 prepared
        // pointers) is complete above. From here the kernel input/output
        // addresses are consumed only as *protocol/claim identity*
        // (`final_evaluation_sources_for_last_step` keys → transcript order +
        // proof addresses, and `claim_idx(output)` lookups). Map any scratch
        // storage alias back to its logical `InnerLayer` identity so those match
        // the CPU verifier; storage/execution keep the `ScratchSpace` alias.
        // No-op for circuits without scratch-backed claimed values. See
        // `transform::logical_protocol_address`.
        if let Some(layout) = self.storage.layout.as_ref() {
            let rev = &layout.scratch_space_mapping_rev;
            if !rev.is_empty() {
                for kp in kernel_plans.iter_mut() {
                    for addr in kp
                        .inputs
                        .inputs_in_base
                        .iter_mut()
                        .chain(kp.inputs.inputs_in_extension.iter_mut())
                        .chain(kp.inputs.outputs_in_base.iter_mut())
                        .chain(kp.inputs.outputs_in_extension.iter_mut())
                    {
                        *addr = crate::transform::logical_protocol_address(*addr, rev);
                    }
                }
            }
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
            flat_recipe_desc_device,
            flat_recipe_count,
            flat_coeff_device_buf,
            flat_use_constant,
            flat_cont_coeff_device_buf,
            flat_cont_use_constant,
            flat_continuation_plan,
            folding_evaluation_sources: folding_evaluation_sources.into_iter().collect(),
            flat_cont_recipe_desc,
            flat_cont_recipe_desc_device,
            flat_cont_recipe_count,
            flat_continuation_unified_descs_compact,
            flat_round1_unified_desc_compact,
            flat_round2_unified_desc_compact,
            flat_round1_terms_device,
            flat_round2_terms_device,
            flat_continuation_terms_device,
            round_scratch,
            recipe_upload_callbacks: recipe_callbacks,
            eq_sizes: GkrEqSizes::zeroed(),
        })
    }

    fn build_flat_round1_desc(
        plan: Option<&flat::FlatContinuationBuildPlan>,
        kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
        storage: &GpuGKRStorage<BF, E>,
    ) -> Option<Box<flat::Round1FusedSources>> {
        use flat::{
            GpuFlatBaseAfterOneSourceEntry, GpuFlatContinuingSourceEntry, Round1FusedSources,
            FLAT_CONT_EXT_SOURCE_BIT, FLAT_CONT_MAX_BASE_SOURCES, FLAT_CONT_MAX_EXT_SOURCES,
        };

        let plan = plan?;
        let mut desc = Box::new(Round1FusedSources::default());
        let mut idx_remap = vec![u16::MAX; plan.term_desc.num_sources as usize];

        for assignment in &plan.source_assignments {
            let address = if assignment.is_ext {
                kernel_plans[assignment.gate_idx].inputs.inputs_in_extension[assignment.input_idx]
            } else {
                kernel_plans[assignment.gate_idx].inputs.inputs_in_base[assignment.input_idx]
            };
            let address = storage
                .layout
                .as_ref()
                .and_then(|layout| layout.aliases.get(&address))
                .copied()
                .unwrap_or(address);

            if assignment.is_ext {
                let idx = desc.num_ext_sources as usize;
                assert!(idx < FLAT_CONT_MAX_EXT_SOURCES);
                let poly = storage
                    .get_ext_poly_for_address(address)
                    .expect("flat round 1 extension source must exist");
                desc.ext_sources[idx] = GpuFlatContinuingSourceEntry {
                    previous_layer_start: poly.as_ptr() as *const u8,
                    this_layer_cache_start: std::ptr::null_mut(),
                };
                idx_remap[assignment.source_table_idx as usize] =
                    idx as u16 | FLAT_CONT_EXT_SOURCE_BIT;
                desc.num_ext_sources += 1;
            } else {
                let idx = desc.num_base_sources as usize;
                assert!(idx < FLAT_CONT_MAX_BASE_SOURCES);
                let (base_len, base_ptr, source_kind) =
                    if let Some(kind) = GpuBaseFieldSourceKind::from_address(address) {
                        (storage.base_trace_len(), std::ptr::null(), kind)
                    } else {
                        let poly = storage
                            .get_base_poly_for_address(address)
                            .expect("flat round 1 base source must exist");
                        (
                            poly.len(),
                            poly.as_ptr() as *const u8,
                            GpuBaseFieldSourceKind::Real,
                        )
                    };
                desc.base_sources[idx] = GpuFlatBaseAfterOneSourceEntry {
                    base_layer_half_size: base_len / 2,
                    next_layer_size: base_len / 4,
                    base_input_start: base_ptr,
                    this_layer_cache_start: std::ptr::null_mut(),
                    first_access: true,
                    source_kind,
                };
                idx_remap[assignment.source_table_idx as usize] = idx as u16;
                desc.num_base_sources += 1;
            }
        }
        desc.idx_remap = idx_remap;
        Some(desc)
    }

    fn build_flat_round2_desc(
        plan: Option<&flat::FlatContinuationBuildPlan>,
        kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
        storage: &GpuGKRStorage<BF, E>,
    ) -> Option<Box<flat::Round2FusedSources>> {
        use flat::{
            GpuFlatBaseAfterTwoSourceEntry, GpuFlatContinuingSourceEntry, Round2FusedSources,
            FLAT_CONT_EXT_SOURCE_BIT, FLAT_CONT_MAX_BASE_SOURCES, FLAT_CONT_MAX_EXT_SOURCES,
        };

        let plan = plan?;
        let mut desc = Box::new(Round2FusedSources::default());
        let mut idx_remap = vec![u16::MAX; plan.term_desc.num_sources as usize];

        for assignment in &plan.source_assignments {
            let address = if assignment.is_ext {
                kernel_plans[assignment.gate_idx].inputs.inputs_in_extension[assignment.input_idx]
            } else {
                kernel_plans[assignment.gate_idx].inputs.inputs_in_base[assignment.input_idx]
            };
            let address = storage
                .layout
                .as_ref()
                .and_then(|layout| layout.aliases.get(&address))
                .copied()
                .unwrap_or(address);
            let source_idx = assignment.source_table_idx as u16;

            if assignment.is_ext {
                let idx = desc.num_ext_sources as usize;
                assert!(idx < FLAT_CONT_MAX_EXT_SOURCES);
                desc.ext_sources[idx] = GpuFlatContinuingSourceEntry::default();
                desc.ext_source_indices.push(source_idx);
                idx_remap[source_idx as usize] = idx as u16 | FLAT_CONT_EXT_SOURCE_BIT;
                desc.num_ext_sources += 1;
            } else {
                let idx = desc.num_base_sources as usize;
                assert!(idx < FLAT_CONT_MAX_BASE_SOURCES);
                let (base_len, base_ptr, source_kind) =
                    if let Some(kind) = GpuBaseFieldSourceKind::from_address(address) {
                        (storage.base_trace_len(), std::ptr::null(), kind)
                    } else {
                        let poly = storage
                            .get_base_poly_for_address(address)
                            .expect("flat round 2 base source must exist");
                        (
                            poly.len(),
                            poly.as_ptr() as *const u8,
                            GpuBaseFieldSourceKind::Real,
                        )
                    };
                desc.base_sources[idx] = GpuFlatBaseAfterTwoSourceEntry {
                    base_input_start: base_ptr,
                    this_layer_cache_start: std::ptr::null_mut(),
                    base_layer_half_size: base_len / 2,
                    base_quarter_size: base_len / 4,
                    next_layer_size: base_len / 8,
                    first_access: true,
                    source_kind,
                };
                desc.base_source_indices.push(source_idx);
                idx_remap[source_idx as usize] = idx as u16;
                desc.num_base_sources += 1;
            }
        }
        desc.idx_remap = idx_remap;
        Some(desc)
    }

    /// Build flat continuation artifacts for round 3+ kernel dispatch.
    #[allow(clippy::type_complexity)]
    fn build_flat_continuation_artifacts(
        &self,
        _static_data: &[PreparedMainLayerKernelStaticData<E>],
        kernel_plans: &[GpuGKRMainLayerKernelPlan<E>],
        _folding_steps: usize,
        _layer_idx: usize,
        context: &ProverContext,
    ) -> CudaResult<(
        Option<flat::FlatContinuationBuildPlan>,
        Option<Box<crate::eval_recipes::GpuFlatRecipeEvalDesc>>,
        // Device-recipes path for the continuation phase. `Some` iff the
        // recipe tables overflow the inline caps (mutually exclusive with the
        // inline desc above).
        Option<RecipeEvalDeviceBuffers>,
        usize,
        Callbacks<'static>,
        // Continuation coeff device buffer (None => __constant__ path) and the
        // use-constant flag. Mirror of the round-0 `flat_coeff_device_buf` /
        // `flat_use_constant` pair.
        Option<DeviceAllocation<E>>,
        bool,
    )> {
        use flat::{
            build_flat_continuation_plan, compile_recipes_for_device,
            PreparedGateForFlatContinuationPlan, FLAT_CONST_MAX,
        };

        let aliases = self.storage.layout.as_ref().map(|layout| &layout.aliases);
        let canonicalize = |address: GKRAddress| {
            aliases
                .and_then(|aliases| aliases.get(&address))
                .copied()
                .unwrap_or(address)
        };
        let canonical_base_addresses: Vec<Vec<GKRAddress>> = kernel_plans
            .iter()
            .map(|kp| {
                kp.inputs
                    .inputs_in_base
                    .iter()
                    .copied()
                    .map(canonicalize)
                    .collect()
            })
            .collect();
        let canonical_ext_addresses: Vec<Vec<GKRAddress>> = kernel_plans
            .iter()
            .map(|kp| {
                kp.inputs
                    .inputs_in_extension
                    .iter()
                    .copied()
                    .map(canonicalize)
                    .collect()
            })
            .collect();
        let gates: Vec<_> = kernel_plans
            .iter()
            .enumerate()
            .map(|(gate_idx, kp)| PreparedGateForFlatContinuationPlan {
                kind: kp.kind,
                gate_idx,
                base_addresses: &canonical_base_addresses[gate_idx],
                ext_addresses: &canonical_ext_addresses[gate_idx],
                batch_challenge_power_offset: kp.batch_challenge_offset as u32,
                constraint_source: kp.constraint_metadata_source.as_ref(),
            })
            .collect();
        let plan = build_flat_continuation_plan(&gates);
        let total = plan.total_coefficients();
        if total == 0 {
            return Ok((Some(plan), None, None, 0, Callbacks::new(), None, true));
        }

        // Compile one descriptor for the continuation eval-recipes launch.
        let compiled = compile_recipes_for_device(&plan.recipes);
        let mut cont_recipe_callbacks = Callbacks::new();
        // Overflowing continuation recipe tables go to device buffers
        // (dispatched via the `_devptr` eval-recipes kernel); otherwise the inline
        // descriptor is used. Mirror of the round-0 recipe-desc split.
        let (flat_cont_recipe_desc, flat_cont_recipe_desc_device) =
            if let Some(ref arrays) = compiled.device_arrays {
                (
                    None,
                    Some(upload_recipe_eval_arrays(
                        arrays,
                        context,
                        &mut cont_recipe_callbacks,
                    )?),
                )
            } else {
                (Some(compiled.desc), None)
            };
        // Use the __constant__ coefficient symbol only when the continuation
        // coefficient count actually fits it; otherwise fall back to the
        // device-buffer path (`coeff_loader_ptr_indexed`) so large delegations
        // (keccak_special5, bigint) whose continuation coefficient count exceeds
        // FLAT_CONST_MAX can still prove. Circuits that fit keep the perf-preferred
        // __constant__/LDC broadcast placement. Mirrors the round-0 policy flip.
        let cont_use_constant = total <= FLAT_CONST_MAX;
        if cont_use_constant {
            assert!(
                total <= FLAT_CONST_MAX,
                "flat continuation: {} coefficients exceeds __constant__ limit of {}",
                total,
                FLAT_CONST_MAX,
            );
        }
        let flat_cont_coeff_device_buf = if cont_use_constant {
            None // eval_recipes writes directly to __constant__ symbol
        } else {
            Some(context.alloc(total, AllocationPlacement::BestFit)?)
        };

        Ok((
            Some(plan),
            flat_cont_recipe_desc,
            flat_cont_recipe_desc_device,
            compiled.num_recipes,
            cont_recipe_callbacks,
            flat_cont_coeff_device_buf,
            cont_use_constant,
        ))
    }

    /// Test-only twin of [`prepare_next_layer_static`] that binds the
    /// per-layer batch challenge and lookup challenges directly into the
    /// kernel blueprints (the static form defers them).
    pub fn prepare_next_layer(
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

        let blueprints = super::blueprints_dynamic::build_main_layer_kernel_blueprints(
            &layer,
            layer_idx,
            &self.storage,
            &self.external_challenges,
            &self.inits_and_teardowns_top_bits,
            self.inits_and_teardowns_address_high_bits_shift,
            batch_challenge_base,
            self.lookup_multiplicative_challenge,
            self.lookup_additive_challenge,
        );
        let plan = self.prepare_layer_from_blueprints(
            layer_idx,
            blueprints,
            Some(batch_challenge_base),
            context,
        )?;
        Ok(Some(plan))
    }

    pub fn prepare_next_layer_static(
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
        );
        Ok(Some(self.prepare_layer_from_blueprints(
            layer_idx, blueprints, None, context,
        )?))
    }
}
