use era_cudart::result::CudaResult;

use crate::upstream::GKRAddress;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_prover_context::ProverContext;

use super::super::kernels::*;
use super::super::main_continuation::MainContinuationWindowSequence;
use super::super::window::binding::{
    window_partials_len, WindowRuntimeScratch, BWD_WINDOW_COORDINATES,
};
use crate::{BackwardExecutionStrategy, GkrBackwardOptions};

impl GpuGKRMainLayerBackwardState {
    fn prepare_layer(
        &mut self,
        layer_idx: usize,
        options: GkrBackwardOptions,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRMainLayerSumcheckLayerPlan> {
        let folding_steps = self.trace_len.trailing_zeros() as usize;
        let layer_plan = &self.programs.backward_layers[layer_idx];
        let main_execution_plan = super::execution_plan::try_derive_main_layer_execution_plan(
            options,
            self.strategy,
            folding_steps,
            super::execution_plan::MainTailRoundBudget::AtLeast {
                min_tail_rounds: super::execution_plan::LEGACY_MAIN_TAIL_MIN_ROUNDS,
            },
        )
        .unwrap_or_else(|error| {
            panic!("main-layer execution plan for layer {layer_idx}: {error:?}")
        });
        if main_execution_plan.window_count() > 0 {
            assert_eq!(
                self.strategy,
                BackwardExecutionStrategy::WindowedR0,
                "continuation windows require the landed windowed R0 arm"
            );
            assert!(
                self.programs.main_continuation_window_programs_ready(),
                "continuation scheduling requires an accepted preflight bundle"
            );
        }

        // Both arms publish into the same buffer, so it holds whichever layout is
        // larger: the per-round warp partials, or the window producer's row-tile-
        // major tensor plus the split tail arm's reduction target.
        let partials_len = super::super::kernels::max_partials_len(self.trace_len / 2)
            .max(window_partials_len(self.trace_len));
        let mut round_scratch = GpuGKRMainLayerRoundScratch {
            eq_low_group: context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)?,
            partials: context.alloc(partials_len, AllocationPlacement::Top)?,
        };
        assert!(
            round_scratch.partials.len() >= window_partials_len(self.trace_len),
            "the shared partials buffer cannot hold the window producer's tensor"
        );

        // The arm selects both the rounds-0-2 binding and where the
        // continuation sequence starts: after round 0 for the per-round arm,
        // after the window's three rounds for the windowed arm.
        let (bwd_vm_r0, ext_start_round) = match self.strategy {
            BackwardExecutionStrategy::PerRound => {
                let round0 = super::super::vm::production_bind::build_bwd_vm_round0(
                    &self.storage,
                    self.programs.r0_layer(layer_idx),
                    1usize << (folding_steps - 1),
                    round_scratch.eq_low_group.as_ptr(),
                    make_eq_sizes(folding_steps - 1),
                    round_scratch.partials.as_mut_ptr(),
                    &self.inits_and_teardowns_top_bits,
                    context,
                )?;
                (MainLayerR0Binding::PerRound(round0), 1u8)
            }
            BackwardExecutionStrategy::WindowedR0 => {
                let program = self.programs.window_layer(layer_idx);
                let bank = super::super::vm::production_bind::build_bwd_vm_window_bank(
                    program,
                    &self.inits_and_teardowns_top_bits,
                    context,
                )?;
                let window = super::super::window::binding::bind_window_launch(
                    program,
                    &self.storage,
                    folding_steps,
                    WindowRuntimeScratch {
                        eq_low: round_scratch.eq_low_group.as_ptr(),
                        partials: round_scratch.partials.as_mut_ptr(),
                        partials_capacity: round_scratch.partials.len(),
                    },
                )
                .unwrap_or_else(|error| {
                    panic!("windowed R0 binding for layer {layer_idx}: {error:?}")
                });
                (
                    MainLayerR0Binding::Windowed(WindowedR0Launch {
                        bank,
                        window,
                        tail_arm: self.window_tail,
                    }),
                    BWD_WINDOW_COORDINATES as u8,
                )
            }
        };
        let bwd_vm_ext = if main_execution_plan.window_count() > 0 {
            super::super::vm::production_bind::build_bwd_vm_ext_rounds_after_continuations(
                &self.storage,
                self.programs.continuation_layer(layer_idx),
                main_execution_plan.tail_start_round(),
                folding_steps,
                round_scratch.eq_low_group.as_ptr(),
                round_scratch.partials.as_mut_ptr(),
                &self.inits_and_teardowns_top_bits,
                context,
            )?
        } else {
            super::super::vm::production_bind::build_bwd_vm_ext_rounds(
                &self.storage,
                self.programs.continuation_layer(layer_idx),
                ext_start_round,
                folding_steps,
                round_scratch.eq_low_group.as_ptr(),
                make_eq_sizes(folding_steps - usize::from(ext_start_round)),
                round_scratch.partials.as_mut_ptr(),
                &self.inits_and_teardowns_top_bits,
                context,
            )?
        };

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
        let folding_evaluation_sources = layer_plan
            .inputs
            .iter()
            .copied()
            .filter(|address| *address != GKRAddress::placeholder())
            .map(logicalize)
            .collect();
        let claim_terms = layer_plan
            .claims
            .iter()
            .map(|&(offset, address)| (offset, logicalize(address)))
            .collect();

        Ok(GpuGKRMainLayerSumcheckLayerPlan {
            layer_idx,
            folding_steps,
            claim_terms,
            folding_evaluation_sources,
            round_scratch,
            bwd_vm_r0,
            bwd_vm_ext,
            main_execution_plan,
            main_continuation: MainContinuationWindowSequence::new(
                main_execution_plan,
                layer_idx,
                self.programs.clone(),
            ),
            main_tail_program: Some(
                self.programs
                    .resolve_main_tail_programs()
                    .expect("main-tail preflight must complete before layer preparation")
                    .layers[layer_idx]
                    .clone(),
            ),
            main_tail_launched: None,
            main_chain_selected: true,
            eq_sizes: GkrEqSizes::zeroed(),
        })
    }

    pub(crate) fn prepare_next_layer_static(
        &mut self,
        options: GkrBackwardOptions,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRMainLayerSumcheckLayerPlan>> {
        let Some(layer_idx) = self.pending_layers.pop_front() else {
            return Ok(None);
        };

        assert!(self.trace_len.is_power_of_two());
        assert!(self.trace_len.trailing_zeros() >= 4);

        Ok(Some(self.prepare_layer(layer_idx, options, context)?))
    }
}

#[cfg(test)]
mod main_continuation_option_history {
    use std::collections::{BTreeMap, BTreeSet, VecDeque};
    use std::mem::size_of;
    use std::path::PathBuf;
    use std::sync::Arc;

    use era_cudart::memory::{memory_copy_async, memory_set_async};
    use era_cudart::slice::DeviceSlice;
    use gpu_core::allocator::tracker::AllocationPlacement;
    use gpu_core::primitives::context::DeviceAllocation;
    use gpu_core::primitives::field::{BF, E4};
    use gpu_gkr_compiler::LeanBoundWindow;
    use gpu_hash::blake2s::STATE_SIZE;
    use gpu_trace::witness::circuit_type::{CircuitType, DelegationCircuitType};

    use super::*;
    use crate::backward::main_layer::sumcheck_plan::{
        main_layer_ext_bank_fill_count_for_test, reset_main_layer_ext_bank_fill_count_for_test,
    };
    use crate::backward::vm::production_bind::family_read_place;
    use crate::forward::vm::lower::read_place_to_gkr_address;
    use crate::proof_layout::{
        BackwardLayerDims, ProofLayout, ProofLayoutInputs, WhirBaseLayerDims, WhirDims,
    };
    use crate::storage_types::{GpuBaseFieldPoly, GpuExtensionFieldPoly};
    use crate::test_utils::make_test_context;
    use crate::upstream::{Field, FieldExtension, FieldKind, GKRCircuitArtifact, PrimeField};
    use crate::{GkrPrograms, GpuGKRStorage, WindowTailArm};

    const SMOKE_FOLDING_STEPS: usize = 7;

    fn sample_e4(value: u32) -> E4 {
        E4::from_base(BF::from_u32_unchecked(value))
    }

    fn collect_raw_addresses(
        windows: &[LeanBoundWindow],
        base: &mut BTreeSet<crate::upstream::GKRAddress>,
        ext: &mut BTreeSet<crate::upstream::GKRAddress>,
    ) {
        for window in windows {
            let destinations = match window.backing_field() {
                FieldKind::Base => &mut *base,
                FieldKind::Ext => &mut *ext,
            };
            for column in &window.columns {
                if let Some(place) = family_read_place(window.family, column.column) {
                    destinations.insert(read_place_to_gkr_address(&place));
                }
            }
        }
    }

    fn storage_for_layer(
        programs: &GkrPrograms,
        layer_idx: usize,
        context: &ProverContext,
    ) -> GpuGKRStorage<BF, E4> {
        let trace_len = programs.runtime_circuit().trace_len;
        let mut base = BTreeSet::new();
        let mut ext = BTreeSet::new();
        collect_raw_addresses(
            &programs.r0_layer(layer_idx).binding.windows,
            &mut base,
            &mut ext,
        );
        collect_raw_addresses(
            &programs.continuation_layer(layer_idx).binding.windows,
            &mut base,
            &mut ext,
        );

        let mut storage = GpuGKRStorage::default();
        if !base.is_empty() {
            let mut backing = context
                .alloc(base.len() * trace_len, AllocationPlacement::Top)
                .unwrap();
            memory_set_async(
                unsafe { backing.transmute_mut::<u8>() },
                0,
                context.get_exec_stream(),
            )
            .unwrap();
            let backing = Arc::new(backing);
            for (rank, address) in base.into_iter().enumerate() {
                let layer = GpuGKRStorage::<BF, E4>::base_poly_layer(address)
                    .expect("a base source has a storage layer");
                storage.insert_base_field_at_layer(
                    layer,
                    address,
                    GpuBaseFieldPoly::from_arc(Arc::clone(&backing), rank * trace_len, trace_len),
                );
            }
        }
        if !ext.is_empty() {
            let mut backing = context
                .alloc(ext.len() * trace_len, AllocationPlacement::Top)
                .unwrap();
            memory_set_async(
                unsafe { backing.transmute_mut::<u8>() },
                0,
                context.get_exec_stream(),
            )
            .unwrap();
            let backing = Arc::new(backing);
            for (rank, address) in ext.into_iter().enumerate() {
                let layer = GpuGKRStorage::<BF, E4>::ext_poly_layer(address)
                    .expect("an extension source has a storage layer");
                storage.insert_extension_at_layer(
                    layer,
                    address,
                    GpuExtensionFieldPoly::from_arc(
                        Arc::clone(&backing),
                        rank * trace_len,
                        trace_len,
                    ),
                );
            }
        }
        storage
    }

    fn smoke_programs() -> Arc<GkrPrograms> {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../cs/compiled_circuits/blake2_with_extended_control_layout_gkr.json");
        let bytes = std::fs::read(&path)
            .unwrap_or_else(|error| panic!("reading {}: {error}", path.display()));
        let mut artifact: GKRCircuitArtifact<BF> = serde_json::from_slice(&bytes)
            .unwrap_or_else(|error| panic!("parsing {}: {error}", path.display()));
        artifact.trace_len = 1usize << SMOKE_FOLDING_STEPS;
        let programs = Arc::new(
            GkrPrograms::compile(
                CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression),
                Arc::new(artifact),
            )
            .expect("compile the reduced-trace full-layer smoke fixture"),
        );
        programs
            .resolve_window_programs()
            .expect("the smoke fixture requires windowed R0");
        programs
            .resolve_main_continuation_window_programs()
            .expect("the smoke fixture requires continuation windows");
        programs
    }

    fn smoke_layer(programs: &GkrPrograms) -> usize {
        let (_, extras) = programs.main_layer_layout_addresses();
        (0..programs.backward_layers.len())
            .rev()
            .find(|&layer_idx| {
                extras[layer_idx].is_empty()
                    && !programs.backward_layers[layer_idx].inputs.is_empty()
                    && !programs.backward_layers[layer_idx].claims.is_empty()
            })
            .expect("the smoke fixture needs a claimed layer without cached extras")
    }

    fn empty_whir_base_dims() -> WhirBaseLayerDims {
        WhirBaseLayerDims {
            num_columns: 0,
            cap_digest_count: 0,
            query_count: 0,
            leaf_values_len: 0,
            path_len: 0,
        }
    }

    fn smoke_proof_layout(programs: &GkrPrograms, layer_idx: usize) -> ProofLayout {
        let (inputs, extras) = programs.main_layer_layout_addresses();
        assert!(
            extras[layer_idx].is_empty(),
            "the isolated smoke does not synthesize cached-relation dependencies"
        );
        ProofLayout::new(&ProofLayoutInputs {
            output_evaluations: BTreeMap::new(),
            backward_layers: vec![BackwardLayerDims {
                layer_idx,
                sumcheck_num_rounds: SMOKE_FOLDING_STEPS,
                final_step_eval_addresses: inputs[layer_idx].clone(),
                final_step_eval_degree: 1,
                extra_evaluations_addresses: Vec::new(),
            }],
            whir: WhirDims {
                original_evaluation_point_len: 0,
                setup: empty_whir_base_dims(),
                memory: empty_whir_base_dims(),
                witness: empty_whir_base_dims(),
                intermediate: Vec::new(),
                num_ood_samples: 0,
                total_sumcheck_polys: 0,
                pow_rounds: 0,
                final_monomials_len: 0,
            },
        })
    }

    fn bytes_of<T>(values: &[T]) -> Vec<u8> {
        // SAFETY: the returned vector copies exactly the initialized host values.
        unsafe {
            std::slice::from_raw_parts(values.as_ptr().cast::<u8>(), std::mem::size_of_val(values))
                .to_vec()
        }
    }

    #[derive(Debug, PartialEq, Eq)]
    struct FullLayerSmokeOutput {
        coefficients: Vec<u8>,
        seed: Vec<u8>,
        claim: Vec<u8>,
        eq_prefactor: Vec<u8>,
        next_claim_point: Vec<u8>,
        next_claims: Vec<u8>,
    }

    fn run_full_layer_smoke(
        programs: Arc<GkrPrograms>,
        layer_idx: usize,
        windowed_main_continuations: bool,
        context: &ProverContext,
    ) -> FullLayerSmokeOutput {
        let options = GkrBackwardOptions {
            windowed_main_continuations,
            ..GkrBackwardOptions::default()
        };
        let mut state = state_for_layer(programs, layer_idx, context);
        let mut prepared = state
            .prepare_next_layer_static(options, context)
            .unwrap()
            .expect("the smoke fixture has one pending layer");
        assert_eq!(
            prepared.main_execution_plan.window_count() > 0,
            windowed_main_continuations,
            "the stored plan must be selected from the current proof option"
        );

        let claim_addresses = prepared
            .claim_terms
            .iter()
            .map(|&(_, address)| address)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let claim_layout = ClaimBufferLayout::from_addresses(claim_addresses);
        let mut device_claims: DeviceAllocation<E4> = context
            .alloc(claim_layout.claim_count(), AllocationPlacement::Top)
            .unwrap();
        let host_claims = (0..claim_layout.claim_count())
            .map(|idx| sample_e4(0x1000 + idx as u32))
            .collect::<Vec<_>>();
        memory_copy_async(&mut device_claims, &host_claims, context.get_exec_stream()).unwrap();

        let mut device_claim_point: DeviceAllocation<E4> = context
            .alloc(SMOKE_FOLDING_STEPS + 1, AllocationPlacement::Top)
            .unwrap();
        let host_claim_point = (0..=SMOKE_FOLDING_STEPS)
            .map(|idx| sample_e4(0x2000 + idx as u32))
            .collect::<Vec<_>>();
        memory_copy_async(
            &mut device_claim_point,
            &host_claim_point,
            context.get_exec_stream(),
        )
        .unwrap();

        let mut device_seed: DeviceAllocation<u32> =
            context.alloc(STATE_SIZE, AllocationPlacement::Top).unwrap();
        let host_seed = std::array::from_fn::<_, STATE_SIZE, _>(|idx| 0x3000 + idx as u32);
        memory_copy_async(&mut device_seed, &host_seed, context.get_exec_stream()).unwrap();

        let mut lookup_challenges: DeviceAllocation<E4> =
            context.alloc(2, AllocationPlacement::Top).unwrap();
        memory_copy_async(
            &mut lookup_challenges,
            &[sample_e4(0x4000), sample_e4(0x4001)],
            context.get_exec_stream(),
        )
        .unwrap();
        let mut external_challenges: DeviceAllocation<E4> = context
            .alloc(
                crate::upstream::GKRExternalChallenges::<BF, E4>::TOTAL_CHALLENGES,
                AllocationPlacement::Top,
            )
            .unwrap();
        let host_external = (0..external_challenges.len())
            .map(|idx| sample_e4(0x5000 + idx as u32))
            .collect::<Vec<_>>();
        memory_copy_async(
            &mut external_challenges,
            &host_external,
            context.get_exec_stream(),
        )
        .unwrap();

        let proof_layout = smoke_proof_layout(&state.programs, layer_idx);
        let mut proof_slab: DeviceAllocation<E4> = context
            .alloc(
                proof_layout.total_bytes / size_of::<E4>(),
                AllocationPlacement::Top,
            )
            .unwrap();
        memory_set_async(
            unsafe { proof_slab.transmute_mut::<u8>() },
            0,
            context.get_exec_stream(),
        )
        .unwrap();

        reset_main_layer_ext_bank_fill_count_for_test();
        let execution = prepared
            .schedule_execute_main_layer(
                device_seed,
                DeviceClaimPointAndBatching::from_allocation(device_claim_point),
                device_claims,
                &claim_layout,
                lookup_challenges.as_ptr(),
                external_challenges.as_ptr(),
                &proof_slab,
                &proof_layout,
                0,
                &mut state.storage,
                context,
            )
            .unwrap();
        assert_eq!(
            main_layer_ext_bank_fill_count_for_test(),
            1,
            "each full windowed-R0 layer must enqueue exactly one Ext bank fill"
        );

        let (coefficients_ptr, coefficients_len) = unsafe {
            proof_layout
                .backward_internal_coeffs_device_mut(proof_slab.as_mut_ptr().cast::<u8>(), 0)
        };
        let coefficients_device =
            unsafe { DeviceSlice::from_raw_parts(coefficients_ptr.cast::<E4>(), coefficients_len) };
        let mut coefficients = vec![E4::ZERO; coefficients_len];
        memory_copy_async(
            &mut coefficients,
            coefficients_device,
            context.get_exec_stream(),
        )
        .unwrap();
        let mut seed = [0u32; STATE_SIZE];
        memory_copy_async(
            &mut seed,
            execution
                .device_seed
                .as_ref()
                .expect("the full layer returns the rolling seed"),
            context.get_exec_stream(),
        )
        .unwrap();
        let mut claim = [E4::ZERO];
        memory_copy_async(
            &mut claim,
            execution
                .device_final_claim_for_test
                .as_ref()
                .expect("the smoke retains the final claim"),
            context.get_exec_stream(),
        )
        .unwrap();
        let mut eq_prefactor = [E4::ZERO];
        memory_copy_async(
            &mut eq_prefactor,
            execution
                .device_final_eq_prefactor_for_test
                .as_ref()
                .expect("the smoke retains the final Eq prefactor"),
            context.get_exec_stream(),
        )
        .unwrap();
        let next_claim_point_device = execution
            .device_claim_point_for_next_layer
            .as_ref()
            .expect("the full layer returns its next claim point");
        let mut next_claim_point = vec![E4::ZERO; next_claim_point_device.len()];
        memory_copy_async(
            &mut next_claim_point,
            next_claim_point_device.slice(0, next_claim_point_device.len()),
            context.get_exec_stream(),
        )
        .unwrap();
        let next_claims_device = execution
            .device_claims_for_next_layer
            .as_ref()
            .expect("the full layer returns its next claims");
        let mut next_claims = vec![E4::ZERO; next_claims_device.len()];
        memory_copy_async(
            &mut next_claims,
            next_claims_device,
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        FullLayerSmokeOutput {
            coefficients: bytes_of(&coefficients),
            seed: bytes_of(&seed),
            claim: bytes_of(&claim),
            eq_prefactor: bytes_of(&eq_prefactor),
            next_claim_point: bytes_of(&next_claim_point),
            next_claims: bytes_of(&next_claims),
        }
    }

    fn state_for_layer(
        programs: Arc<GkrPrograms>,
        layer_idx: usize,
        context: &ProverContext,
    ) -> GpuGKRMainLayerBackwardState {
        let runtime = programs.runtime_circuit();
        GpuGKRMainLayerBackwardState {
            forward_tracing_ranges: Vec::new(),
            storage: storage_for_layer(&programs, layer_idx, context),
            pending_layers: VecDeque::from([layer_idx]),
            trace_len: runtime.trace_len,
            inits_and_teardowns_top_bits: vec![0; runtime.memory_layout.teardown_sets.len()],
            programs,
            strategy: BackwardExecutionStrategy::WindowedR0,
            window_tail: WindowTailArm::Split,
        }
    }

    #[test]
    fn main_continuation_option_history_uses_current_options_not_cached_readiness() {
        let context = make_test_context(512, 64);
        let (programs, layers) =
            crate::backward::compile_corpus_layout("blake2_with_extended_control_layout_gkr.json");
        let programs = Arc::new(programs);
        programs
            .resolve_window_programs()
            .expect("the option-history fixture requires windowed R0");
        programs
            .resolve_main_continuation_window_programs()
            .expect("option-on preflight resolves the continuation bundle");
        assert!(programs.main_continuation_window_programs_ready());
        let layer_idx = layers - 1;

        let option_off = GkrBackwardOptions {
            windowed_main_continuations: false,
            ..GkrBackwardOptions::default()
        };
        let mut off_state = state_for_layer(Arc::clone(&programs), layer_idx, &context);
        let off = off_state
            .prepare_next_layer_static(option_off, &context)
            .unwrap()
            .expect("the fixture has one pending layer");
        assert_eq!(off.main_execution_plan.window_count(), 0);
        assert_eq!(off.main_continuation.window_count(), 0);
        assert!(off.main_continuation.published_level().is_none());
        drop(off);
        drop(off_state);

        // Proven-fail mutation: selecting from the sticky OnceLock readiness
        // instead of the current proof option changes this same preparation
        // seam to W>0 and therefore cannot satisfy the option-off assertion.
        let readiness_selected = GkrBackwardOptions {
            windowed_main_continuations: programs.main_continuation_window_programs_ready(),
            ..option_off
        };
        let mut mutated_state = state_for_layer(Arc::clone(&programs), layer_idx, &context);
        let mutated = mutated_state
            .prepare_next_layer_static(readiness_selected, &context)
            .unwrap()
            .expect("the mutation fixture has one pending layer");
        assert!(mutated.main_execution_plan.window_count() > 0);
        let mutated_windows = mutated.main_execution_plan.window_count();
        assert!(
            std::panic::catch_unwind(move || assert_eq!(mutated_windows, 0)).is_err(),
            "cached-readiness selection must be proven to violate option-off W=0"
        );
    }

    #[test]
    fn main_continuation_scheduler_smoke() {
        let context = make_test_context(512, 64);
        let programs = smoke_programs();
        let layer_idx = smoke_layer(&programs);
        let option_on = run_full_layer_smoke(Arc::clone(&programs), layer_idx, true, &context);
        let option_off = run_full_layer_smoke(programs, layer_idx, false, &context);
        assert_eq!(
            option_on, option_off,
            "continuation windows must preserve the full layer's coefficients and transcript state"
        );
    }
}
