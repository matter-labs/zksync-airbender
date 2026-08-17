use super::vm::desc::{REDUCTION_PAIR_CAP, REDUCTION_PAIR_LOOKUP, REDUCTION_PAIR_PAIRWISE2};
use super::*;

#[derive(Clone, Copy)]
pub(super) enum LoweredSlotInitialInput<E> {
    PairwiseProduct { input: *const E },
    LookupPair { num: *const E, den: *const E },
}

/// Per-slot output pointers for a single reduction round.
#[derive(Clone, Copy)]
pub(super) enum LoweredSlotOutput<E> {
    PairwiseProduct {
        output: *mut E,
    },
    LookupPair {
        output_num: *mut E,
        output_den: *mut E,
    },
}

pub(super) struct LoweredDimReducingForwardRound<E> {
    pub(super) slot_initial_inputs: Vec<LoweredSlotInitialInput<E>>,
    pub(super) slot_output_types: Vec<OutputType>,
    pub(super) slot_outputs: Vec<LoweredSlotOutput<E>>,
    pub(super) layer_description: BTreeMap<OutputType, DimensionReducingInputOutput>,
    pub(super) computed_extension_outputs: Vec<(GKRAddress, GpuExtensionFieldPoly<E>)>,
}

pub(super) struct PreparedDimensionReductionForward<E> {
    pub(super) initial_trace_log_2: u32,
    pub(super) total_rounds: u32,
    pub(super) final_layer_idx: usize,
    pub(super) dimension_reduction_description:
        BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
    pub(super) slot_initial_inputs: Vec<LoweredSlotInitialInput<E>>,
    pub(super) slot_output_types: Vec<OutputType>,
    pub(super) per_round_slot_outputs: Vec<Vec<LoweredSlotOutput<E>>>,
}

pub(super) fn prepare_dimension_reduction_forward<E>(
    storage: &mut GpuGKRStorage<BF, E>,
    initial_layer_idx: usize,
    initial_output_map: &BTreeMap<OutputType, Vec<GKRAddress>>,
    initial_trace_log_2: u32,
    final_trace_log_2: u32,
    output_evaluations_slab: Option<&ForwardOutputSlabTarget<E>>,
    context: &ProverContext,
) -> CudaResult<PreparedDimensionReductionForward<E>>
where
    E: FieldExtension<BF> + Field + 'static,
{
    let total_rounds = initial_trace_log_2
        .checked_sub(final_trace_log_2)
        .expect("final trace size must not exceed the initial trace size");
    assert!(total_rounds >= vm::desc::FUSED_REDUCTION_ROUNDS as u32);
    let mut dimension_reduction_description = BTreeMap::new();
    let mut per_round_slot_outputs = Vec::with_capacity(total_rounds as usize);
    let mut slot_initial_inputs = None;
    let mut slot_output_types = None;
    let mut current_layer_idx = initial_layer_idx;

    for round_idx in 0..total_rounds {
        let input_size_log_2 = initial_trace_log_2 - round_idx;
        let output_trace_len = 1usize << (input_size_log_2 - 1);
        let is_final_round = round_idx + 1 == total_rounds;
        let layer_inputs = if current_layer_idx == initial_layer_idx {
            initial_output_map.clone()
        } else {
            let previous: &BTreeMap<OutputType, DimensionReducingInputOutput> =
                dimension_reduction_description
                    .get(&(current_layer_idx - 1))
                    .expect("dimension reduction input layer must exist");
            BTreeMap::from_iter(previous.iter().map(|(kind, io)| (*kind, io.output.clone())))
        };
        let lowered = lower_dimension_reducing_forward_round(
            &layer_inputs,
            current_layer_idx,
            output_trace_len,
            storage,
            if is_final_round {
                output_evaluations_slab
            } else {
                None
            },
            context,
        )?;

        if round_idx == 0 {
            slot_initial_inputs = Some(lowered.slot_initial_inputs.clone());
            slot_output_types = Some(lowered.slot_output_types.clone());
        }
        per_round_slot_outputs.push(lowered.slot_outputs.clone());
        for (address, poly) in lowered.computed_extension_outputs {
            storage.insert_extension_at_layer(current_layer_idx + 1, address, poly);
        }
        dimension_reduction_description.insert(current_layer_idx, lowered.layer_description);
        current_layer_idx += 1;
    }

    Ok(PreparedDimensionReductionForward {
        initial_trace_log_2,
        total_rounds,
        final_layer_idx: current_layer_idx - 1,
        dimension_reduction_description,
        slot_initial_inputs: slot_initial_inputs.expect("dimension reduction inputs must exist"),
        slot_output_types: slot_output_types.expect("dimension reduction output types must exist"),
        per_round_slot_outputs,
    })
}

pub(super) fn schedule_prepared_dimension_reduction_forward<E>(
    prepared: &PreparedDimensionReductionForward<E>,
    start_round: u32,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: crate::ForwardKernels,
{
    assert!(start_round <= prepared.total_rounds);
    if start_round == prepared.total_rounds {
        return Ok(());
    }

    let stream = context.get_exec_stream();
    let slot_count = prepared.slot_initial_inputs.len();
    assert_eq!(prepared.slot_output_types.len(), slot_count);

    // A pairwise OutputType contributes its two slots as one pair's (a, b)
    // streams; a lookup slot contributes its (num, den).
    let mut pair_slots: Vec<(u32, [usize; 2])> = Vec::new();
    let mut slot_idx = 0usize;
    while slot_idx < slot_count {
        match prepared.slot_initial_inputs[slot_idx] {
            LoweredSlotInitialInput::PairwiseProduct { .. } => {
                let partner = slot_idx + 1;
                assert!(
                    partner < slot_count
                        && prepared.slot_output_types[partner]
                            == prepared.slot_output_types[slot_idx]
                        && matches!(
                            prepared.slot_initial_inputs[partner],
                            LoweredSlotInitialInput::PairwiseProduct { .. }
                        ),
                    "pairwise reduction type must own exactly two adjacent slots"
                );
                pair_slots.push((REDUCTION_PAIR_PAIRWISE2, [slot_idx, partner]));
                slot_idx += 2;
            }
            LoweredSlotInitialInput::LookupPair { .. } => {
                pair_slots.push((REDUCTION_PAIR_LOOKUP, [slot_idx, slot_idx]));
                slot_idx += 1;
            }
        }
    }
    assert!(pair_slots.len() <= REDUCTION_PAIR_CAP);

    let mut round = start_round;
    let mut input_log_2 = prepared.initial_trace_log_2 - start_round;
    while round < prepared.total_rounds {
        let chunk_rounds =
            (prepared.total_rounds - round).min(GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK);
        let mut batch = GpuGKRDimensionReducingForwardTowerBatch::<E> {
            pair_count: pair_slots.len() as u32,
            input_len: 1u32 << input_log_2,
            round_count: chunk_rounds,
            ..Default::default()
        };
        for (pair, &(kind, slots)) in batch.pairs.iter_mut().zip(&pair_slots) {
            pair.kind = kind;
            pair.input = pair_input_streams(prepared, round, kind, slots);
            for local_r in 0..chunk_rounds as usize {
                pair.round_outputs[local_r] =
                    pair_output_streams(prepared, round as usize + local_r, kind, slots);
            }
        }
        launch_dimension_reducing_forward_tower(batch, stream)?;
        round += chunk_rounds;
        input_log_2 -= chunk_rounds;
    }
    Ok(())
}

fn pair_input_streams<E>(
    prepared: &PreparedDimensionReductionForward<E>,
    round: u32,
    kind: u32,
    slots: [usize; 2],
) -> [*const E; 2] {
    if round == 0 {
        match kind {
            REDUCTION_PAIR_PAIRWISE2 => slots.map(|slot| {
                let LoweredSlotInitialInput::PairwiseProduct { input } =
                    prepared.slot_initial_inputs[slot]
                else {
                    panic!("tower slot {slot} changed kind");
                };
                input
            }),
            _ => {
                let LoweredSlotInitialInput::LookupPair { num, den } =
                    prepared.slot_initial_inputs[slots[0]]
                else {
                    panic!("tower slot {} changed kind", slots[0]);
                };
                [num, den]
            }
        }
    } else {
        pair_output_streams(prepared, round as usize - 1, kind, slots).map(|ptr| ptr as *const E)
    }
}

fn pair_output_streams<E>(
    prepared: &PreparedDimensionReductionForward<E>,
    round: usize,
    kind: u32,
    slots: [usize; 2],
) -> [*mut E; 2] {
    let round_outputs = &prepared.per_round_slot_outputs[round];
    match kind {
        REDUCTION_PAIR_PAIRWISE2 => slots.map(|slot| {
            let LoweredSlotOutput::PairwiseProduct { output } = round_outputs[slot] else {
                panic!("tower slot {slot} changed kind at round {round}");
            };
            output
        }),
        _ => {
            let LoweredSlotOutput::LookupPair {
                output_num,
                output_den,
            } = round_outputs[slots[0]]
            else {
                panic!("tower slot {} changed kind at round {round}", slots[0]);
            };
            [output_num, output_den]
        }
    }
}

// Tower outputs are routed through the consolidated per-(tower-layer, class)
// backings populated by `GpuGKRStorageLayout::from_artifact_with_tower`. Each
// view returned by `storage.allocate_ext_view` is sized to the round's
// `output_trace_len` (the layout's per-layer `log2_stride` halves each round).
fn lower_dimension_reducing_forward_round<E>(
    layer_inputs: &BTreeMap<OutputType, Vec<GKRAddress>>,
    current_layer_idx: usize,
    output_trace_len: usize,
    storage: &mut GpuGKRStorage<BF, E>,
    output_evaluations_slab: Option<&ForwardOutputSlabTarget<E>>,
    context: &ProverContext,
) -> CudaResult<LoweredDimReducingForwardRound<E>>
where
    E: FieldExtension<BF> + Field,
    E: 'static,
{
    let output_layer = current_layer_idx + 1;
    if let Some(target) = output_evaluations_slab {
        let output_polys: usize = layer_inputs.values().map(Vec::len).sum();
        assert_eq!(
            target.len,
            output_polys * output_trace_len,
            "slab output_evaluations length must match final forward reduction outputs",
        );
        assert!(
            target.backing.len() >= target.len,
            "proof slab backing must contain the output_evaluations prefix",
        );
        if output_layer >= storage.layers.len() {
            storage
                .layers
                .resize_with(output_layer + 1, GpuGKRLayerSource::default);
        }
        let previous = storage.layers[output_layer].ext_class_backings.insert(
            super::super::gkr_address_audit::AddressClass::ThisLayerInnerLayerWrite,
            Arc::clone(&target.backing),
        );
        assert!(
            previous.is_none(),
            "final forward output slab backing must be bound before any output allocation",
        );
    }
    let mut output_idx = 0usize;
    let mut layer_description = BTreeMap::new();
    let mut slot_initial_inputs = Vec::new();
    let mut slot_output_types = Vec::new();
    let mut slot_outputs = Vec::new();
    let mut computed_extension_outputs = Vec::new();

    for (arg_type, inputs) in layer_inputs.iter() {
        let inputs: [GKRAddress; 2] = inputs
            .clone()
            .try_into()
            .expect("dimension reduction forward inputs must have arity 2");
        // FS-safe merge: both passes iterate `BTreeMap<OutputType>`
        // with the derived `Ord`; `InitsAndTeardownsProduct` is the last
        // discriminant (cs/src/definitions/gkr_layers.rs:5-10), so its 2
        // pairwise records / 2 challenges are always squeezed AFTER the
        // PermutationProduct + lookup records — identical to the CPU order.
        match *arg_type {
            OutputType::PermutationProduct | OutputType::InitsAndTeardownsProduct => {
                let mut outputs = [GKRAddress::placeholder(); 2];
                for (idx, input) in inputs.into_iter().enumerate() {
                    let input_start_ptr = storage
                        .try_get_ext_poly(input)
                        .unwrap_or_else(|| {
                            panic!("missing dimension reduction input poly for {:?}", input)
                        })
                        .as_ptr();
                    let output = GKRAddress::InnerLayer {
                        layer: output_layer,
                        offset: output_idx,
                    };
                    output_idx += 1;
                    let reduced = storage.allocate_ext_view(output_layer, output, context)?;
                    assert_eq!(
                        reduced.len(),
                        output_trace_len,
                        "tower layer {output_layer} layout stride implies len {} but round expects {}",
                        reduced.len(),
                        output_trace_len,
                    );
                    let output_ptr = reduced.as_mut_ptr();
                    slot_initial_inputs.push(LoweredSlotInitialInput::PairwiseProduct {
                        input: input_start_ptr,
                    });
                    slot_output_types.push(*arg_type);
                    slot_outputs.push(LoweredSlotOutput::PairwiseProduct { output: output_ptr });
                    computed_extension_outputs.push((output, reduced));
                    outputs[idx] = output;
                }
                layer_description.insert(
                    *arg_type,
                    DimensionReducingInputOutput {
                        inputs: inputs.to_vec(),
                        output: outputs.to_vec(),
                    },
                );
            }
            OutputType::Lookup16Bits | OutputType::LookupTimestamps | OutputType::GenericLookup => {
                let num_ptr = storage
                    .try_get_ext_poly(inputs[0])
                    .unwrap_or_else(|| {
                        panic!(
                            "missing lookup reduction numerator poly for {:?}",
                            inputs[0]
                        )
                    })
                    .as_ptr();
                let den_ptr = storage
                    .try_get_ext_poly(inputs[1])
                    .unwrap_or_else(|| {
                        panic!(
                            "missing lookup reduction denominator poly for {:?}",
                            inputs[1]
                        )
                    })
                    .as_ptr();
                let new_num = GKRAddress::InnerLayer {
                    layer: output_layer,
                    offset: output_idx,
                };
                output_idx += 1;
                let new_den = GKRAddress::InnerLayer {
                    layer: output_layer,
                    offset: output_idx,
                };
                output_idx += 1;
                let reduced_num = storage.allocate_ext_view(output_layer, new_num, context)?;
                let reduced_den = storage.allocate_ext_view(output_layer, new_den, context)?;
                assert_eq!(reduced_num.len(), output_trace_len);
                assert_eq!(reduced_den.len(), output_trace_len);
                let out_num_ptr = reduced_num.as_mut_ptr();
                let out_den_ptr = reduced_den.as_mut_ptr();
                slot_initial_inputs.push(LoweredSlotInitialInput::LookupPair {
                    num: num_ptr,
                    den: den_ptr,
                });
                slot_output_types.push(*arg_type);
                slot_outputs.push(LoweredSlotOutput::LookupPair {
                    output_num: out_num_ptr,
                    output_den: out_den_ptr,
                });
                computed_extension_outputs.push((new_num, reduced_num));
                computed_extension_outputs.push((new_den, reduced_den));
                layer_description.insert(
                    *arg_type,
                    DimensionReducingInputOutput {
                        inputs: inputs.to_vec(),
                        output: [new_num, new_den].to_vec(),
                    },
                );
            }
        }
    }
    Ok(LoweredDimReducingForwardRound {
        slot_initial_inputs,
        slot_output_types,
        slot_outputs,
        layer_description,
        computed_extension_outputs,
    })
}
