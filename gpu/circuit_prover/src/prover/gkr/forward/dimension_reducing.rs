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

pub(super) fn schedule_dimension_reduction_forward<E>(
    storage: &mut GpuGKRStorage<BF, E>,
    initial_layer_idx: usize,
    initial_output_map: BTreeMap<OutputType, Vec<GKRAddress>>,
    initial_trace_log_2: usize,
    final_trace_log_2: usize,
    output_evaluations_slab: Option<ForwardOutputSlabTarget<E>>,
    tracing_ranges: &mut Vec<Range>,
    context: &ProverContext,
) -> CudaResult<(
    usize,
    BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
)>
where
    E: FieldExtension<BF> + Field + SetByRef + SetByVal,
    E: crate::prover::gkr::ForwardKernels,
    Add: BinaryOp<E, E, E>,
    Add: BinaryOp<BF, E, E>,
    Add: BinaryOp<E, BF, E>,
    Mul: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
    Mul: BinaryOp<E, BF, E>,
    Sub: BinaryOp<E, E, E>,
    Sub: BinaryOp<E, BF, E>,
    Sub: BinaryOp<BF, BF, BF>,
{
    let mut dimension_reduction_description = BTreeMap::new();
    let mut current_layer_idx = initial_layer_idx;
    let stream = context.get_exec_stream();
    let total_rounds = initial_trace_log_2.saturating_sub(final_trace_log_2);
    if total_rounds == 0 {
        return Ok((current_layer_idx, dimension_reduction_description));
    }

    // Phase 1: lower + commit every round sequentially so subsequent rounds can resolve inputs
    // from storage. Collect per-round per-slot output pointers for the later tower assembly.
    let mut per_round_slot_outputs: Vec<Vec<LoweredSlotOutput<E>>> =
        Vec::with_capacity(total_rounds);
    let mut slot_initial_inputs: Option<Vec<LoweredSlotInitialInput<E>>> = None;
    let mut slot_output_types: Option<Vec<OutputType>> = None;

    for round_idx in 0..total_rounds {
        let input_size_log_2 = initial_trace_log_2 - round_idx;
        let output_trace_len = 1usize << (input_size_log_2 - 1);
        let is_final_round = round_idx + 1 == total_rounds;

        let layer_inputs = if current_layer_idx != initial_layer_idx {
            let previous: &BTreeMap<OutputType, DimensionReducingInputOutput> =
                dimension_reduction_description
                    .get(&(current_layer_idx - 1))
                    .expect("dimension reduction input layer must exist");
            BTreeMap::from_iter(previous.iter().map(|(k, v)| (*k, v.output.clone())))
        } else {
            initial_output_map.clone()
        };

        let lowered = lower_dimension_reducing_forward_round(
            &layer_inputs,
            current_layer_idx,
            output_trace_len,
            storage,
            if is_final_round {
                output_evaluations_slab.as_ref()
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

    // Phase 2: slot-major dispatch, all launches on exec_stream. Each slot's full reduction
    // chain (every tower chunk) runs contiguously before the next slot starts. One NVTX range
    // per OutputType wraps all slots belonging to that type — PermutationProduct covers both
    // read_set and write_set chains; each lookup type covers its single (num, den) chain.
    let slot_initial_inputs =
        slot_initial_inputs.expect("non-zero rounds implies we captured initial inputs");
    let slot_output_types =
        slot_output_types.expect("non-zero rounds implies we captured slot output types");
    let slot_count = slot_initial_inputs.len();
    let log_block = GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK as usize;

    let mut slot_idx = 0usize;
    while slot_idx < slot_count {
        let range_type = slot_output_types[slot_idx];
        let range_end = slot_output_types[slot_idx..]
            .iter()
            .position(|t| *t != range_type)
            .map(|offset| slot_idx + offset)
            .unwrap_or(slot_count);

        let range = Range::new(format!(
            "gkr.forward.dimension_reduction.tower.{:?}",
            range_type
        ))?;
        range.start(stream)?;

        for s in slot_idx..range_end {
            let mut cur_input = slot_initial_inputs[s];
            let mut cur_input_log_2 = initial_trace_log_2;
            let mut r = 0usize;
            while r < total_rounds {
                let remaining = total_rounds - r;
                let chunk_rounds = remaining.min(log_block);
                let chunk_input_len = 1u32 << cur_input_log_2;
                dispatch_tower_slot_launch(
                    cur_input,
                    s,
                    r,
                    chunk_rounds,
                    chunk_input_len,
                    &per_round_slot_outputs,
                    stream,
                )?;
                r += chunk_rounds;
                cur_input_log_2 -= chunk_rounds;
                if r < total_rounds {
                    let last_round = r - 1;
                    cur_input = match per_round_slot_outputs[last_round][s] {
                        LoweredSlotOutput::PairwiseProduct { output } => {
                            LoweredSlotInitialInput::PairwiseProduct {
                                input: output as *const E,
                            }
                        }
                        LoweredSlotOutput::LookupPair {
                            output_num,
                            output_den,
                        } => LoweredSlotInitialInput::LookupPair {
                            num: output_num as *const E,
                            den: output_den as *const E,
                        },
                    };
                }
            }
        }

        range.end(stream)?;
        tracing_ranges.push(range);

        slot_idx = range_end;
    }

    Ok((current_layer_idx - 1, dimension_reduction_description))
}

fn dispatch_tower_slot_launch<E>(
    slot_input: LoweredSlotInitialInput<E>,
    slot_idx: usize,
    chunk_start_round: usize,
    chunk_rounds: usize,
    chunk_input_len: u32,
    per_round_slot_outputs: &[Vec<LoweredSlotOutput<E>>],
    stream: &era_cudart::stream::CudaStream,
) -> CudaResult<()>
where
    E: crate::prover::gkr::ForwardKernels,
{
    match slot_input {
        LoweredSlotInitialInput::PairwiseProduct { input } => {
            let mut batch = GpuGKRDimensionReducingForwardTowerPairwiseBatch::<E>::default();
            batch.input = input;
            batch.input_len = chunk_input_len;
            batch.round_count = chunk_rounds as u32;
            for local_r in 0..chunk_rounds {
                let round_idx = chunk_start_round + local_r;
                match per_round_slot_outputs[round_idx][slot_idx] {
                    LoweredSlotOutput::PairwiseProduct { output } => {
                        batch.round_outputs[local_r] = output;
                    }
                    LoweredSlotOutput::LookupPair { .. } => panic!(
                        "tower slot {} changed kind between round 0 and round {}",
                        slot_idx, round_idx
                    ),
                }
            }
            launch_dimension_reducing_forward_tower_pairwise(&batch, stream)
        }
        LoweredSlotInitialInput::LookupPair { num, den } => {
            let mut batch = GpuGKRDimensionReducingForwardTowerLookupBatch::<E>::default();
            batch.input_num = num;
            batch.input_den = den;
            batch.input_len = chunk_input_len;
            batch.round_count = chunk_rounds as u32;
            for local_r in 0..chunk_rounds {
                let round_idx = chunk_start_round + local_r;
                match per_round_slot_outputs[round_idx][slot_idx] {
                    LoweredSlotOutput::LookupPair {
                        output_num,
                        output_den,
                    } => {
                        batch.round_outputs_num[local_r] = output_num;
                        batch.round_outputs_den[local_r] = output_den;
                    }
                    LoweredSlotOutput::PairwiseProduct { .. } => panic!(
                        "tower slot {} changed kind between round 0 and round {}",
                        slot_idx, round_idx
                    ),
                }
            }
            launch_dimension_reducing_forward_tower_lookup(&batch, stream)
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
        // FS-safe merge (PR #305): both passes iterate `BTreeMap<OutputType>`
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
