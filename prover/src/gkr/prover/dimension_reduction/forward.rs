use crate::gkr::prover::dimension_reduction::kernels::{
    logup::LookupPairDimensionReducingGKRRelation,
    pairwise_product::PairwiseProductDimensionReducingGKRRelation,
};

use super::*;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DimensionReducingInputOutput {
    pub inputs: Vec<GKRAddress>,
    pub output: Vec<GKRAddress>,
}

/// Backend-parameterized forward skeleton: the layer/address bookkeeping is
/// backend-independent; the per-relation evaluation is supplied by the
/// [`GKRBackend`](crate::gkr::prover::gkr_backend::GKRBackend) implementation
/// (scalar for the naive backend, platform-specialized otherwise). Platform
/// selection NEVER appears in this file.
pub fn evaluate_dimension_reduction_forward_with<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    PW: Fn(&mut GKRStorage<F, E>, GKRAddress, GKRAddress, usize, usize, &Worker),
    LG: Fn(&mut GKRStorage<F, E>, [GKRAddress; 2], [GKRAddress; 2], usize, usize, &Worker),
>(
    gkr_storage: &mut GKRStorage<F, E>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    initial_trace_log_2: usize,
    final_trace_log_2: usize,
    worker: &Worker,
    pairwise: PW,
    logup: LG,
) -> (
    usize,
    BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
) {
    println!(
        "Evaluating dimension reduction 2^{} -> 2^{} in forward direction",
        initial_trace_log_2, final_trace_log_2
    );

    let mut dimension_reduction_description: BTreeMap<
        usize,
        BTreeMap<OutputType, DimensionReducingInputOutput>,
    > = BTreeMap::new();
    let layer_idx = compiled_circuit.layers.len();
    for (_, v) in compiled_circuit.global_output_map.iter() {
        for address in v.iter() {
            address.assert_as_layer(layer_idx);
        }
    }

    let mut current_layer_idx = layer_idx;

    let forward_total = std::time::Instant::now();
    for input_size_log_2 in ((final_trace_log_2 + 1)..=initial_trace_log_2).rev() {
        let layer_timer = std::time::Instant::now();
        let layer_inputs = if current_layer_idx != layer_idx {
            let t = dimension_reduction_description
                .get(&(current_layer_idx - 1))
                .expect("input layer");
            BTreeMap::from_iter(t.iter().map(|(k, v)| (*k, v.output.clone())))
        } else {
            compiled_circuit.global_output_map.clone()
        };
        let mut layer_description: BTreeMap<OutputType, DimensionReducingInputOutput> =
            BTreeMap::new();
        let mut output_idx = 0;
        let input_trace_len = 1 << input_size_log_2;
        for (arg_type, inputs) in layer_inputs.into_iter() {
            let inputs: [_; 2] = inputs.try_into().unwrap();
            match arg_type {
                a @ OutputType::PermutationProduct | a @ OutputType::InitsAndTeardownsProduct => {
                    let [read_set, write_set] = inputs;
                    let mut set_outputs = [GKRAddress::placeholder(); 2];
                    for (i, set) in [read_set, write_set].into_iter().enumerate() {
                        let output = GKRAddress::InnerLayer {
                            layer: current_layer_idx + 1,
                            offset: output_idx,
                        };
                        output_idx += 1;
                        pairwise(
                            gkr_storage,
                            set,
                            output,
                            current_layer_idx + 1,
                            input_trace_len,
                            worker,
                        );
                        set_outputs[i] = output;
                    }
                    let descr = DimensionReducingInputOutput {
                        inputs: inputs.to_vec(),
                        output: set_outputs.to_vec(),
                    };
                    layer_description.insert(a, descr);
                }
                a @ OutputType::Lookup16Bits
                | a @ OutputType::LookupTimestamps
                | a @ OutputType::GenericLookup => {
                    let [num, den] = inputs;
                    let new_num = GKRAddress::InnerLayer {
                        layer: current_layer_idx + 1,
                        offset: output_idx,
                    };
                    output_idx += 1;
                    let new_den = GKRAddress::InnerLayer {
                        layer: current_layer_idx + 1,
                        offset: output_idx,
                    };
                    output_idx += 1;
                    logup(
                        gkr_storage,
                        [num, den],
                        [new_num, new_den],
                        current_layer_idx + 1,
                        input_trace_len,
                        worker,
                    );
                    let descr = DimensionReducingInputOutput {
                        inputs: inputs.to_vec(),
                        output: [new_num, new_den].to_vec(),
                    };
                    layer_description.insert(a, descr);
                }
            }
        }
        dimension_reduction_description.insert(current_layer_idx, layer_description);

        println!(
            "Dimension-reduction forward layer 2^{} -> 2^{} took {:?}",
            input_size_log_2,
            input_size_log_2 - 1,
            layer_timer.elapsed()
        );
        current_layer_idx += 1;
    }
    println!(
        "Dimension-reduction forward pass total: {:?}",
        forward_total.elapsed()
    );

    (current_layer_idx - 1, dimension_reduction_description)
}

/// Naive (scalar) forward pass: the skeleton with the scalar per-relation ops.
pub fn evaluate_dimension_reduction_forward<F: PrimeField, E: FieldExtension<F> + Field>(
    gkr_storage: &mut GKRStorage<F, E>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    initial_trace_log_2: usize,
    final_trace_log_2: usize,
    worker: &Worker,
) -> (
    usize,
    BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
) {
    evaluate_dimension_reduction_forward_with(
        gkr_storage,
        compiled_circuit,
        initial_trace_log_2,
        final_trace_log_2,
        worker,
        forward_pairwise_specialized,
        forward_logup_specialized,
    )
}

/// Specialized forward evaluation of one pairwise-product reduction:
/// `out[i] = in[2i] * in[2i+1]`, straight over the raw slices (no
/// `EvaluationFormStorage` / kernel-trait indirection), worker-chunked.
pub(crate) fn forward_pairwise_specialized<F: PrimeField, E: FieldExtension<F> + Field>(
    gkr_storage: &mut GKRStorage<F, E>,
    input: GKRAddress,
    output: GKRAddress,
    expected_output_layer: usize,
    input_trace_len: usize,
    worker: &Worker,
) {
    use crate::gkr::PAR_THRESHOLD;
    let output_trace_len = input_trace_len / 2;
    unsafe {
        let inputs = GKRInputs {
            inputs_in_base: Vec::new(),
            inputs_in_extension: vec![input],
            outputs_in_base: Vec::new(),
            outputs_in_extension: Vec::new(),
        };
        let sources = gkr_storage.get_for_sumcheck_round_0(&inputs);
        let src: &[E] = sources.extension_field_inputs[0].current_values();
        debug_assert_eq!(src.len(), input_trace_len);
        let mut destination = Box::<[E]>::new_uninit_slice(output_trace_len);
        let src_addr = src.as_ptr() as usize;
        let dst_addr = destination.as_mut_ptr() as usize;
        worker.scope_with_threshold(output_trace_len, PAR_THRESHOLD, |scope, geometry| {
            for thread_idx in 0..geometry.num_chunks {
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                let chunk_size = geometry.get_chunk_size(thread_idx);
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let sp = src_addr as *const E;
                    let dp = dst_addr as *mut E;
                    for i in chunk_start..(chunk_start + chunk_size) {
                        let mut v = *sp.add(2 * i);
                        v.mul_assign(&*sp.add(2 * i + 1));
                        *dp.add(i) = v;
                    }
                })
            }
        });
        let values = destination.assume_init();
        output.assert_as_layer(expected_output_layer);
        gkr_storage.insert_extension_at_layer(
            expected_output_layer,
            output,
            crate::gkr::sumcheck::access_and_fold::ExtensionFieldPoly::new(values),
        );
    }
}

/// Specialized forward evaluation of one logup fraction-add reduction:
/// `out_num[i] = n[2i]*d[2i+1] + n[2i+1]*d[2i]`, `out_den[i] = d[2i]*d[2i+1]`.
pub(crate) fn forward_logup_specialized<F: PrimeField, E: FieldExtension<F> + Field>(
    gkr_storage: &mut GKRStorage<F, E>,
    inputs: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    expected_output_layer: usize,
    input_trace_len: usize,
    worker: &Worker,
) {
    use crate::gkr::PAR_THRESHOLD;
    let output_trace_len = input_trace_len / 2;
    unsafe {
        let gkr_inputs = GKRInputs {
            inputs_in_base: Vec::new(),
            inputs_in_extension: inputs.to_vec(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: Vec::new(),
        };
        let sources = gkr_storage.get_for_sumcheck_round_0(&gkr_inputs);
        let n_src: &[E] = sources.extension_field_inputs[0].current_values();
        let d_src: &[E] = sources.extension_field_inputs[1].current_values();
        debug_assert_eq!(n_src.len(), input_trace_len);
        debug_assert_eq!(d_src.len(), input_trace_len);
        let mut num_dst = Box::<[E]>::new_uninit_slice(output_trace_len);
        let mut den_dst = Box::<[E]>::new_uninit_slice(output_trace_len);
        let n_addr = n_src.as_ptr() as usize;
        let d_addr = d_src.as_ptr() as usize;
        let nd_addr = num_dst.as_mut_ptr() as usize;
        let dd_addr = den_dst.as_mut_ptr() as usize;
        worker.scope_with_threshold(output_trace_len, PAR_THRESHOLD, |scope, geometry| {
            for thread_idx in 0..geometry.num_chunks {
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                let chunk_size = geometry.get_chunk_size(thread_idx);
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let np = n_addr as *const E;
                    let dp = d_addr as *const E;
                    let ndp = nd_addr as *mut E;
                    let ddp = dd_addr as *mut E;
                    for i in chunk_start..(chunk_start + chunk_size) {
                        let (n0, n1) = (*np.add(2 * i), *np.add(2 * i + 1));
                        let (d0, d1) = (*dp.add(2 * i), *dp.add(2 * i + 1));
                        let mut num_v = n0;
                        num_v.mul_assign(&d1);
                        let mut t = n1;
                        t.mul_assign(&d0);
                        num_v.add_assign(&t);
                        let mut den_v = d0;
                        den_v.mul_assign(&d1);
                        *ndp.add(i) = num_v;
                        *ddp.add(i) = den_v;
                    }
                })
            }
        });
        for (addr, dst) in outputs
            .into_iter()
            .zip([num_dst.assume_init(), den_dst.assume_init()].into_iter())
        {
            addr.assert_as_layer(expected_output_layer);
            gkr_storage.insert_extension_at_layer(
                expected_output_layer,
                addr,
                crate::gkr::sumcheck::access_and_fold::ExtensionFieldPoly::new(dst),
            );
        }
    }
}
