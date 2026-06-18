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

    for input_size_log_2 in ((final_trace_log_2 + 1)..=initial_trace_log_2).rev() {
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
                a @ OutputType::PermutationProduct => {
                    let [read_set, write_set] = inputs;
                    let mut set_outputs = [GKRAddress::placeholder(); 2];
                    for (i, set) in [read_set, write_set].into_iter().enumerate() {
                        let output = GKRAddress::InnerLayer {
                            layer: current_layer_idx + 1,
                            offset: output_idx,
                        };
                        output_idx += 1;
                        let kernel =
                            PairwiseProductDimensionReducingGKRRelation { input: set, output };
                        kernel.evaluate_forward_over_storage(
                            gkr_storage,
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
                    let kernel = LookupPairDimensionReducingGKRRelation {
                        inputs: [num, den],
                        outputs: [new_num, new_den],
                    };
                    kernel.evaluate_forward_over_storage(
                        gkr_storage,
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

        current_layer_idx += 1;
    }

    (current_layer_idx - 1, dimension_reduction_description)
}
