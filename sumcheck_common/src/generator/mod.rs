use ::field::*;
use cs::gkr_compiler::GKRLayerDescription;
use proc_macro2::TokenStream;

pub fn generate_layer<F: PrimeField, E: FieldExtension<F> + Field>(
    _layer: &GKRLayerDescription<F>,
) -> TokenStream {
    todo!();
}

#[cfg(test)]
mod tests {
    use cs::gkr_compiler::GKRCircuitArtifact;

    fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
        let src = std::fs::File::open(filename).unwrap();
        serde_json::from_reader(src).unwrap()
    }

    #[test]
    fn test_generation() {
        use ::field::baby_bear::base::BabyBearField;

        let circuit: GKRCircuitArtifact<BabyBearField> = deserialize_from_file(
            "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
        );

        let layer_idx = 0;
        let _layer = &circuit.layers[layer_idx];
    }
}
