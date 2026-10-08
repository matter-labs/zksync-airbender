use ::field::*;
use cs::gkr_compiler::GKRLayerDescription;
use proc_macro2::TokenStream;

#[cfg(test)]
pub(crate) fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).unwrap();
    serde_json::from_reader(src).unwrap()
}

pub fn generate_layer<F: PrimeField, E: FieldExtension<F> + Field>(
    _layer: &GKRLayerDescription<F>,
) -> TokenStream {
    todo!();
}

#[test]
fn test_generation() {
    use ::field::baby_bear::base::BabyBearField;
    use cs::gkr_compiler::GKRCircuitArtifact;

    let circuit: GKRCircuitArtifact<BabyBearField> = deserialize_from_file(
        "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
    );

    let layer_idx = 0;
    let _layer = &circuit.layers[layer_idx];
}
