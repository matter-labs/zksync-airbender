use ::field::*;
use cs::gkr_compiler::{GKRCircuitArtifact, GKRLayerDescription};
use proc_macro2::TokenStream;

pub(crate) fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

pub(crate) fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).unwrap();
    serde_json::from_reader(src).unwrap()
}

pub fn generate_layer<F: PrimeField, E: FieldExtension<F> + Field>(
    layer: &GKRLayerDescription,
) -> TokenStream {
    todo!();
}

#[test]
fn test_generation() {
    use ::field::baby_bear::base::BabyBearField;

    let circuit: GKRCircuitArtifact<BabyBearField> = deserialize_from_file(
        "../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
    );

    let layer_idx = 0;
    let layer = &circuit.layers[layer_idx];
}
