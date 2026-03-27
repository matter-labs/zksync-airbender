use super::*;

pub fn forward_evaluate_copy<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const CAN_NOT_FAIL: bool,
>(
    input: GKRAddress,
    output: GKRAddress,
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    _trace_len: usize,
    _worker: &Worker,
) {
    output.assert_as_layer(expected_output_layer);
    assert!(output.is_cache() == false);
    input.assert_as_layer(expected_output_layer - 1);

    if gkr_storage.try_get_base_poly(output).is_some()
        || gkr_storage.try_get_ext_poly(output).is_some()
    {
        return;
    }

    if let Some(source) = gkr_storage.try_get_base_poly_arc_cloned(input) {
        // println!("Copying base field {:?} -> {:?}", input, output);
        gkr_storage.insert_base_field_at_layer(expected_output_layer, output, source);
    } else if let Some(source) = gkr_storage.try_get_ext_poly_arc_cloned(input) {
        // println!("Copying extension field {:?} -> {:?}", input, output);
        gkr_storage.insert_extension_at_layer(expected_output_layer, output, source);
    } else {
        if CAN_NOT_FAIL {
            panic!(
                "Trying to copy {:?} -> {:?}, but the input is not present in storage",
                input, output
            );
        }
    }
}
