use std::collections::BTreeMap;

use cs::definitions::GKRAddress;
use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};
use field::{Field, FieldExtension, PrimeField};

use crate::gkr::sumcheck::access_and_fold::GKRStorage;

pub(crate) fn evaluate_mle<E: Field>(evals: &[E], point: &[E]) -> E {
    assert_eq!(evals.len(), 1 << point.len());
    let mut buf = evals.to_vec();
    for z_i in point.iter() {
        let half = buf.len() / 2;
        for j in 0..half {
            // buf[j] = buf[2j] * (1 - z_i) + buf[2j+1] * z_i
            let mut diff = buf[2 * j + 1];
            diff.sub_assign(&buf[2 * j]);
            diff.mul_assign(z_i);
            buf[j] = buf[2 * j];
            buf[j].add_assign(&diff);
        }
        buf.truncate(half);
    }
    buf[0]
}


pub(crate) fn check_logup_identity<F: PrimeField, E: FieldExtension<F> + Field>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    gkr_storage: &GKRStorage<F, E>,
) -> bool {
    for output_type in [
        OutputType::Lookup16Bits,
        OutputType::LookupTimestamps,
        OutputType::GenericLookup,
    ] {
        if let Some(addrs) = compiled_circuit.global_output_map.get(&output_type) {
            let num_addr = addrs[0];
            let den_addr = addrs[1];
            let layer_idx = match num_addr {
                GKRAddress::InnerLayer { layer, .. } => layer,
                _ => panic!("expected InnerLayer address for lookup output"),
            };
            let layer_source = &gkr_storage.layers[layer_idx];
            let num_poly = &layer_source.extension_field_inputs[&num_addr].values;
            let den_poly = &layer_source.extension_field_inputs[&den_addr].values;
            let mut sum = E::ZERO;
            for (n, d) in num_poly.iter().zip(den_poly.iter()) {
                let den_inv = d.inverse().expect("denominator must be nonzero");
                let mut term = *n;
                term.mul_assign(&den_inv);
                sum.add_assign(&term);
            }
            if !sum.is_zero() {
                return false;
            }
        }
    }
    true
}

pub(crate) fn mock_output_claims<F: PrimeField, E: FieldExtension<F> + Field>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    gkr_storage: &GKRStorage<F, E>,
    z: &[E],
) -> BTreeMap<GKRAddress, E> {
    let mut claims = BTreeMap::new();

    for output_type in [
        OutputType::PermutationProduct,
        OutputType::Lookup16Bits,
        OutputType::LookupTimestamps,
        OutputType::GenericLookup,
    ] {
        if let Some(addrs) = compiled_circuit.global_output_map.get(&output_type) {
            for &addr in addrs.iter() {
                let layer_idx = match addr {
                    GKRAddress::InnerLayer { layer, .. } => layer,
                    _ => panic!("expected InnerLayer address for output"),
                };
                let poly = &gkr_storage.layers[layer_idx]
                    .extension_field_inputs[&addr].values;
                let claim = evaluate_mle(poly, z);
                claims.insert(addr, claim);
            }
        }
    }

    claims
}
