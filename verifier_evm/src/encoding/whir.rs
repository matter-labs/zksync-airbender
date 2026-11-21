//! WHIR section of the compressed calldata (single-tx: the committed-state header comes from
//! the GKR verifier).

use field::Proth120;

use super::digest::digest_wire;
use super::params::Geometry;
use super::runs::write_fe_run;
use super::Writer;
use crate::seed::Proof;

/// Base-oracle leaf values in column-major transcript order.
pub(crate) fn base_leaf(vals: &[Proth120], num_columns: usize) -> Vec<Proth120> {
    assert!(vals.len().is_multiple_of(num_columns));
    let vp = vals.len() / num_columns;
    (0..num_columns)
        .flat_map(|c| (0..vp).map(move |o| vals[o * num_columns + c]))
        .collect()
}

fn digests(path: &[[u32; 8]]) -> Vec<u8> {
    path.iter().flat_map(digest_wire).collect()
}

pub(super) fn encode_whir(w: &mut Writer, proof: &Proof, params: &Geometry) {
    let wp = &proof.whir_proof;
    let num_rounds = params.folds.len();
    let mut steps = wp.all_sumcheck_polys();
    let nonces = wp.queries_pow_nonces();
    assert_eq!(nonces.len(), num_rounds, "WHIR query PoW count");
    for oracle in &wp.intermediate_whir_oracles {
        assert_eq!(
            oracle.ood_samples.len(),
            1,
            "the compressed calldata encodes exactly one OOD sample"
        );
    }
    for r in 0..num_rounds {
        let sumcheck: Vec<Proth120> = (0..params.folds[r])
            .flat_map(|_| {
                let sp = steps.next().expect("missing WHIR sumcheck step");
                // c1 is not sent: the verifier derives it as claim − 2·c0 − c2
                [sp[0], sp[2]]
            })
            .collect();
        w.put(format!("whir_{r}_sumcheck"), &write_fe_run(&sumcheck));
        let folding_nonces = if r == 0 {
            &wp.base_folding_pow_nonces
        } else {
            &wp.intermediate_whir_oracles[r - 1].folding_pow_nonces
        };
        let expected = if params.folding_pow_bits[r] > 0 {
            params.folds[r]
        } else {
            0
        };
        assert_eq!(folding_nonces.len(), expected, "folding PoW nonce count");
        if expected > 0 {
            let bytes: Vec<_> = folding_nonces
                .iter()
                .flat_map(|n| n.to_be_bytes())
                .collect();
            w.put(format!("whir_{r}_folding_nonces"), &bytes);
        }
        if r < num_rounds - 1 {
            let oracle = &wp.intermediate_whir_oracles[r];
            let cap = &oracle.commitment.cap.cap;
            assert_eq!(cap.len(), params.cap(), "intermediate cap size");
            w.put(format!("whir_{r}_cap"), &digests(cap));
            assert_eq!(
                oracle.ood_pow_nonce.is_some(),
                params.ood_pow_bits[r] > 0,
                "OOD PoW nonce presence"
            );
            if let Some(nonce) = oracle.ood_pow_nonce {
                w.put(format!("whir_{r}_ood_nonce"), &nonce.to_be_bytes());
            }
            w.put(
                format!("whir_{r}_ood"),
                &oracle.ood_samples[0].to_u128().to_be_bytes(),
            );
            w.put(format!("whir_{r}_pow_nonce"), &nonces[r].to_be_bytes());
        } else {
            w.put(
                format!("whir_{r}_monomials"),
                &write_fe_run(&wp.final_monomials),
            );
            w.put(format!("whir_{r}_pow_nonce"), &nonces[r].to_be_bytes());
        }
        for q in 0..params.queries[r] {
            if r == 0 {
                for (name, oracle) in [
                    ("memory", &wp.memory_commitment),
                    ("setup", &wp.setup_commitment),
                ] {
                    let query = &oracle.queries[q];
                    w.put(
                        format!("whir_0_query_{q}_{name}_leaf"),
                        &write_fe_run(&base_leaf(
                            &query.leaf_values_concatenated,
                            oracle.num_columns,
                        )),
                    );
                    // the setup path stops at the setup frontier
                    let kept = if name == "setup" {
                        query.path.len() - params.setup_frontier_skip()
                    } else {
                        query.path.len()
                    };
                    w.put(
                        format!("whir_0_query_{q}_{name}_path"),
                        &digests(&query.path[..kept]),
                    );
                }
            } else {
                let oracle = &wp.intermediate_whir_oracles[r - 1];
                let query = &oracle.queries[q];
                w.put(
                    format!("whir_{r}_query_{q}_leaf"),
                    &write_fe_run(&query.leaf_values_concatenated),
                );
                w.put(format!("whir_{r}_query_{q}_path"), &digests(&query.path));
            }
        }
    }
    assert!(steps.next().is_none(), "unconsumed WHIR sumcheck steps");
}
