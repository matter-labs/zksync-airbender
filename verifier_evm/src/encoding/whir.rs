//! F1 WHIR section (single-tx: the committed-state header comes from the GKR verifier).

use field::Proth120;

use super::digest::digest_wire;
use super::params::FormatParams;
use super::runs::write_fe_run;
use super::Writer;
use crate::seed::Proof;

/// Base-oracle leaf values in v0 order: column-major (`flatten.rs` `push_base`).
pub(crate) fn base_leaf(vals: &[Proth120], num_columns: usize) -> Vec<Proth120> {
    assert!(vals.len().is_multiple_of(num_columns));
    let vp = vals.len() / num_columns;
    (0..num_columns)
        .flat_map(|c| (0..vp).map(move |o| vals[o * num_columns + c]))
        .collect()
}

fn digests(path: &[[u32; 8]], params: &FormatParams) -> Vec<u8> {
    path.iter()
        .flat_map(|d| digest_wire(d, params.digest_bytes))
        .collect()
}

pub(super) fn encode_whir(w: &mut Writer, proof: &Proof, params: &FormatParams) {
    let wp = &proof.whir_proof;
    let num_rounds = params.folds.len();
    let mut steps = wp.sumcheck_polys.iter();
    for r in 0..num_rounds {
        let sumcheck: Vec<Proth120> = (0..params.folds[r])
            .flat_map(|_| {
                let sp = steps.next().expect("missing WHIR sumcheck step");
                [sp[0], sp[2]] // E2: c1 = claim − 2·c0 − c2
            })
            .collect();
        w.put(format!("whir_{r}_sumcheck"), &write_fe_run(&sumcheck));
        if r < num_rounds - 1 {
            let cap = &wp.intermediate_whir_oracles[r].commitment.cap.cap;
            assert_eq!(cap.len(), params.cap(), "intermediate cap size");
            w.put(format!("whir_{r}_cap"), &digests(cap, params));
            w.put(
                format!("whir_{r}_ood"),
                &wp.ood_samples[r].to_u128().to_be_bytes(),
            );
            w.put(
                format!("whir_{r}_pow_nonce"),
                &wp.pow_nonces[r].to_be_bytes(),
            );
        } else {
            w.put(
                format!("whir_{r}_monomials"),
                &write_fe_run(&wp.final_monomials),
            );
            w.put(
                format!("whir_{r}_pow_nonce"),
                &wp.pow_nonces[r].to_be_bytes(),
            );
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
                        &digests(&query.path[..kept], params),
                    );
                }
            } else {
                let oracle = &wp.intermediate_whir_oracles[r - 1];
                let query = &oracle.queries[q];
                w.put(
                    format!("whir_{r}_query_{q}_leaf"),
                    &write_fe_run(&query.leaf_values_concatenated),
                );
                w.put(
                    format!("whir_{r}_query_{q}_path"),
                    &digests(&query.path, params),
                );
            }
        }
    }
    assert!(steps.next().is_none(), "unconsumed WHIR sumcheck steps");
}
