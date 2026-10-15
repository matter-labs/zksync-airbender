//! F1 GKR section and the E1 round-polynomial factorization.

use cs::definitions::split_timestamp;
use field::{Field, Proth120};
use prover::gkr::prover::CommitmentMode;

use super::digest::digest_wire;
use super::params::FormatParams;
use super::replay::{dim_reducing_layers, GkrReplay};
use super::runs::{write_fe_run, write_ts_run};
use super::Writer;
use crate::seed::{Circuit, Proof};

fn add(a: Proth120, b: Proth120) -> Proth120 {
    let mut s = a;
    s.add_assign(&b);
    s
}

fn sub(a: Proth120, b: Proth120) -> Proth120 {
    let mut s = a;
    s.sub_assign(&b);
    s
}

fn mul(a: Proth120, b: Proth120) -> Proth120 {
    let mut s = a;
    s.mul_assign(&b);
    s
}

/// `(1 − z, 2z − 1)`: `e_z(X) = (1 − z) + (2z − 1)·X`.
fn eq_factor(z: Proth120) -> (Proth120, Proth120) {
    (sub(Proth120::ONE, z), sub(add(z, z), Proth120::ONE))
}

/// The monomial round polynomial `p̃ = e_z·u` of `u = a + bX + cX²`.
pub fn join_round(u: [Proth120; 3], z: Proth120) -> [Proth120; 4] {
    let [a, b, c] = u;
    let (t, s) = eq_factor(z);
    [
        mul(t, a),
        add(mul(t, b), mul(s, a)),
        add(mul(t, c), mul(s, b)),
        mul(s, c),
    ]
}

/// The quadratic `u` with `p̃ = e_z·u`. Panics when `p̃` has no such factor.
pub fn split_round(p: &[Proth120; 4], z: Proth120) -> [Proth120; 3] {
    let (t, s) = eq_factor(z);
    let u = match (t.inverse(), s.inverse()) {
        (Some(t_inv), Some(s_inv)) => {
            let c = mul(p[3], s_inv);
            let b = mul(sub(p[2], mul(t, c)), s_inv);
            [mul(p[0], t_inv), b, c]
        }
        // z = 1/2: e_z is the constant 1/2
        (Some(t_inv), None) => [mul(p[0], t_inv), mul(p[1], t_inv), mul(p[2], t_inv)],
        // z = 1: e_z(X) = X
        (None, Some(_)) => [p[1], p[2], p[3]],
        (None, None) => unreachable!("1 − z and 2z − 1 cannot both vanish"),
    };
    assert_eq!(
        join_round(u, z),
        *p,
        "round polynomial is not e_z(X) times a quadratic"
    );
    u
}

/// `a = K − z·(b + c)`: the constant term fixed by `p̃(0) + p̃(1) = a + z·(b + c) = K`.
pub fn round_constant(k: Proth120, z: Proth120, b: Proth120, c: Proth120) -> Proth120 {
    sub(k, mul(z, add(b, c)))
}

/// `u(r) = a + b·r + c·r²`: the next round's `K`.
pub fn eval_quadratic(u: [Proth120; 3], r: Proth120) -> Proth120 {
    add(u[0], mul(r, add(u[1], mul(r, u[2]))))
}

/// The `(b, c)` pairs of every round of `layer` (E1).
fn e1_coefficients(proof: &Proof, layer: usize, z: &[Proth120]) -> Vec<Proth120> {
    let siv = &proof.sumcheck_intermediate_values[&layer];
    siv.internal_round_coefficients
        .iter()
        .zip(z)
        .flat_map(|(c, z)| {
            let [_, b, c] = split_round(c.as_multilinear(), *z);
            [b, c]
        })
        .collect()
}

pub(super) fn encode_gkr(
    w: &mut Writer,
    circuit: &Circuit,
    proof: &Proof,
    aux: &CommitmentMode,
    params: &FormatParams,
    replay: &GkrReplay,
) {
    let CommitmentMode::MergedAndPackedMemoryAndWitness {
        register_final_state,
        final_timestamp,
        ..
    } = aux
    else {
        panic!("expected packed commitment mode");
    };
    let registers: Vec<u8> = register_final_state
        .iter()
        .flat_map(|r| r.value.to_le_bytes())
        .collect();
    w.put("gkr_registers", &registers);
    let timestamps: Vec<(u32, u32)> = register_final_state
        .iter()
        .map(|r| split_timestamp(r.last_access_timestamp))
        .chain(std::iter::once(split_timestamp(*final_timestamp)))
        .collect();
    w.put("gkr_timestamps", &write_ts_run(&timestamps));
    let top_bits: Vec<u8> = proof
        .inits_and_teardowns_top_bits
        .iter()
        .flat_map(|t| t.to_le_bytes())
        .collect();
    w.put("gkr_top_bits", &top_bits);
    let memory_cap = &proof.whir_proof.memory_commitment.commitment.cap.cap;
    assert_eq!(memory_cap.len(), params.cap(), "memory cap size");
    let memory_cap: Vec<u8> = memory_cap
        .iter()
        .flat_map(|d| digest_wire(d, params.digest_bytes))
        .collect();
    w.put("gkr_memory_cap", &memory_cap);
    w.put(
        "gkr_external_pow_nonce",
        &proof.lookup_challenges_pow_nonce.to_be_bytes(),
    );

    let output_evals: Vec<Proth120> = proof
        .final_explicit_evaluations
        .values()
        .flat_map(|v| {
            assert_eq!(v[0].len(), 1 << params.explicit_output_log2);
            v[0].iter().chain(v[1].iter())
        })
        .copied()
        .collect();
    w.put("gkr_output_evals", &write_fe_run(&output_evals));

    let dim_layers = dim_reducing_layers(circuit, proof);
    assert_eq!(
        dim_layers.len(),
        params.trace_log2 - params.explicit_output_log2,
        "dimension-reducing layer count"
    );
    let mut points = replay.layers.iter();
    for layer in dim_layers {
        let lp = points.next().unwrap();
        assert_eq!(lp.layer, layer);
        w.put(
            format!("gkr_dr_{layer}_rounds"),
            &write_fe_run(&e1_coefficients(proof, layer, &lp.z)),
        );
        let lines: Vec<Proth120> = proof.sumcheck_intermediate_values[&layer]
            .final_step_evaluations
            .values()
            .flat_map(|v| [v[0], v[1]])
            .collect();
        w.put(format!("gkr_dr_{layer}_lines"), &write_fe_run(&lines));
    }
    for layer in (0..circuit.layers.len()).rev() {
        let lp = points.next().unwrap();
        assert_eq!(lp.layer, layer);
        assert_eq!(lp.z.len(), params.trace_log2, "standard layer rounds");
        w.put(
            format!("gkr_layer_{layer}_rounds"),
            &write_fe_run(&e1_coefficients(proof, layer, &lp.z)),
        );
        w.put(
            format!("gkr_layer_{layer}_evals"),
            &write_fe_run(&crate::flatten::circuit_layer_evals(circuit, proof, layer)),
        );
    }
    assert!(points.next().is_none());
    w.put(
        "gkr_batching_pow_nonce",
        &proof.batched_proximity_check_pow_nonce.to_be_bytes(),
    );
}
