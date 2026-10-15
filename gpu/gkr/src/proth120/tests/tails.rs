use std::collections::BTreeMap;
use std::panic::{catch_unwind, AssertUnwindSafe};

use field::Field;
use gpu_core::primitives::field::PR;
use gpu_prover_context::ProverContext;
use prover::transcript::{Keccak256Transcript, Transcript};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use super::{make_context, panic_message, read_back, upload};
use crate::backward::{derive_dimension_reducing_inputs, GKR_DIM_REDUCING_SLOTS};
use crate::proth120::backward::dr_tail::{
    dimension_reducing_slots_pr, encode_dr_tail_slots_pr, launch_dr_tail_megakernel_pr,
    preflight_dr_tail_resources_pr, DrTailLayerPlanPr, DrTailMegakernelDescPr, DrTailSlotPr,
    PR_DR_TAIL_MAX_SOURCES,
};
use crate::proth120::backward::window_dr::schedule_dr_batch_challenge_table_pr;
use crate::proth120::programs::GkrProgramsPr;
use crate::upstream::{DimensionReducingInputOutput, OutputType};

const PAIRWISE_SLOTS: u32 = (1 << 0) | (1 << 4);

fn add(a: PR, b: PR) -> PR {
    *a.clone().add_assign(&b)
}

fn sub(a: PR, b: PR) -> PR {
    *a.clone().sub_assign(&b)
}

fn mul(a: PR, b: PR) -> PR {
    *a.clone().mul_assign(&b)
}

fn random_pr(rng: &mut StdRng) -> PR {
    PR::from_u128_with_reduction(rng.random())
}

fn eq_weight(tau: PR, bit: bool) -> PR {
    if bit {
        tau
    } else {
        sub(PR::ONE, tau)
    }
}

fn eq_rows(tau: &[PR]) -> Vec<PR> {
    let mut rows = vec![PR::ONE];
    for (k, &coordinate) in tau.iter().enumerate() {
        let mut next = vec![PR::ZERO; rows.len() << 1];
        for (index, value) in next.iter_mut().enumerate() {
            *value = mul(
                rows[index & ((1 << k) - 1)],
                eq_weight(coordinate, (index >> k) & 1 == 1),
            );
        }
        rows = next;
    }
    rows
}

fn lsb_fold(column: &[PR], challenge: PR) -> Vec<PR> {
    (0..column.len() / 2)
        .map(|cell| {
            let ancestor = 4 * (cell / 2) + (cell & 1);
            add(
                column[ancestor],
                mul(challenge, sub(column[ancestor + 2], column[ancestor])),
            )
        })
        .collect()
}

fn slot_terms(
    columns: &[Vec<PR>],
    slots: &[DrTailSlotPr; GKR_DIM_REDUCING_SLOTS],
    enabled_mask: u32,
    table: &[PR],
    row: usize,
) -> [PR; 3] {
    let at = |column: &[PR], x: usize, gate: usize| column[4 * row + 2 * x + gate];
    let delta = |column: &[PR], gate: usize| sub(at(column, 1, gate), at(column, 0, gate));
    let mut terms = [PR::ZERO; 3];
    for (slot_idx, slot) in slots.iter().enumerate() {
        if enabled_mask & (1 << slot_idx) == 0 {
            continue;
        }
        if PAIRWISE_SLOTS & (1 << slot_idx) != 0 {
            for input in 0..2 {
                let column = &columns[slot.input_source[input] as usize];
                let weight = table[slot.batch_exp[input] as usize];
                let values = [
                    mul(at(column, 0, 0), at(column, 0, 1)),
                    mul(at(column, 1, 0), at(column, 1, 1)),
                    mul(delta(column, 0), delta(column, 1)),
                ];
                for (term, value) in terms.iter_mut().zip(values) {
                    *term = add(*term, mul(weight, value));
                }
            }
        } else {
            let a = &columns[slot.input_source[0] as usize];
            let b = &columns[slot.input_source[1] as usize];
            let numerator =
                |x: usize| add(mul(at(a, x, 0), at(b, x, 1)), mul(at(a, x, 1), at(b, x, 0)));
            let denominator = |x: usize| mul(at(b, x, 0), at(b, x, 1));
            let numerators = [
                numerator(0),
                numerator(1),
                add(mul(delta(a, 0), delta(b, 1)), mul(delta(a, 1), delta(b, 0))),
            ];
            let denominators = [
                denominator(0),
                denominator(1),
                mul(delta(b, 0), delta(b, 1)),
            ];
            let w0 = table[slot.batch_exp[0] as usize];
            let w1 = table[slot.batch_exp[1] as usize];
            for k in 0..3 {
                terms[k] = add(
                    terms[k],
                    add(mul(w0, numerators[k]), mul(w1, denominators[k])),
                );
            }
        }
    }
    terms
}

fn round_sums(
    columns: &[Vec<PR>],
    slots: &[DrTailSlotPr; GKR_DIM_REDUCING_SLOTS],
    enabled_mask: u32,
    table: &[PR],
    tau: &[PR],
    round: usize,
    folding_steps: usize,
) -> [PR; 3] {
    let round_eq = eq_rows(&tau[round + 1..folding_steps]);
    assert_eq!(round_eq.len(), columns[0].len() / 4);
    let mut sums = [PR::ZERO; 3];
    for (row, weight) in round_eq.iter().enumerate() {
        let terms = slot_terms(columns, slots, enabled_mask, table, row);
        for (sum, term) in sums.iter_mut().zip(terms) {
            *sum = add(*sum, mul(*weight, term));
        }
    }
    sums
}

fn cubic_round_message(h0: PR, h1: PR, hinf: PR, tau: PR) -> [PR; 4] {
    let h1x = sub(sub(h1, h0), hinf);
    let e0 = sub(PR::ONE, tau);
    let e1 = sub(tau, e0);
    [
        mul(e0, h0),
        add(mul(e0, h1x), mul(e1, h0)),
        add(mul(e0, hinf), mul(e1, h1x)),
        mul(e1, hinf),
    ]
}

fn horner4(coefficients: &[PR; 4], point: PR) -> PR {
    coefficients
        .iter()
        .rev()
        .fold(PR::ZERO, |acc, &coefficient| {
            add(mul(acc, point), coefficient)
        })
}

fn check_tail_case(
    context: &ProverContext,
    programs: &GkrProgramsPr,
    layer: &DrTailLayerPlanPr,
    layer_map: &BTreeMap<OutputType, DimensionReducingInputOutput>,
    rng: &mut StdRng,
) {
    let n = layer.folding_steps();
    let capacity = layer.capacity();
    let entry = capacity.entry_round;
    let sources = layer.canonical_sources();
    let layer_slots = dimension_reducing_slots_pr(layer_map);
    let enabled_mask = layer_slots.enabled_mask();
    let slots = encode_dr_tail_slots_pr(
        &layer_slots,
        sources,
        Some(&programs.storage_layout.aliases),
    );
    let len = 1usize << (n + 1);
    let columns: Vec<Vec<PR>> = (0..sources.len())
        .map(|_| (0..len).map(|_| random_pr(rng)).collect())
        .collect();
    let d_columns = upload(&columns.concat(), context);
    let mut source_ptrs = [core::ptr::null(); PR_DR_TAIL_MAX_SOURCES];
    for (index, pointer) in source_ptrs.iter_mut().take(sources.len()).enumerate() {
        *pointer = unsafe { d_columns.as_ptr().add(index * len) };
    }
    let tau: Vec<PR> = (0..=n).map(|_| random_pr(rng)).collect();
    let d_tau = upload(&tau, context);
    let d_table =
        schedule_dr_batch_challenge_table_pr(unsafe { d_tau.as_ptr().add(n) }, context).unwrap();
    let mut table = vec![PR::ONE];
    for _ in 1..10 {
        table.push(mul(*table.last().unwrap(), tau[n]));
    }
    assert_eq!(
        read_back(&d_table, PR::ZERO, context),
        table,
        "batch powers"
    );

    let mut challenges = vec![PR::ZERO; n + 2];
    let mut folded = columns.clone();
    for challenge in challenges.iter_mut().take(entry) {
        *challenge = random_pr(rng);
        folded = folded
            .iter()
            .map(|column| lsb_fold(column, *challenge))
            .collect();
    }
    let entry_sums = round_sums(&folded, &slots, enabled_mask, &table, &tau, entry, n);
    let honest_sum = add(
        mul(sub(PR::ONE, tau[entry]), entry_sums[0]),
        mul(tau[entry], entry_sums[1]),
    );
    let eq_prefactor = random_pr(rng);
    let claim = mul(eq_prefactor, honest_sum);
    let seed_bytes: [u8; 32] = std::array::from_fn(|_| rng.random());

    let mut d_challenges = upload(&challenges, context);
    let mut d_seed = upload(&seed_bytes, context);
    let mut d_claim = upload(&[claim], context);
    let mut d_eq_prefactor = upload(&[eq_prefactor], context);
    let mut d_coeffs = upload(&vec![PR::ZERO; 4 * n], context);
    let mut d_final = upload(&vec![PR::ZERO; 4 * sources.len()], context);
    launch_dr_tail_megakernel_pr(
        DrTailMegakernelDescPr {
            enabled_mask,
            folding_steps: n as u32,
            entry_round: entry as u32,
            source_count: sources.len() as u32,
            source_ptrs,
            final_sources: d_final.as_mut_ptr(),
            tau: d_tau.as_ptr(),
            seed: d_seed.as_mut_ptr(),
            claim: d_claim.as_mut_ptr(),
            eq_prefactor: d_eq_prefactor.as_mut_ptr(),
            coeffs_out: d_coeffs.as_mut_ptr(),
            challenges_out: d_challenges.as_mut_ptr(),
            batch_challenges: d_table.as_ptr(),
            slots,
        },
        &capacity,
        context,
    )
    .unwrap();
    let device_coeffs = read_back(&d_coeffs, PR::ZERO, context);
    let device_challenges = read_back(&d_challenges, PR::ZERO, context);
    let device_seed = read_back(&d_seed, 0u8, context);
    let device_claim = read_back(&d_claim, PR::ZERO, context)[0];
    let device_eq_prefactor = read_back(&d_eq_prefactor, PR::ZERO, context)[0];
    let device_final = read_back(&d_final, PR::ZERO, context);

    let label = format!("layer {} (n = {n}, entry = {entry})", layer.layer_idx());
    assert!(
        device_coeffs[..4 * entry]
            .iter()
            .all(|value| *value == PR::ZERO),
        "{label}: rounds before the entry were written"
    );
    let mut seed = <Keccak256Transcript as Transcript<PR, PR>>::commit_initial_u32(&[]);
    seed.0 = seed_bytes;
    let mut host_claim = claim;
    let mut host_eq_prefactor = eq_prefactor;
    for round in entry..n {
        let sums = round_sums(&folded, &slots, enabled_mask, &table, &tau, round, n);
        let coefficients = cubic_round_message(sums[0], sums[1], sums[2], tau[round]);
        let normalized = mul(host_claim, host_eq_prefactor.inverse().unwrap());
        assert_eq!(
            add(
                add(coefficients[0], coefficients[0]),
                add(add(coefficients[1], coefficients[2]), coefficients[3])
            ),
            normalized,
            "{label}: round {round} host sumcheck identity"
        );
        assert_eq!(
            device_coeffs[4 * round..4 * round + 4],
            coefficients,
            "{label}: round {round} coefficients"
        );
        <Keccak256Transcript as Transcript<PR, PR>>::commit_base_field_elements(
            &mut seed,
            &device_coeffs[4 * round..4 * round + 4],
        );
        let mut drawn = [PR::ZERO];
        <Keccak256Transcript as Transcript<PR, PR>>::draw_random_field_elements(
            &mut seed, &mut drawn,
        );
        assert_eq!(
            device_challenges[round], drawn[0],
            "{label}: round {round} challenge"
        );
        host_claim = horner4(&coefficients, drawn[0]);
        host_eq_prefactor = add(
            mul(drawn[0], tau[round]),
            mul(sub(PR::ONE, drawn[0]), sub(PR::ONE, tau[round])),
        );
        if round + 1 < n {
            folded = folded
                .iter()
                .map(|column| lsb_fold(column, drawn[0]))
                .collect();
        }
    }
    assert_eq!(device_seed, seed.0, "{label}: final seed");
    assert_eq!(device_claim, host_claim, "{label}: final claim");
    assert_eq!(
        device_eq_prefactor, host_eq_prefactor,
        "{label}: final eq prefactor"
    );
    assert_eq!(device_final, folded.concat(), "{label}: final source cells");
    println!(
        "M6_DR_TAIL_CASE {label}: sources={} rounds={} transcript=match",
        sources.len(),
        n - entry
    );
    assert_eq!(
        device_challenges[..entry],
        challenges[..entry],
        "{label}: pending challenges changed"
    );
}

#[test]
#[cfg(not(no_cuda))]
fn pr_tail_round_update_matches_keccak() {
    let context = make_context();
    let programs = super::cpu_abi::programs();
    let rejected = catch_unwind(AssertUnwindSafe(|| {
        preflight_dr_tail_resources_pr(&programs, 5, &context)
    }))
    .unwrap_err();
    let final_log = crate::proth120::backward::dr_tail::PR_DR_FINAL_TRACE_LOG_2;
    assert!(panic_message(rejected).contains(&format!(
        "Proth120 DR tail supports final trace log {final_log} only"
    )));
    let plan = preflight_dr_tail_resources_pr(&programs, final_log, &context);
    plan.validate_before_enqueue(&programs, final_log, &context);
    println!("M6_DR_TAIL_ADMISSION {}", plan.admission_record());
    assert_eq!(
        plan.layers().len(),
        prover::gkr::prover_config::example_configs::l1_wrap_2p21::TRACE_LEN_LOG2
            - final_log as usize
    );
    let rejected = catch_unwind(AssertUnwindSafe(|| {
        plan.validate_before_enqueue(&programs, 5, &context)
    }))
    .unwrap_err();
    assert!(panic_message(rejected).contains("admitted for another final trace log"));
    let circuit = programs.runtime_circuit.as_ref();
    let layer_inputs = derive_dimension_reducing_inputs(
        circuit.layers.len(),
        &circuit.global_output_map,
        circuit.trace_len.trailing_zeros(),
        final_log,
    );
    let mut rng = StdRng::seed_from_u64(0xd7a1_5eed);
    let mut cursor = plan.cursor();
    for layer in plan.layers() {
        let capacity = cursor.bind(
            layer.layer_idx(),
            layer.folding_steps(),
            layer.canonical_sources(),
        );
        assert_eq!(capacity, layer.capacity());
        assert_eq!(
            plan.window_program(layer.layer_idx()).folding_steps(),
            layer.folding_steps()
        );
    }
    cursor.finish();
    for folding_steps in [2, 3, 4, 8, 11] {
        let layer = plan
            .layers()
            .iter()
            .find(|layer| layer.folding_steps() == folding_steps)
            .unwrap();
        check_tail_case(
            &context,
            &programs,
            layer,
            &layer_inputs[&layer.layer_idx()],
            &mut rng,
        );
    }
}
