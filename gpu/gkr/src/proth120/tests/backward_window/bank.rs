use field::{Field, PrimeField};
use gkr_eval_ir::{ChallengeKey, ChallengePower, PermutationSlot};
use gpu_core::primitives::field::PR;
use gpu_gkr_compiler::{CoefficientRecipeId, NormalizedCoefficientRecipe, WindowCoefficientPlan};
use rand::rngs::StdRng;
use rand::SeedableRng;

use super::super::cpu_abi::programs;
use super::super::{make_context, read_back, upload};
use super::random_canonical;
use crate::proth120::backward::banks::{
    coefficient_bank_device_ptr_pr, schedule_coefficient_bank_fill_pr, CoefficientBankHostPr,
    CoefficientBankPr, PR_COEFF_CHALLENGES, PR_COEFF_CHALLENGE_ABSENT,
};
use crate::proth120::programs::GkrProgramsPr;

fn challenge_value(key: &ChallengeKey, challenges: &[PR], batching: PR) -> PR {
    match key {
        ChallengeKey::PermutationLinearization(slot) => {
            challenges[match slot {
                PermutationSlot::AddressLow => {
                    cs::definitions::PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX
                }
                PermutationSlot::AddressHigh => {
                    cs::definitions::PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX
                }
                PermutationSlot::TimestampLow => {
                    cs::definitions::PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX
                }
                PermutationSlot::TimestampHigh => {
                    cs::definitions::PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX
                }
                PermutationSlot::ValueLow => {
                    cs::definitions::PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX
                }
                PermutationSlot::ValueHigh => {
                    cs::definitions::PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX
                }
            }]
        }
        ChallengeKey::PermutationAdditive => {
            challenges[crate::upstream::NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES]
        }
        ChallengeKey::LookupMultiplicative => challenges[7],
        ChallengeKey::LookupAdditive => challenges[8],
        ChallengeKey::ClaimBatching => batching,
    }
}

fn evaluate_recipe(
    recipe: &NormalizedCoefficientRecipe,
    challenges: &[PR],
    batching: PR,
    top_bits: &[u32],
) -> PR {
    let mut sum = PR::ZERO;
    for product in &recipe.terms {
        let mut term = PR::from_u128_with_reduction(product.scalar);
        for reference in &product.inits_and_teardowns_top_bits {
            let shifted = top_bits[reference.set_index]
                .checked_shl(reference.shift)
                .unwrap_or(0);
            term.mul_assign(&PR::from_u32_with_reduction(shifted));
        }
        for challenge in &product.challenges {
            let power = match challenge.0.power {
                ChallengePower::One => 1u32,
                ChallengePower::Static(power) => power,
            };
            term.mul_assign(&challenge_value(&challenge.0.key, challenges, batching).pow(power));
        }
        sum.add_assign(&term);
    }
    sum
}

fn expected_layer(
    programs: &GkrProgramsPr,
    layer: usize,
    challenges: &[PR],
    batching: PR,
    top_bits: &[u32],
) -> Vec<PR> {
    let literals = [CoefficientRecipeId::ONE, CoefficientRecipeId::NEG_ONE]
        .map(|literal| literal.literal::<PR>().unwrap());
    let mut values = literals.to_vec();
    for plan in &programs.r0[layer].window.coefficient_plans {
        values.push(match plan {
            WindowCoefficientPlan::Direct(recipe) => {
                evaluate_recipe(recipe, challenges, batching, top_bits)
            }
            _ => panic!("Proth120 coefficient plan must be Direct"),
        });
    }
    values.extend(literals);
    for recipe in &programs.continuations.layers[layer]
        .coefficients
        .coefficients
    {
        values.push(evaluate_recipe(recipe, challenges, batching, top_bits));
    }
    values
}

fn fixture_top_bits(programs: &GkrProgramsPr) -> Vec<u32> {
    (0..programs.runtime_circuit.memory_layout.teardown_sets.len())
        .map(|index| 0x1234_5678u32.rotate_left(7 * index as u32) ^ 0x8000_0001)
        .collect()
}

fn evaluate_bank(host: &CoefficientBankHostPr, challenges: &[PR], batching: PR) -> Vec<PR> {
    host.recipes
        .iter()
        .map(|recipe| {
            let mut sum = PR::ZERO;
            let first = recipe.monomial_offset as usize;
            for (monomial, coefficient) in host.monomials
                [first..first + recipe.monomial_count as usize]
                .iter()
                .zip(&host.monomial_coeffs[first..])
            {
                let mut term = *coefficient;
                term.mul_assign(&batching.pow(u32::from(monomial.batch_power)));
                for (slot, power) in [
                    (monomial.challenge_idx_0, monomial.power_0),
                    (monomial.challenge_idx_1, monomial.power_1),
                ] {
                    if slot != PR_COEFF_CHALLENGE_ABSENT {
                        term.mul_assign(&challenges[usize::from(slot)].pow(u32::from(power)));
                    }
                }
                sum.add_assign(&term);
            }
            sum
        })
        .collect()
}

#[test]
fn cpu_pr_coefficient_tables_cover_programs() {
    let programs = programs();
    let mut rng = StdRng::seed_from_u64(0xba4c);
    let sets = programs.runtime_circuit.memory_layout.teardown_sets.len();
    for top_bits in [
        vec![0; sets],
        vec![1; sets],
        vec![u32::MAX; sets],
        fixture_top_bits(&programs),
    ] {
        for case in 0..3 {
            let challenges: Vec<PR> = (0..PR_COEFF_CHALLENGES)
                .map(|_| match case {
                    0 => PR::ZERO,
                    1 => PR::ONE,
                    _ => random_canonical(&mut rng),
                })
                .collect();
            let batching = match case {
                0 => PR::ZERO,
                1 => PR::ONE,
                _ => random_canonical(&mut rng),
            };
            for layer in 0..programs.r0.len() {
                let mut actual = Vec::new();
                for r0 in [true, false] {
                    let host = CoefficientBankHostPr::build(&programs, layer, &top_bits, r0);
                    let chunks = host.chunks();
                    assert_eq!(chunks.len(), 1, "wrap layer {layer}, r0={r0}");
                    let chunk = &chunks[0];
                    assert_eq!(chunk.bank_first, 0);
                    assert_eq!(chunk.bank_count as usize, host.recipes.len());
                    assert_eq!(&chunk.recipes[..host.recipes.len()], host.recipes);
                    assert_eq!(&chunk.monomials[..host.monomials.len()], host.monomials);
                    assert_eq!(
                        &chunk.monomial_coeffs[..host.monomial_coeffs.len()],
                        host.monomial_coeffs
                    );
                    assert_eq!(&chunk.immediates[..host.immediates.len()], host.immediates);
                    actual.extend(evaluate_bank(&host, &challenges, batching));
                }
                assert_eq!(
                    actual,
                    expected_layer(&programs, layer, &challenges, batching, &top_bits),
                    "layer {layer}, case {case}, top_bits={top_bits:?}"
                );
            }
        }
    }
}

#[test]
#[cfg(not(no_cuda))]
fn pr_eval_coefficients_matches_host() {
    let context = make_context();
    let programs = programs();
    let top_bits = fixture_top_bits(&programs);
    let mut rng = StdRng::seed_from_u64(0xba4c);
    let poison = PR::from_u128_with_reduction(0x0bad_cafe);
    let symbol = coefficient_bank_device_ptr_pr().unwrap();
    for case in 0..3 {
        let challenges: Vec<PR> = (0..PR_COEFF_CHALLENGES)
            .map(|_| match case {
                0 => PR::ZERO,
                1 => PR::ONE,
                _ => random_canonical(&mut rng),
            })
            .collect();
        let batchings: Vec<PR> = (0..programs.r0.len())
            .map(|_| match case {
                0 => PR::ZERO,
                1 => PR::ONE,
                _ => random_canonical(&mut rng),
            })
            .collect();
        let d_challenges = upload(&challenges, &context);
        let d_batchings = upload(&batchings, &context);
        for layer in (0..programs.r0.len()).rev() {
            let mut bank = CoefficientBankPr::new(&programs, layer, &top_bits).unwrap();
            for view in [bank.r0(), bank.continuation()] {
                let len = view.coefficient_count + view.immediate_count;
                let poisoned = upload(&vec![poison; len], &context);
                unsafe {
                    era_cudart::memory::memory_copy_async(
                        era_cudart::slice::DeviceSlice::from_raw_parts_mut(
                            symbol.add(view.coefficient_offset as usize),
                            len,
                        ),
                        &poisoned,
                        context.get_exec_stream(),
                    )
                    .unwrap();
                }
            }
            schedule_coefficient_bank_fill_pr(
                &mut bank,
                d_challenges.as_ptr(),
                unsafe { d_batchings.as_ptr().add(layer) },
                &context,
            )
            .unwrap();
            let mut actual = Vec::new();
            for view in [bank.r0(), bank.continuation()] {
                actual.extend(read_back(
                    unsafe {
                        era_cudart::slice::DeviceSlice::from_raw_parts(
                            symbol.add(view.coefficient_offset as usize),
                            view.coefficient_count,
                        )
                    },
                    PR::ZERO,
                    &context,
                ));
            }
            assert_eq!(
                actual,
                expected_layer(&programs, layer, &challenges, batchings[layer], &top_bits),
                "case {case}, layer {layer}"
            );
            for (view, source) in [
                (bank.r0(), &programs.r0[layer].window.immediates),
                (bank.continuation(), &programs.main_tail[layer].immediates),
            ] {
                assert_eq!(view.immediate_count, source.len());
                if view.immediate_count == 0 {
                    continue;
                }
                let actual = read_back(
                    unsafe {
                        era_cudart::slice::DeviceSlice::from_raw_parts(
                            symbol.add(view.immediate_offset as usize),
                            view.immediate_count,
                        )
                    },
                    PR::ZERO,
                    &context,
                );
                let expected: Vec<PR> = source
                    .iter()
                    .map(|&v| PR::from_u128_with_reduction(v))
                    .collect();
                assert_eq!(actual, expected, "layer {layer} immediates");
            }
        }
        assert_eq!(read_back(&d_challenges, PR::ZERO, &context), challenges);
    }
    context.get_exec_stream().synchronize().unwrap();
}
