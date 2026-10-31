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
    schedule_coefficient_bank_fill_pr, schedule_coefficient_range_fill_pr,
    schedule_coefficient_tables_upload_pr, CoeffMonomialPr, CoefficientBankPr,
    CoefficientLayerRangesPr, CoefficientTablesHostPr, PR_COEFF_CHALLENGES,
    PR_COEFF_CHALLENGE_ABSENT, PR_COEFF_PLAN_DIRECT, PR_COEFF_PLAN_SCALED,
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
            WindowCoefficientPlan::Scaled { recipe, scalar } => {
                *evaluate_recipe(recipe, challenges, batching, top_bits)
                    .mul_assign(&PR::from_u128_with_reduction(*scalar))
            }
            WindowCoefficientPlan::LinearBasis { .. } => panic!("Proth120 LinearBasis plan"),
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

#[test]
fn cpu_pr_coefficient_tables_cover_programs() {
    let programs = programs();
    let top_bits = fixture_top_bits(&programs);
    let tables = CoefficientTablesHostPr::build(&programs, &top_bits);
    assert_eq!(tables.layers.len(), 5);
    let mut r0_plans = Vec::new();
    let mut continuation_recipes = Vec::new();
    let mut immediates = Vec::new();
    for (layer, ranges) in tables.layers.iter().enumerate() {
        assert_eq!(
            ranges.r0_len as usize,
            programs.r0[layer].window.coefficient_plans.len() + 2
        );
        assert_eq!(
            ranges.continuation_len as usize,
            programs.continuations.layers[layer]
                .coefficients
                .coefficients
                .len()
                + 2
        );
        r0_plans.push(ranges.r0_len - 2);
        continuation_recipes.push(ranges.continuation_len - 2);
        immediates.push((
            ranges.r0_immediates.len(),
            ranges.continuation_immediates.len(),
        ));
    }
    assert_eq!(r0_plans, [276, 32, 21, 11, 9]);
    assert_eq!(continuation_recipes, [265, 32, 21, 11, 9]);
    assert_eq!(immediates, [(17, 17), (0, 0), (0, 0), (0, 0), (0, 0)]);
    let r0_terms: usize = programs
        .r0
        .iter()
        .flat_map(|layer| &layer.window.coefficient_plans)
        .map(|plan| match plan {
            WindowCoefficientPlan::Direct(recipe)
            | WindowCoefficientPlan::Scaled { recipe, .. } => recipe.terms.len(),
            WindowCoefficientPlan::LinearBasis { .. } => {
                panic!("Proth120 coefficient tables do not support LinearBasis")
            }
        })
        .sum();
    let continuation_terms: usize = programs
        .continuations
        .layers
        .iter()
        .flat_map(|layer| &layer.coefficients.coefficients)
        .map(|recipe| recipe.terms.len())
        .sum();
    assert!(tables.monomials.len() <= r0_terms + continuation_terms + 4 * tables.layers.len());
    assert!(tables.scalars.is_empty());
    for monomial in &tables.monomials {
        for index in [monomial.challenge_idx_0, monomial.challenge_idx_1] {
            assert!(index == PR_COEFF_CHALLENGE_ABSENT || usize::from(index) < PR_COEFF_CHALLENGES);
        }
    }
    let top_bit_products = programs
        .continuations
        .layers
        .iter()
        .flat_map(|layer| &layer.coefficients.coefficients)
        .flat_map(|recipe| &recipe.terms)
        .filter(|product| !product.inits_and_teardowns_top_bits.is_empty())
        .count();
    println!(
        "GKR_T5_BANK recipes={} monomials={} scalars={} immediates={} r0_plans={:?} continuation_recipes={:?} top_bit_products={}",
        tables.recipes.len(),
        tables.monomials.len(),
        tables.scalars.len(),
        tables.immediates.len(),
        r0_plans,
        continuation_recipes,
        top_bit_products
    );
}

#[test]
#[cfg(not(no_cuda))]
fn pr_eval_coefficients_matches_host() {
    let context = make_context();
    let programs = programs();
    let top_bits = fixture_top_bits(&programs);
    let host = CoefficientTablesHostPr::build(&programs, &top_bits);
    let (tables, keepalive) = schedule_coefficient_tables_upload_pr(&host, &context).unwrap();
    let mut rng = StdRng::seed_from_u64(0xba4c);
    let poison = PR::from_u128_with_reduction(0x0bad_cafe);
    for case in 0..3 {
        let challenges: Vec<PR> = (0..PR_COEFF_CHALLENGES)
            .map(|_| match case {
                0 => PR::ZERO,
                1 => PR::ONE,
                _ => random_canonical(&mut rng),
            })
            .collect();
        let batchings: Vec<PR> = (0..tables.layers().len())
            .map(|_| match case {
                0 => PR::ZERO,
                1 => PR::ONE,
                _ => random_canonical(&mut rng),
            })
            .collect();
        let d_challenges = upload(&challenges, &context);
        let d_batchings = upload(&batchings, &context);
        for layer in (0..tables.layers().len()).rev() {
            let mut bank = CoefficientBankPr::new(&tables, layer, &context).unwrap();
            let poisoned = vec![poison; bank.len()];
            let poisoned = upload(&poisoned, &context);
            unsafe {
                era_cudart::memory::memory_copy_async(
                    era_cudart::slice::DeviceSlice::from_raw_parts_mut(
                        bank.values().cast_mut(),
                        bank.len(),
                    ),
                    &poisoned,
                    context.get_exec_stream(),
                )
                .unwrap();
            }
            schedule_coefficient_bank_fill_pr(
                &tables,
                &mut bank,
                d_challenges.as_ptr(),
                unsafe { d_batchings.as_ptr().add(layer) },
                &context,
            )
            .unwrap();
            let actual = read_back(
                unsafe {
                    era_cudart::slice::DeviceSlice::from_raw_parts(bank.values(), bank.len())
                },
                PR::ZERO,
                &context,
            );
            let expected =
                expected_layer(&programs, layer, &challenges, batchings[layer], &top_bits);
            assert_eq!(actual.len(), expected.len());
            for (slot, (actual, expected)) in actual.iter().zip(&expected).enumerate() {
                assert_eq!(actual, expected, "case {case} layer {layer} slot {slot}");
            }
            let r0 = bank.r0();
            let continuation = bank.continuation();
            assert_eq!(
                r0.coefficient_count + continuation.coefficient_count,
                bank.len()
            );
            assert_eq!(
                r0.immediate_count,
                programs.r0[layer].window.immediates.len()
            );
            assert_eq!(
                continuation.immediate_count,
                programs.main_tail[layer].immediates.len()
            );
            for (view, source) in [
                (r0, &programs.r0[layer].window.immediates),
                (continuation, &programs.main_tail[layer].immediates),
            ] {
                if view.immediate_count == 0 {
                    assert!(view.immediates.is_null());
                    continue;
                }
                let actual = read_back(
                    unsafe {
                        era_cudart::slice::DeviceSlice::from_raw_parts(
                            view.immediates,
                            view.immediate_count,
                        )
                    },
                    PR::ZERO,
                    &context,
                );
                let expected: Vec<PR> = source
                    .iter()
                    .map(|&value| PR::from_u128_with_reduction(value))
                    .collect();
                assert_eq!(actual, expected, "layer {layer} immediates");
            }
        }
        assert_eq!(read_back(&d_challenges, PR::ZERO, &context), challenges);
    }
    context.get_exec_stream().synchronize().unwrap();
    drop(keepalive);
}

fn synthetic_tables(counts: &[usize]) -> CoefficientTablesHostPr {
    let mut tables = CoefficientTablesHostPr::default();
    for (slot, &count) in counts.iter().enumerate() {
        let monomials: Vec<(PR, CoeffMonomialPr)> = (0..count)
            .map(|i| {
                (
                    PR::from_u128_with_reduction(((slot * 31 + i + 1) as u128) << 90 | 7),
                    CoeffMonomialPr {
                        batch_power: [0, u16::MAX, 1, 31, 255][i % 5],
                        challenge_idx_0: if i.is_multiple_of(3) {
                            PR_COEFF_CHALLENGE_ABSENT
                        } else {
                            (i % PR_COEFF_CHALLENGES) as u8
                        },
                        challenge_idx_1: if i.is_multiple_of(4) {
                            PR_COEFF_CHALLENGE_ABSENT
                        } else {
                            ((i * 7 + 3) % PR_COEFF_CHALLENGES) as u8
                        },
                        power_0: [0, 1, 31, u8::MAX][i % 4],
                        power_1: [1, 0, 2, u8::MAX][i % 4],
                        _pad: [0; 2],
                    },
                )
            })
            .collect();
        let scalar = (slot % 2 == 1).then(|| PR::from_u128_with_reduction(slot as u128 + 2));
        tables.push_monomials(&monomials, scalar);
    }
    tables.layers.push(CoefficientLayerRangesPr {
        recipe_first: 0,
        r0_len: counts.len() as u32,
        continuation_len: 0,
        r0_immediates: 0..0,
        continuation_immediates: 0..0,
    });
    tables
}

fn evaluate_synthetic(
    tables: &CoefficientTablesHostPr,
    challenges: &[PR],
    batching: PR,
) -> Vec<PR> {
    tables
        .recipes
        .iter()
        .map(|recipe| {
            let mut sum = PR::ZERO;
            let start = recipe.monomial_offset as usize;
            for index in start..start + recipe.monomial_count as usize {
                let monomial = tables.monomials[index];
                let mut term = tables.monomial_coeffs[index];
                term.mul_assign(&batching.pow(u32::from(monomial.batch_power)));
                for (challenge, power) in [
                    (monomial.challenge_idx_0, monomial.power_0),
                    (monomial.challenge_idx_1, monomial.power_1),
                ] {
                    if challenge != PR_COEFF_CHALLENGE_ABSENT {
                        term.mul_assign(&challenges[challenge as usize].pow(u32::from(power)));
                    }
                }
                sum.add_assign(&term);
            }
            match recipe.kind {
                PR_COEFF_PLAN_DIRECT => {}
                PR_COEFF_PLAN_SCALED => {
                    sum.mul_assign(&tables.scalars[recipe.scalar_index as usize]);
                }
                kind => panic!("unknown plan kind {kind}"),
            }
            sum
        })
        .collect()
}

#[test]
#[cfg(not(no_cuda))]
fn pr_eval_coefficients_synthetic_ranges() {
    let context = make_context();
    let counts = [0usize, 1, 2, 3, 31, 32, 33, 63, 64, 65, 297, 5, 1];
    let host = synthetic_tables(&counts);
    let (tables, keepalive) = schedule_coefficient_tables_upload_pr(&host, &context).unwrap();
    let mut rng = StdRng::seed_from_u64(0x5e7);
    let challenges: Vec<PR> = (0..PR_COEFF_CHALLENGES)
        .map(|_| random_canonical(&mut rng))
        .collect();
    let batching = random_canonical(&mut rng);
    let expected = evaluate_synthetic(&host, &challenges, batching);
    let d_challenges = upload(&challenges, &context);
    let d_batching = upload(&[batching], &context);
    let poison = PR::from_u128_with_reduction(991);
    for (first, count) in [(0usize, counts.len()), (4, 7), (10, 1)] {
        let mut d_bank = upload(&vec![poison; count + 2], &context);
        schedule_coefficient_range_fill_pr(
            &tables,
            first as u32,
            count as u32,
            d_challenges.as_ptr(),
            d_batching.as_ptr(),
            unsafe { d_bank.as_mut_ptr().add(1) },
            &context,
        )
        .unwrap();
        let actual = read_back(&d_bank, PR::ZERO, &context);
        assert_eq!(actual[0], poison);
        assert_eq!(actual[count + 1], poison);
        assert_eq!(&actual[1..count + 1], &expected[first..first + count]);
    }
    context.get_exec_stream().synchronize().unwrap();
    drop(keepalive);
}
