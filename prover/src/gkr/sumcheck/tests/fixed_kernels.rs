use cs::definitions::GKRAddress;
use field::{FieldExtension, Mersenne31Field, Mersenne31Quartic, PrimeField};

use crate::gkr::sumcheck::evaluation_kernels::*;

use super::utils::*;

type F = Mersenne31Field;
type E = Mersenne31Quartic;

#[test]
fn test_initial_grand_product() {
    const FOLDING_STEPS: usize = 3;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    // InitialGrandProductFromCaches requires both inputs to be Cached addresses
    let addr_a = GKRAddress::Cached {
        layer: 0,
        offset: 0,
    };
    let addr_b = GKRAddress::Cached {
        layer: 0,
        offset: 1,
    };
    let addr_out = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };

    let a = random_poly_in_ext::<F, E>(POLY_SIZE);
    let b = random_poly_in_ext::<F, E>(POLY_SIZE);
    let output = compute_product::<F, E>(&a, &b);

    let mut storage = setup_storage::<F, E>(
        vec![(addr_a, a.clone()), (addr_b, b.clone())],
        vec![(addr_out, output)],
    );

    let kernel = InitialGrandProductFromCachesGKRRelation {
        inputs: [addr_a, addr_b],
        output: addr_out,
    };

    let (claim, prev_challenges, folding_challenges, expected_evals) = setup_sumcheck_params(
        &storage,
        &[addr_out],
        &[(addr_a, &a), (addr_b, &b)],
        FOLDING_STEPS,
    );

    run_sumcheck_test(
        &mut storage,
        &kernel,
        claim,
        &prev_challenges,
        &folding_challenges,
        &expected_evals,
    );
}

#[test]
fn test_unbalanced_grand_product() {
    const FOLDING_STEPS: usize = 3;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    // UnbalancedGrandProductWithCache requires exactly one Cached input
    let addr_cached = GKRAddress::Cached {
        layer: 0,
        offset: 0,
    };
    let addr_scalar = GKRAddress::BaseLayerMemory(0);
    let addr_out = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };

    let a = random_poly_in_ext::<F, E>(POLY_SIZE);
    let b = random_poly_in_ext::<F, E>(POLY_SIZE);
    let output = compute_product::<F, E>(&a, &b);

    let mut storage = setup_storage::<F, E>(
        vec![(addr_cached, a.clone()), (addr_scalar, b.clone())],
        vec![(addr_out, output)],
    );

    let kernel = UnbalancedGrandProductWithCacheGKRRelation {
        inputs: [addr_cached, addr_scalar],
        output: addr_out,
    };

    let (claim, prev_challenges, folding_challenges, expected_evals) = setup_sumcheck_params(
        &storage,
        &[addr_out],
        &[(addr_cached, &a), (addr_scalar, &b)],
        FOLDING_STEPS,
    );

    run_sumcheck_test(
        &mut storage,
        &kernel,
        claim,
        &prev_challenges,
        &folding_challenges,
        &expected_evals,
    );
}

#[test]
fn test_same_size_product() {
    const FOLDING_STEPS: usize = 3;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    // SameSizeProduct requires neither input to be Cached
    let addr_a = GKRAddress::BaseLayerMemory(0);
    let addr_b = GKRAddress::BaseLayerMemory(1);
    let addr_out = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };

    let a = random_poly_in_ext::<F, E>(POLY_SIZE);
    let b = random_poly_in_ext::<F, E>(POLY_SIZE);
    let output = compute_product::<F, E>(&a, &b);

    let mut storage = setup_storage::<F, E>(
        vec![(addr_a, a.clone()), (addr_b, b.clone())],
        vec![(addr_out, output)],
    );

    let kernel = SameSizeProductGKRRelation {
        inputs: [addr_a, addr_b],
        output: addr_out,
    };

    let (claim, prev_challenges, folding_challenges, expected_evals) = setup_sumcheck_params(
        &storage,
        &[addr_out],
        &[(addr_a, &a), (addr_b, &b)],
        FOLDING_STEPS,
    );

    run_sumcheck_test(
        &mut storage,
        &kernel,
        claim,
        &prev_challenges,
        &folding_challenges,
        &expected_evals,
    );
}

#[test]
fn test_lookup_with_cached_dens() {
    const FOLDING_STEPS: usize = 3;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    // LookupWithCachedDensAndSetup computes input/input - setup/setup = (a*d - c*b) / (b*d)
    // where input = [mask (a), denominator (b)], setup = [multiplicity (c), setup_denominator (d)]
    // Validation: input[0] (mask) NOT cached, input[1] (denominator) IS cached
    let addr_mask = GKRAddress::BaseLayerMemory(0); // input[0] - NOT cached
    let addr_den = GKRAddress::Cached {
        layer: 0,
        offset: 0,
    }; // input[1] - IS cached
    let addr_mult = GKRAddress::BaseLayerMemory(1); // setup[0] - multiplicity
    let addr_setup_den = GKRAddress::BaseLayerMemory(2); // setup[1] - setup denominator
    let addr_out_num = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };
    let addr_out_den = GKRAddress::InnerLayer {
        layer: 1,
        offset: 1,
    };

    let mask = random_poly_in_ext::<F, E>(POLY_SIZE);
    let den = random_poly_in_ext::<F, E>(POLY_SIZE);
    let mult = random_poly_in_ext::<F, E>(POLY_SIZE);
    let setup_den = random_poly_in_ext::<F, E>(POLY_SIZE);

    let (output_num, output_den) = compute_lookup_sub::<F, E>(&mask, &den, &mult, &setup_den);

    let mut storage = setup_storage::<F, E>(
        vec![
            (addr_mask, mask.clone()),
            (addr_den, den.clone()),
            (addr_mult, mult.clone()),
            (addr_setup_den, setup_den.clone()),
        ],
        vec![(addr_out_num, output_num), (addr_out_den, output_den)],
    );

    let kernel = LookupWithCachedDensAndSetupGKRRelation {
        input: [addr_mask, addr_den],
        setup: [addr_mult, addr_setup_den],
        output: [addr_out_num, addr_out_den],
    };

    let (claim, prev_challenges, folding_challenges, expected_evals) = setup_sumcheck_params(
        &storage,
        &[addr_out_num, addr_out_den],
        &[
            (addr_mask, &mask),
            (addr_den, &den),
            (addr_mult, &mult),
            (addr_setup_den, &setup_den),
        ],
        FOLDING_STEPS,
    );

    run_sumcheck_test(
        &mut storage,
        &kernel,
        claim,
        &prev_challenges,
        &folding_challenges,
        &expected_evals,
    );
}

#[test]
fn test_lookup_pair() {
    const FOLDING_STEPS: usize = 3;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    // a/b + c/d = (a*d + c*b) / (b*d)
    let a = random_poly_in_ext::<F, E>(POLY_SIZE);
    let b = random_poly_in_ext::<F, E>(POLY_SIZE);
    let c = random_poly_in_ext::<F, E>(POLY_SIZE);
    let d = random_poly_in_ext::<F, E>(POLY_SIZE);

    // Output: [a*d + c*b, b*d]
    let (output_num, output_den) = compute_lookup_add::<F, E>(&a, &b, &c, &d);

    let mut storage = setup_storage::<F, E>(
        vec![
            (GKRAddress::BaseLayerMemory(0), a.clone()),
            (GKRAddress::BaseLayerMemory(1), b.clone()),
            (GKRAddress::BaseLayerMemory(2), c.clone()),
            (GKRAddress::BaseLayerMemory(3), d.clone()),
        ],
        vec![
            (
                GKRAddress::InnerLayer {
                    layer: 1,
                    offset: 0,
                },
                output_num,
            ),
            (
                GKRAddress::InnerLayer {
                    layer: 1,
                    offset: 1,
                },
                output_den,
            ),
        ],
    );

    let kernel = LookupPairGKRRelation {
        inputs: [
            [
                GKRAddress::BaseLayerMemory(0),
                GKRAddress::BaseLayerMemory(1),
            ],
            [
                GKRAddress::BaseLayerMemory(2),
                GKRAddress::BaseLayerMemory(3),
            ],
        ],
        outputs: [
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 0,
            },
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 1,
            },
        ],
    };

    let (claim, prev_challenges, folding_challenges, expected_evals) = setup_sumcheck_params(
        &storage,
        &[
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 0,
            },
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 1,
            },
        ],
        &[
            (GKRAddress::BaseLayerMemory(0), &a),
            (GKRAddress::BaseLayerMemory(1), &b),
            (GKRAddress::BaseLayerMemory(2), &c),
            (GKRAddress::BaseLayerMemory(3), &d),
        ],
        FOLDING_STEPS,
    );

    run_sumcheck_test(
        &mut storage,
        &kernel,
        claim,
        &prev_challenges,
        &folding_challenges,
        &expected_evals,
    );
}

#[test]
fn test_copy() {
    const FOLDING_STEPS: usize = 3;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    let a = random_poly_in_ext::<F, E>(POLY_SIZE);

    // Copy: output = input (same polynomial)
    let output = a.clone();

    let mut storage = setup_storage::<F, E>(
        vec![(GKRAddress::BaseLayerMemory(0), a.clone())],
        vec![(
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 0,
            },
            output,
        )],
    );

    let kernel = CopyGKRRelation {
        input: GKRAddress::BaseLayerMemory(0),
        output: GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        },
    };

    let (claim, prev_challenges, folding_challenges, expected_evals) = setup_sumcheck_params(
        &storage,
        &[GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        }],
        &[(GKRAddress::BaseLayerMemory(0), &a)],
        FOLDING_STEPS,
    );

    run_sumcheck_test(
        &mut storage,
        &kernel,
        claim,
        &prev_challenges,
        &folding_challenges,
        &expected_evals,
    );
}

#[test]
fn test_mask_into_identity_product() {
    const FOLDING_STEPS: usize = 3;
    const POLY_SIZE: usize = 1 << FOLDING_STEPS;

    let input = random_poly_in_ext::<F, E>(POLY_SIZE);
    // Mask: alternating 0 and 1
    let mask: Vec<E> = (0..POLY_SIZE)
        .map(|el| E::from_base(F::from_u64_with_reduction((el % 2) as u64)))
        .collect();

    // Output: input * mask + (1 - mask)
    let output: Vec<E> = compute_mask_identity::<F, E>(&input, &mask);

    let mut storage = setup_storage::<F, E>(
        vec![
            (GKRAddress::BaseLayerMemory(0), input.clone()),
            (GKRAddress::BaseLayerMemory(1), mask.clone()),
        ],
        vec![(
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 0,
            },
            output,
        )],
    );

    let kernel = MaskIntoIdentityProductGKRRelation {
        input: GKRAddress::BaseLayerMemory(0),
        mask: GKRAddress::BaseLayerMemory(1),
        output: GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        },
    };

    let (claim, prev_challenges, folding_challenges, expected_evals) = setup_sumcheck_params(
        &storage,
        &[GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        }],
        &[
            (GKRAddress::BaseLayerMemory(0), &input),
            (GKRAddress::BaseLayerMemory(1), &mask),
        ],
        FOLDING_STEPS,
    );

    run_sumcheck_test(
        &mut storage,
        &kernel,
        claim,
        &prev_challenges,
        &folding_challenges,
        &expected_evals,
    );
}
