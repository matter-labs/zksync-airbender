use gpu_core::primitives::field::{BF, E4};

use super::reference::tensor_round_tail_reference;
use crate::upstream::{
    commit_field_els, draw_random_field_els, evaluate_eq_poly, evaluate_small_univariate_poly,
    output_univariate_monomial_form_max_quadratic, BabyBearField, Blake2sTranscript, Field,
    FieldExtension, PrimeField, Seed,
};

/// The one tensor cell that feeds only evaluations the round tail never reads:
/// `x0 = x1 = x2 = 1` reaches the output solely through the round-2 value at 1.
const CELL_FEEDING_ONLY_UNREAD_EVALUATIONS: usize = 13;

fn splitmix64(mut value: u64) -> u64 {
    value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

struct Rng(u64);

impl Rng {
    fn next_u32(&mut self) -> u32 {
        self.0 = splitmix64(self.0);
        (self.0 >> 32) as u32
    }

    fn next_e4(&mut self) -> E4 {
        E4::from_array_of_base(core::array::from_fn(|_| {
            BF::from_u32_with_reduction(self.next_u32())
        }))
    }
}

fn add(mut left: E4, right: E4) -> E4 {
    left.add_assign(&right);
    left
}

fn sub(mut left: E4, right: E4) -> E4 {
    left.sub_assign(&right);
    left
}

fn mul(mut left: E4, right: E4) -> E4 {
    left.mul_assign(&right);
    left
}

fn halve(mut value: E4) -> E4 {
    let half = BF::from_u32_with_reduction(2)
        .inverse()
        .expect("two is invertible");
    value.mul_assign_by_base(&half);
    value
}

fn eq(left: E4, right: E4) -> E4 {
    evaluate_eq_poly::<BabyBearField, E4>(&left, &right)
}

fn small_field_point(value: u32) -> E4 {
    <E4 as FieldExtension<BF>>::from_base(BF::from_u32_with_reduction(value))
}

/// Leading coefficient of the quadratic through samples at `0, 1, 2`.
fn leading_coefficient(samples: [E4; 3]) -> E4 {
    halve(add(
        sub(samples[2], add(samples[1], samples[1])),
        samples[0],
    ))
}

/// Lagrange evaluation of the quadratic through samples at `0, 1, 2`.
fn evaluate_quadratic(samples: [E4; 3], point: E4) -> E4 {
    let at_one = sub(point, small_field_point(1));
    let at_two = sub(point, small_field_point(2));
    let basis0 = halve(mul(at_one, at_two));
    let basis1 = mul(point, sub(small_field_point(2), point));
    let basis2 = halve(mul(point, at_one));
    add(
        add(mul(samples[0], basis0), mul(samples[1], basis1)),
        mul(samples[2], basis2),
    )
}

fn cell(x0: usize, x1: usize, x2: usize) -> usize {
    9 * x0 + 3 * x1 + x2
}

/// The three peeled axes of one surviving row, sampled on `{0, 1, 2}^3`.
struct RowSamples([E4; 27]);

impl RowSamples {
    fn evaluate(&self, point: [E4; 3]) -> E4 {
        let mut after_x2 = [E4::ZERO; 9];
        for x0 in 0..3 {
            for x1 in 0..3 {
                after_x2[3 * x0 + x1] = evaluate_quadratic(
                    core::array::from_fn(|x2| self.0[cell(x0, x1, x2)]),
                    point[2],
                );
            }
        }
        let after_x1: [E4; 3] = core::array::from_fn(|x0| {
            evaluate_quadratic(core::array::from_fn(|x1| after_x2[3 * x0 + x1]), point[1])
        });
        evaluate_quadratic(after_x1, point[0])
    }
}

struct Instance {
    rows: Vec<RowSamples>,
    high_point: Vec<E4>,
    rho: [E4; 3],
    seed: [u32; 8],
    eq_prefactor: E4,
}

impl Instance {
    fn new(index: usize) -> Self {
        let mut rng = Rng(splitmix64(0xa11c_e5ed ^ ((index as u64) << 17)));
        let high_bits = 1 + index % 3;
        let rows = (0..(1usize << high_bits))
            .map(|_| RowSamples(core::array::from_fn(|_| rng.next_e4())))
            .collect();
        Self {
            rows,
            high_point: (0..high_bits).map(|_| rng.next_e4()).collect(),
            rho: core::array::from_fn(|_| rng.next_e4()),
            seed: core::array::from_fn(|_| rng.next_u32()),
            eq_prefactor: rng.next_e4(),
        }
    }

    fn row_weight(&self, row: usize) -> E4 {
        self.high_point
            .iter()
            .enumerate()
            .fold(E4::ONE, |weight, (bit, coordinate)| {
                let factor = if row & (1 << bit) == 0 {
                    sub(E4::ONE, *coordinate)
                } else {
                    *coordinate
                };
                mul(weight, factor)
            })
    }

    /// The window executor's output before the `{0, 1, infinity}` transform:
    /// the equality-weighted sum of the surviving rows' `{0, 1, 2}^3` samples.
    fn finite_tensor(&self) -> [E4; 27] {
        let mut tensor = [E4::ZERO; 27];
        for (row, samples) in self.rows.iter().enumerate() {
            let weight = self.row_weight(row);
            for (slot, value) in tensor.iter_mut().zip(samples.0.iter()) {
                slot.add_assign(&mul(weight, *value));
            }
        }
        tensor
    }

    fn tensor(&self) -> [E4; 27] {
        let mut tensor = self.finite_tensor();
        for axis in 0..3 {
            for first in 0..3 {
                for second in 0..3 {
                    let index = |coordinate| match axis {
                        0 => cell(coordinate, first, second),
                        1 => cell(first, coordinate, second),
                        _ => cell(first, second, coordinate),
                    };
                    tensor[index(2)] =
                        leading_coefficient([tensor[index(0)], tensor[index(1)], tensor[index(2)]]);
                }
            }
        }
        tensor
    }

    /// Direct equality-weighted summation of the model over the surviving rows.
    fn evaluate(&self, point: [E4; 3]) -> E4 {
        self.rows
            .iter()
            .enumerate()
            .fold(E4::ZERO, |sum, (row, samples)| {
                add(sum, mul(self.row_weight(row), samples.evaluate(point)))
            })
    }

    /// The round polynomial's samples at `0, 1, 2` of the variable at
    /// `bound.len()`, with the earlier variables bound to `bound` and the later
    /// ones contracted against their previous claim-point coordinates.
    fn round_samples(&self, bound: &[E4]) -> [E4; 3] {
        let trailing = 3 - bound.len() - 1;
        core::array::from_fn(|sample| {
            let mut total = E4::ZERO;
            for mask in 0..(1usize << trailing) {
                let mut weight = E4::ONE;
                let mut point = [E4::ZERO; 3];
                point[..bound.len()].copy_from_slice(bound);
                point[bound.len()] = small_field_point(sample as u32);
                for trailing_index in 0..trailing {
                    let variable = bound.len() + 1 + trailing_index;
                    let bit = (mask >> trailing_index) & 1;
                    point[variable] = small_field_point(bit as u32);
                    weight = mul(
                        weight,
                        if bit == 0 {
                            sub(E4::ONE, self.rho[variable])
                        } else {
                            self.rho[variable]
                        },
                    );
                }
                total = add(total, mul(weight, self.evaluate(point)));
            }
            total
        })
    }

    /// The three rounds recomputed from direct summation and the production
    /// analytic-equality convention: coefficients, challenges, and the final
    /// `(seed, claim, eq_prefactor)`.
    fn direct_rounds(&self) -> ([E4; 12], [E4; 3], [u32; 8], E4, E4, E4) {
        let mut seed = Seed(self.seed);
        let mut coeffs = [E4::ZERO; 12];
        let mut challenges = [E4::ZERO; 3];
        let mut claim = E4::ZERO;
        let mut eq_prefactor = self.eq_prefactor;
        let mut initial_claim = E4::ZERO;
        let mut bound: Vec<E4> = Vec::new();

        for round in 0..3 {
            let samples = self.round_samples(&bound);
            let normalized_claim = add(
                mul(sub(E4::ONE, self.rho[round]), samples[0]),
                mul(self.rho[round], samples[1]),
            );
            if round == 0 {
                initial_claim = mul(eq_prefactor, normalized_claim);
            } else {
                assert_eq!(
                    mul(claim, eq_prefactor.inverse().expect("non-zero")),
                    normalized_claim,
                    "round {round} claim identity"
                );
            }

            let round_coeffs = output_univariate_monomial_form_max_quadratic::<BabyBearField, E4>(
                self.rho[round],
                normalized_claim,
                samples[0],
                leading_coefficient(samples),
            );
            commit_field_els::<BabyBearField, E4, Blake2sTranscript>(&mut seed, &round_coeffs);
            let challenge =
                draw_random_field_els::<BabyBearField, E4, Blake2sTranscript>(&mut seed, 1)[0];

            coeffs[4 * round..4 * round + 4].copy_from_slice(&round_coeffs);
            challenges[round] = challenge;
            claim =
                evaluate_small_univariate_poly::<BabyBearField, E4, 4>(&round_coeffs, &challenge);
            eq_prefactor = eq(challenge, self.rho[round]);
            bound.push(challenge);
        }

        (
            coeffs,
            challenges,
            seed.0,
            claim,
            eq_prefactor,
            initial_claim,
        )
    }
}

type ReferenceOutput = ([E4; 12], [E4; 3], [u32; 8], E4, E4);

fn run_reference(instance: &Instance, tensor: [E4; 27], initial_claim: E4) -> ReferenceOutput {
    let mut seed = instance.seed;
    let mut claim = initial_claim;
    let mut eq_prefactor = instance.eq_prefactor;
    let (coeffs, challenges) = tensor_round_tail_reference(
        tensor,
        &instance.rho,
        &mut seed,
        &mut claim,
        &mut eq_prefactor,
    );
    (coeffs, challenges, seed, claim, eq_prefactor)
}

#[test]
fn cpu_window_tail_reference_matches_direct_summation() {
    for index in 0..36 {
        let instance = Instance::new(index);
        let (coeffs, challenges, seed, claim, eq_prefactor, initial_claim) =
            instance.direct_rounds();
        let tensor = instance.tensor();
        let reference = run_reference(&instance, tensor, initial_claim);

        assert_eq!(reference.0, coeffs, "instance {index} coefficients");
        assert_eq!(reference.1, challenges, "instance {index} challenges");
        assert_eq!(reference.2, seed, "instance {index} seed");
        assert_eq!(reference.3, claim, "instance {index} claim");
        assert_eq!(reference.4, eq_prefactor, "instance {index} eq prefactor");

        let transposed: [E4; 27] =
            core::array::from_fn(|slot| tensor[cell(slot / 9, slot % 3, (slot / 3) % 3)]);
        assert_ne!(
            run_reference(&instance, transposed, initial_claim),
            reference,
            "instance {index} survives transposing the two contracted axes"
        );

        let inert: Vec<usize> = (0..27)
            .filter(|slot| {
                let mut perturbed = tensor;
                perturbed[*slot].add_assign(&E4::ONE);
                run_reference(&instance, perturbed, initial_claim) == reference
            })
            .collect();
        assert_eq!(
            inert,
            vec![CELL_FEEDING_ONLY_UNREAD_EVALUATIONS],
            "instance {index} tensor cell sensitivity"
        );
    }
}
