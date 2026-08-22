use field::{Field, FieldExtension, PrimeField};

use gpu_gkr::backward::window::reference::tensor_round_tail_reference;

use crate::abi::{BF, E4};
use crate::r0_input::{direct_eq_weight, FrozenE4};
use crate::r0_reference::{assert_degree_two_at_three, quadratic_tensor_transform, tensor_index};

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

fn divide(value: E4, divisor: E4) -> E4 {
    mul(value, divisor.inverse().expect("non-zero divisor"))
}

fn halve(mut value: E4) -> E4 {
    let half = BF::from_u32_with_reduction(2)
        .inverse()
        .expect("two is invertible");
    value.mul_assign_by_base(&half);
    value
}

fn small_field_point(value: u32) -> E4 {
    <E4 as FieldExtension<BF>>::from_base(BF::from_u32_with_reduction(value))
}

fn eq_factor(bit: usize, coordinate: E4) -> E4 {
    if bit == 0 {
        sub(E4::ONE, coordinate)
    } else {
        coordinate
    }
}

fn leading_coefficient(samples: [E4; 3]) -> E4 {
    halve(add(
        sub(samples[2], add(samples[1], samples[1])),
        samples[0],
    ))
}

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

fn horner(coeffs: &[E4], point: E4) -> E4 {
    coeffs.iter().rev().fold(E4::ZERO, |value, coefficient| {
        add(mul(value, point), *coefficient)
    })
}

fn eq_poly(left: E4, right: E4) -> E4 {
    add(
        mul(left, right),
        mul(sub(E4::ONE, left), sub(E4::ONE, right)),
    )
}

fn extend_axis(samples: [E4; 3]) -> E4 {
    let mut extended = add(samples[2], add(samples[2], samples[2]));
    extended = sub(extended, add(samples[1], add(samples[1], samples[1])));
    add(extended, samples[0])
}

struct Instance {
    rows: Vec<[E4; 27]>,
    equality_point: Vec<FrozenE4>,
    rho: [E4; 3],
    seed: [u32; 8],
    eq_prefactor: E4,
}

impl Instance {
    fn new(index: usize) -> Self {
        let mut rng = Rng(splitmix64(0x0c17_a55e ^ ((index as u64) << 19)));
        let high_bits = 1 + index % 3;
        let rows = (0..(1usize << high_bits))
            .map(|_| core::array::from_fn(|_| rng.next_e4()))
            .collect();
        let equality_point = (0..high_bits)
            .map(|_| FrozenE4::from_e4(rng.next_e4()))
            .collect();
        Self {
            rows,
            equality_point,
            rho: core::array::from_fn(|_| rng.next_e4()),
            seed: core::array::from_fn(|_| rng.next_u32()),
            eq_prefactor: rng.next_e4(),
        }
    }

    /// Equality-weighted sum of the surviving rows' `{0, 1, 2}^3` samples, in
    /// the `r0_reference` cell order.
    fn finite_cells(&self) -> [E4; 27] {
        let mut cells = [E4::ZERO; 27];
        for (row, samples) in self.rows.iter().enumerate() {
            let weight = direct_eq_weight(row, &self.equality_point);
            for (slot, value) in cells.iter_mut().zip(samples.iter()) {
                slot.add_assign(&mul(weight, *value));
            }
        }
        cells
    }

    /// The `{0, 1, infinity}^3` tensor, built through the bench's own degree
    /// check and quadratic transform.
    fn tensor(&self) -> [E4; 27] {
        let cells = self.finite_cells();
        let mut grid = [E4::ZERO; 64];
        for x0 in 0..3 {
            for x1 in 0..3 {
                for x2 in 0..3 {
                    grid[16 * x0 + 4 * x1 + x2] = cells[tensor_index(x0, x1, x2)];
                }
            }
        }
        for x0 in 0..3 {
            for x1 in 0..3 {
                grid[16 * x0 + 4 * x1 + 3] =
                    extend_axis(core::array::from_fn(|x2| grid[16 * x0 + 4 * x1 + x2]));
            }
        }
        for x0 in 0..3 {
            for x2 in 0..4 {
                grid[16 * x0 + 12 + x2] =
                    extend_axis(core::array::from_fn(|x1| grid[16 * x0 + 4 * x1 + x2]));
            }
        }
        for x1 in 0..4 {
            for x2 in 0..4 {
                grid[48 + 4 * x1 + x2] =
                    extend_axis(core::array::from_fn(|x0| grid[16 * x0 + 4 * x1 + x2]));
            }
        }
        assert_degree_two_at_three(&grid).expect("model is quadratic per peeled axis");
        quadratic_tensor_transform(cells).expect("canonical transform")
    }

    fn evaluate(&self, point: [E4; 3]) -> E4 {
        let cells = self.finite_cells();
        let after_x2: [E4; 9] = core::array::from_fn(|index| {
            let (x0, x1) = (index / 3, index % 3);
            evaluate_quadratic(
                core::array::from_fn(|x2| cells[tensor_index(x0, x1, x2)]),
                point[2],
            )
        });
        let after_x1: [E4; 3] = core::array::from_fn(|x0| {
            evaluate_quadratic(core::array::from_fn(|x1| after_x2[3 * x0 + x1]), point[1])
        });
        evaluate_quadratic(after_x1, point[0])
    }

    /// Samples at `0, 1, 2` of the round polynomial for the variable at
    /// `bound.len()`: earlier variables bound to `bound`, later ones contracted
    /// against their previous claim-point coordinates.
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
                    weight = mul(weight, eq_factor(bit, self.rho[variable]));
                }
                total = add(total, mul(weight, self.evaluate(point)));
            }
            total
        })
    }
}

#[test]
fn cpu_window_tail_cross_matches_bench_round_evaluation() {
    for index in 0..12 {
        let instance = Instance::new(index);

        let initial_samples = instance.round_samples(&[]);
        let initial_normalized_claim = add(
            mul(eq_factor(0, instance.rho[0]), initial_samples[0]),
            mul(eq_factor(1, instance.rho[0]), initial_samples[1]),
        );
        let mut claim = mul(instance.eq_prefactor, initial_normalized_claim);
        let mut eq_prefactor = instance.eq_prefactor;
        let mut seed = instance.seed;

        let (coeffs, challenges) = tensor_round_tail_reference(
            instance.tensor(),
            &instance.rho,
            &mut seed,
            &mut claim,
            &mut eq_prefactor,
        );

        let mut expected_claim = mul(instance.eq_prefactor, initial_normalized_claim);
        let mut expected_prefactor = instance.eq_prefactor;
        let mut bound: Vec<E4> = Vec::new();

        for round in 0..3 {
            let samples = instance.round_samples(&bound);
            let round_coeffs = &coeffs[4 * round..4 * round + 4];
            let coordinate = instance.rho[round];

            let normalized_claim = add(
                mul(eq_factor(0, coordinate), samples[0]),
                mul(eq_factor(1, coordinate), samples[1]),
            );
            assert_eq!(
                divide(expected_claim, expected_prefactor),
                normalized_claim,
                "instance {index} round {round} claim identity"
            );

            let linear_constant = sub(E4::ONE, coordinate);
            let linear_leading = sub(add(coordinate, coordinate), E4::ONE);
            assert_eq!(
                divide(round_coeffs[0], linear_constant),
                samples[0],
                "instance {index} round {round} evaluation at zero"
            );
            assert_eq!(
                divide(round_coeffs[3], linear_leading),
                leading_coefficient(samples),
                "instance {index} round {round} leading coefficient"
            );

            expected_claim = horner(round_coeffs, challenges[round]);
            expected_prefactor = eq_poly(challenges[round], coordinate);
            bound.push(challenges[round]);
        }

        assert_eq!(claim, expected_claim, "instance {index} final claim");
        assert_eq!(
            eq_prefactor, expected_prefactor,
            "instance {index} final eq prefactor"
        );
    }
}
