use gpu_core::primitives::field::{BF, E4};

use super::reference::tensor_round_tail_reference;
use super::tail::WindowTailArm;
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

/// Row-tile counts the GPU arms are driven over: the `row_tiles == 1`
/// boundary, both sides of the absorbed arm's 32 tile slots, both sides of the
/// split arm's 256-thread stride, and production-scale counts.
#[cfg(not(no_cuda))]
const WINDOW_TAIL_ROW_TILES: [usize; 12] = [1, 2, 3, 7, 31, 32, 33, 64, 100, 256, 257, 1000];

#[cfg(not(no_cuda))]
const WINDOW_TAIL_CASES: usize = 36;

#[cfg(not(no_cuda))]
fn drive_window_tail_arm(arm: WindowTailArm) {
    use era_cudart::memory::memory_copy_async;
    use gpu_core::allocator::tracker::AllocationPlacement;
    use gpu_core::primitives::context::DeviceAllocation;

    use super::tail::{launch_window_tensor_round_tail, WindowTailState, WINDOW_TAIL_TENSOR_CELLS};
    use crate::backward::kernels::GKR_EQ_GROUP_TABLE_LEN;
    use crate::test_utils::make_test_context;

    let context = make_test_context(256, 64);
    let stream = context.get_exec_stream();
    let max_row_tiles = *WINDOW_TAIL_ROW_TILES.iter().max().expect("non-empty");

    let mut d_partials: DeviceAllocation<E4> = context
        .alloc(
            WINDOW_TAIL_TENSOR_CELLS * max_row_tiles,
            AllocationPlacement::Top,
        )
        .unwrap();
    let mut d_tensor: DeviceAllocation<E4> = context
        .alloc(WINDOW_TAIL_TENSOR_CELLS, AllocationPlacement::Top)
        .unwrap();
    let mut d_claim_point: DeviceAllocation<E4> =
        context.alloc(3, AllocationPlacement::Top).unwrap();
    let mut d_challenges: DeviceAllocation<E4> =
        context.alloc(3, AllocationPlacement::Top).unwrap();
    let mut d_seed: DeviceAllocation<u32> = context.alloc(8, AllocationPlacement::Top).unwrap();
    let mut d_claim: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
    let mut d_eq_prefactor: DeviceAllocation<E4> =
        context.alloc(1, AllocationPlacement::Top).unwrap();
    let mut d_coeffs: DeviceAllocation<E4> = context.alloc(12, AllocationPlacement::Top).unwrap();
    let mut d_eq: DeviceAllocation<E4> = context
        .alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)
        .unwrap();

    for case in 0..WINDOW_TAIL_CASES {
        let row_tiles = WINDOW_TAIL_ROW_TILES[case % WINDOW_TAIL_ROW_TILES.len()];
        let partials_len = WINDOW_TAIL_TENSOR_CELLS * row_tiles;
        let mut rng = Rng(splitmix64(0x7a11_c0de ^ ((case as u64) << 23)));
        let partials: Vec<E4> = (0..partials_len).map(|_| rng.next_e4()).collect();
        let mut tensor = [E4::ZERO; 27];
        for (index, value) in partials.iter().enumerate() {
            tensor[index % WINDOW_TAIL_TENSOR_CELLS].add_assign(value);
        }
        let rho: [E4; 3] = core::array::from_fn(|_| rng.next_e4());
        let seed: [u32; 8] = core::array::from_fn(|_| rng.next_u32());
        let claim = rng.next_e4();
        let eq_prefactor = rng.next_e4();
        let eq_size_before_fold = 1 + (case % 8) as u32;
        let eq_before: Vec<E4> = (0..GKR_EQ_GROUP_TABLE_LEN).map(|_| rng.next_e4()).collect();
        // Production points the output claim-point view at the same symbol the
        // input view reads, so half the cases overwrite the coordinates the
        // tail still needs.
        let aliased_claim_point = case % 2 == 1;
        let label = format!("{arm:?} case {case} (row_tiles {row_tiles})");

        memory_copy_async(&mut d_partials[..partials_len], &partials, stream).unwrap();
        memory_copy_async(&mut d_claim_point[..], &rho, stream).unwrap();
        memory_copy_async(&mut d_seed[..], &seed, stream).unwrap();
        memory_copy_async(&mut d_claim[..], &[claim], stream).unwrap();
        memory_copy_async(&mut d_eq_prefactor[..], &[eq_prefactor], stream).unwrap();
        memory_copy_async(&mut d_eq[..], &eq_before, stream).unwrap();

        let claim_point_ptr = d_claim_point.as_mut_ptr();
        let state = WindowTailState {
            partials: d_partials.as_ptr(),
            row_tiles,
            reduced_tensor: d_tensor.as_mut_ptr(),
            prev_claim_coords: claim_point_ptr,
            seed: d_seed.as_mut_ptr(),
            claim: d_claim.as_mut_ptr(),
            eq_prefactor: d_eq_prefactor.as_mut_ptr(),
            coeffs_out: d_coeffs.as_mut_ptr(),
            challenges_out: if aliased_claim_point {
                claim_point_ptr
            } else {
                d_challenges.as_mut_ptr()
            },
            active_eq_slot_base: d_eq.as_mut_ptr(),
            active_eq_size_before_fold: eq_size_before_fold,
        };
        launch_window_tensor_round_tail(arm, &state, &context).unwrap();

        let mut gpu_coeffs = [E4::ZERO; 12];
        let mut gpu_challenges = [E4::ZERO; 3];
        let mut gpu_seed = [0u32; 8];
        let mut gpu_claim = [E4::ZERO; 1];
        let mut gpu_eq_prefactor = [E4::ZERO; 1];
        let mut gpu_tensor = [E4::ZERO; 27];
        let mut gpu_eq = vec![E4::ZERO; GKR_EQ_GROUP_TABLE_LEN];
        memory_copy_async(&mut gpu_coeffs[..], &d_coeffs[..], stream).unwrap();
        if aliased_claim_point {
            memory_copy_async(&mut gpu_challenges[..], &d_claim_point[..], stream).unwrap();
        } else {
            memory_copy_async(&mut gpu_challenges[..], &d_challenges[..], stream).unwrap();
        }
        memory_copy_async(&mut gpu_seed[..], &d_seed[..], stream).unwrap();
        memory_copy_async(&mut gpu_claim[..], &d_claim[..], stream).unwrap();
        memory_copy_async(&mut gpu_eq_prefactor[..], &d_eq_prefactor[..], stream).unwrap();
        memory_copy_async(&mut gpu_tensor[..], &d_tensor[..], stream).unwrap();
        memory_copy_async(&mut gpu_eq[..], &d_eq[..], stream).unwrap();
        stream.synchronize().unwrap();

        let mut expected_seed = seed;
        let mut expected_claim = claim;
        let mut expected_eq_prefactor = eq_prefactor;
        let (expected_coeffs, expected_challenges) = tensor_round_tail_reference(
            tensor,
            &rho,
            &mut expected_seed,
            &mut expected_claim,
            &mut expected_eq_prefactor,
        );

        assert_eq!(gpu_coeffs, expected_coeffs, "{label} coefficients");
        assert_eq!(gpu_challenges, expected_challenges, "{label} challenges");
        assert_eq!(gpu_seed, expected_seed, "{label} seed");
        assert_eq!(gpu_claim[0], expected_claim, "{label} claim");
        assert_eq!(
            gpu_eq_prefactor[0], expected_eq_prefactor,
            "{label} eq prefactor"
        );
        if arm == WindowTailArm::Split {
            assert_eq!(gpu_tensor, tensor, "{label} reduced tensor");
        }

        let folded_len = 1usize << (eq_size_before_fold - 1);
        let expected_eq: Vec<E4> = (0..GKR_EQ_GROUP_TABLE_LEN)
            .map(|index| {
                if index < folded_len {
                    add(eq_before[2 * index], eq_before[2 * index + 1])
                } else {
                    eq_before[index]
                }
            })
            .collect();
        assert_eq!(gpu_eq, expected_eq, "{label} folded eq slot");
    }
}

#[test]
#[cfg(not(no_cuda))]
fn window_tail_gpu_absorbed_arm_matches_reference() {
    drive_window_tail_arm(WindowTailArm::Absorbed);
}

#[test]
#[cfg(not(no_cuda))]
fn window_tail_gpu_split_arm_matches_reference() {
    drive_window_tail_arm(WindowTailArm::Split);
}
