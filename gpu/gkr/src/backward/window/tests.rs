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

/// GPU-free probes of the launch ABI, the runtime binding, and dispatch.
mod cpu_window_binding {
    use core::mem::{align_of, offset_of, size_of};

    use gpu_gkr_compiler::{
        resolve_windowed_r0_dispatch, windowed_r0_bank, windowed_r0_kernel_symbol,
        WindowCapacities, WindowProgram, WindowShape, WindowSourceLane, DESCRIPTOR_ALIGNMENT_BYTES,
        KERNEL_ARGUMENT_CEILING_BYTES, SOURCE_WINDOW_COLUMNS, WINDOWED_R0_KERNEL_COUNT,
        WINDOW_SHAPE_DEFINED_BITS,
    };

    use crate::backward::kernels::{make_eq_sizes, max_partials_len, record_active_eq_slot_fold};
    use crate::backward::vm::production_bind::drained_eq_sizes;
    use crate::backward::vm::seg_desc::{BwdSegAddrSlot, BWD_COEFF_PROCEDURAL_NONE};
    use crate::backward::window::binding::{
        build_window_binding, resolve_window_kernel, window_chunk_address, window_log_rows,
        window_partials_len, window_row_tiles, WindowAddressing, WindowBindError,
        WindowLaunchBinding, WindowRuntimeScratch, BWD_WINDOW_ADDR_SLOTS, BWD_WINDOW_COORDINATES,
        BWD_WINDOW_MAX_FOLDING_STEPS, BWD_WINDOW_MAX_IMMEDIATES, BWD_WINDOW_PROGRAM_WORD_CAP,
        BWD_WINDOW_ROWS_PER_TILE,
    };
    use crate::backward::window::generated_registry::{
        WINDOWED_R0_BLOCK_THREADS, WINDOWED_R0_DISPATCH, WINDOWED_R0_FALLBACK_MASK,
        WINDOWED_R0_KERNELS,
    };
    use crate::backward::window::tail::WINDOW_TAIL_TENSOR_CELLS;
    use gpu_core::primitives::field::E4;

    const EQ_LOW: *const E4 = 0x1_0000 as *const E4;
    const PARTIALS: *mut E4 = 0x2_0000 as *mut E4;

    fn scratch(capacity: usize) -> WindowRuntimeScratch {
        WindowRuntimeScratch {
            eq_low: EQ_LOW,
            partials: PARTIALS,
            partials_capacity: capacity,
        }
    }

    fn program(words: Vec<u16>, immediates: Vec<u32>) -> WindowProgram {
        let mut sections = [0u32; 16];
        for (index, endpoint) in [4u32, 8, 12, 16].into_iter().enumerate() {
            sections[index] = endpoint;
        }
        sections[4] = u32::from(WindowShape::BF_PROCEDURAL.bits());
        WindowProgram {
            layer: 3,
            words,
            source_slots: vec![0, 129],
            source_lanes: Vec::new(),
            windows: Vec::new(),
            immediates,
            sections,
            coefficient_plans: Vec::new(),
            shape: WindowShape::BF_PROCEDURAL,
            capacities: WindowCapacities::default(),
        }
    }

    /// A hand-built runtime addressing: the binder normally interns these from
    /// storage pointers, which needs a live layer.
    fn addressing(slots: &[BwdSegAddrSlot], lanes: &[Option<u16>]) -> WindowAddressing {
        WindowAddressing {
            slots: slots.to_vec(),
            lanes: lanes.to_vec(),
        }
    }

    /// The rejection a binder call produced; neither the descriptor nor a kernel
    /// entry is `Debug`, so `unwrap_err` is not available.
    fn rejection<T>(result: Result<T, WindowBindError>) -> WindowBindError {
        result.err().expect("the binder must reject this input")
    }

    fn slot(base: usize, log2_stride: u8) -> BwdSegAddrSlot {
        BwdSegAddrSlot {
            base: base as *const u8,
            log2_stride,
            origin: 0,
            procedural_kind: BWD_COEFF_PROCEDURAL_NONE,
            reserved: [0; 5],
        }
    }

    #[test]
    fn descriptor_layout_matches_the_wire() {
        assert_eq!(size_of::<WindowLaunchBinding>(), 17_248);
        assert_eq!(
            align_of::<WindowLaunchBinding>(),
            DESCRIPTOR_ALIGNMENT_BYTES
        );
        assert!(size_of::<WindowLaunchBinding>() <= KERNEL_ARGUMENT_CEILING_BYTES);
        assert_eq!(KERNEL_ARGUMENT_CEILING_BYTES, 32_764);
        assert_eq!(offset_of!(WindowLaunchBinding, slot), 0);
        assert_eq!(offset_of!(WindowLaunchBinding, eq_low), 1_024);
        assert_eq!(offset_of!(WindowLaunchBinding, partials), 1_032);
        assert_eq!(offset_of!(WindowLaunchBinding, log_rows), 1_040);
        assert_eq!(offset_of!(WindowLaunchBinding, eq_sizes), 1_044);
        assert_eq!(offset_of!(WindowLaunchBinding, sections), 1_056);
        assert_eq!(offset_of!(WindowLaunchBinding, program), 1_120);
        assert_eq!(offset_of!(WindowLaunchBinding, immediates), 15_200);
        assert_eq!(BWD_WINDOW_ADDR_SLOTS, 64);
        assert_eq!(BWD_WINDOW_PROGRAM_WORD_CAP, 7_040);
        assert_eq!(BWD_WINDOW_MAX_IMMEDIATES, 512);
    }

    #[test]
    fn binding_carries_the_program_the_scratch_and_the_row_shape() {
        let words = vec![6u16, 0x8001, 3, 0x0080, 0, 1, 2, 3];
        let immediates = vec![7u32, 11, 13];
        let program = program(words.clone(), immediates.clone());
        let slots = [slot(0x10_0000, 21), slot(0x20_0000, 19)];
        let binding = build_window_binding(
            &program,
            &addressing(&slots, &[]),
            24,
            scratch(window_partials_len(1 << 24)),
        )
        .expect("the synthetic program fits every capacity");

        assert_eq!(binding.eq_low, EQ_LOW);
        assert_eq!(binding.partials, PARTIALS);
        assert_eq!(binding.log_rows, 21);
        // The window peels three coordinates per launch, so its eq schedule is
        // two groups shorter than round 0's per-round schedule.
        assert_eq!(binding.eq_sizes.high, [8, 8]);
        assert_eq!(binding.eq_sizes.low, 5);
        assert_eq!(binding.sections, program.sections);
        assert_eq!(&binding.program[..words.len()], words.as_slice());
        assert!(binding.program[words.len()..].iter().all(|word| *word == 0));
        assert_eq!(
            &binding.immediates[..immediates.len()],
            immediates.as_slice()
        );
        assert!(binding.immediates[immediates.len()..]
            .iter()
            .all(|immediate| *immediate == 0));
        for (index, expected) in slots.iter().enumerate() {
            assert_eq!(binding.slot[index].base, expected.base, "slot {index} base");
            assert_eq!(
                binding.slot[index].log2_stride, expected.log2_stride,
                "slot {index} stride"
            );
        }
        assert!(binding.slot[slots.len()..]
            .iter()
            .all(|slot| slot.base.is_null()));
    }

    #[test]
    fn binding_eq_schedule_tracks_the_smallest_trace() {
        let binding = build_window_binding(
            &program(Vec::new(), Vec::new()),
            &addressing(&[], &[]),
            4,
            scratch(1 << 10),
        )
        .expect("a log-4 trace is one row tile");
        assert_eq!(binding.log_rows, 1);
        assert_eq!(binding.eq_sizes.high, [0, 0]);
        assert_eq!(binding.eq_sizes.low, 1);
        assert_eq!(window_log_rows(4), 1);
    }

    /// The handoff the windowed arm depends on: the window kernel reads the
    /// freshly built schedule, the tail applies exactly ONE physical fold, and
    /// round 3's continuation descriptor is lowered against that same one-fold
    /// drain. A tail that folded once per consumed round would break this.
    #[test]
    fn binding_eq_schedule_hands_the_round3_drain_its_own_state() {
        for folding_steps in [4usize, 6, 20, 22, 23, 24] {
            let binding = build_window_binding(
                &program(Vec::new(), Vec::new()),
                &addressing(&[], &[]),
                folding_steps,
                scratch(window_partials_len(1usize << folding_steps)),
            )
            .expect("the corpus folding steps are all bindable");
            let built = make_eq_sizes(folding_steps - BWD_WINDOW_COORDINATES);
            assert_eq!(binding.eq_sizes, built);
            let mut after_tail = built;
            record_active_eq_slot_fold(&mut after_tail);
            assert_eq!(
                after_tail,
                drained_eq_sizes(built, 1),
                "folding_steps {folding_steps}"
            );
            // What `build_bwd_vm_ext_rounds(start_round = 3, base = built)`
            // lowers round 3 against.
            assert_eq!(after_tail, drained_eq_sizes(built, 3 - 3 + 1));
        }
    }

    /// Production storage allocates a layer's columns per storage class, so two
    /// columns of one artifact window can sit in different matrices — and even a
    /// contiguous pair addresses off its chunk base, not off the window's first
    /// column. This is the add_sub layer-3 case that the wire's lowered lanes
    /// cannot express: columns 4 and 5 of matrix A, column 6 of matrix B, where
    /// B is A + 6 strides.
    #[test]
    fn binding_chunk_addressing_splits_a_window_across_matrices() {
        const STRIDE: usize = 1 << 28;
        let matrix_a = 0x1000_0000_0000usize;
        let matrix_b = matrix_a + 6 * STRIDE;
        assert_eq!(
            window_chunk_address(matrix_a, matrix_a + 4 * STRIDE, STRIDE),
            (matrix_a, 4)
        );
        assert_eq!(
            window_chunk_address(matrix_a, matrix_a + 5 * STRIDE, STRIDE),
            (matrix_a, 5)
        );
        assert_eq!(
            window_chunk_address(matrix_b, matrix_b + 6 * STRIDE, STRIDE),
            (matrix_b, 6)
        );
        // Past the first chunk the slot bases at the chunk, not at the matrix.
        let columns = SOURCE_WINDOW_COLUMNS;
        assert_eq!(
            window_chunk_address(matrix_a, matrix_a + (columns + 3) * STRIDE, STRIDE),
            (matrix_a + columns * STRIDE, 3)
        );
    }

    /// The binder rewrites exactly the words the side table names, to the lanes
    /// storage implies, and leaves every other word alone.
    #[test]
    fn binding_rewrites_lowered_lanes_to_storage_lanes() {
        let words = vec![
            2u16, 0, 0x0000, 0x0001, // BF product of window 0 columns 0 and 1
            6, 0x8001, 1, 0x0080, // group header: arity and product prefix
            2, 0, 0x0002, 0x0080, // member reading window 0 column 2 and window 1 column 0
        ];
        let mut program = program(words.clone(), Vec::new());
        program.source_slots = vec![0x0000, 0x0001, 0x0002, 0x0080];
        program.source_lanes = vec![
            WindowSourceLane { word: 2, source: 0 },
            WindowSourceLane { word: 3, source: 1 },
            WindowSourceLane {
                word: 10,
                source: 2,
            },
            WindowSourceLane {
                word: 11,
                source: 3,
            },
        ];
        let lanes = [Some(0x0104), Some(0x0105), Some(0x0206), Some(0x0300)];
        let binding = build_window_binding(
            &program,
            &addressing(&[slot(0x10_0000, 21); 4], &lanes),
            24,
            scratch(window_partials_len(1 << 24)),
        )
        .expect("the synthetic program fits every capacity");

        assert_eq!(
            &binding.program[..words.len()],
            &[2, 0, 0x0104, 0x0105, 6, 0x8001, 1, 0x0080, 2, 0, 0x0206, 0x0300]
        );
        assert!(binding.program[words.len()..].iter().all(|word| *word == 0));

        // A lane word whose source never resolved is a rejection, not a silent
        // stale address.
        assert_eq!(
            rejection(build_window_binding(
                &program,
                &addressing(
                    &[slot(0x10_0000, 21); 4],
                    &[Some(0x0104), None, Some(0x0206), Some(0x0300)]
                ),
                24,
                scratch(window_partials_len(1 << 24))
            )),
            WindowBindError::LaneSourceMissing { word: 3, source: 1 }
        );
    }

    #[test]
    fn binding_rejects_what_the_descriptor_cannot_hold() {
        let empty = program(Vec::new(), Vec::new());
        assert_eq!(
            rejection(build_window_binding(
                &empty,
                &addressing(&[], &[]),
                3,
                scratch(1 << 20)
            )),
            WindowBindError::UnsupportedFoldingSteps { folding_steps: 3 }
        );
        assert_eq!(
            rejection(build_window_binding(
                &empty,
                &addressing(&[], &[]),
                BWD_WINDOW_MAX_FOLDING_STEPS + 1,
                scratch(1 << 20)
            )),
            WindowBindError::UnsupportedFoldingSteps {
                folding_steps: BWD_WINDOW_MAX_FOLDING_STEPS + 1
            }
        );
        assert_eq!(
            rejection(build_window_binding(
                &empty,
                &addressing(&vec![slot(0x1000, 4); BWD_WINDOW_ADDR_SLOTS + 1], &[]),
                12,
                scratch(1 << 20)
            )),
            WindowBindError::Capacity {
                resource: "window address slots",
                required: BWD_WINDOW_ADDR_SLOTS + 1,
                capacity: BWD_WINDOW_ADDR_SLOTS,
            }
        );
        assert_eq!(
            rejection(build_window_binding(
                &program(vec![0; BWD_WINDOW_PROGRAM_WORD_CAP + 1], Vec::new()),
                &addressing(&[], &[]),
                12,
                scratch(1 << 20)
            )),
            WindowBindError::Capacity {
                resource: "window program words",
                required: BWD_WINDOW_PROGRAM_WORD_CAP + 1,
                capacity: BWD_WINDOW_PROGRAM_WORD_CAP,
            }
        );
        assert_eq!(
            rejection(build_window_binding(
                &program(Vec::new(), vec![0; BWD_WINDOW_MAX_IMMEDIATES + 1]),
                &addressing(&[], &[]),
                12,
                scratch(1 << 20)
            )),
            WindowBindError::Capacity {
                resource: "window immediates",
                required: BWD_WINDOW_MAX_IMMEDIATES + 1,
                capacity: BWD_WINDOW_MAX_IMMEDIATES,
            }
        );
        let required = window_partials_len(1 << 20);
        assert_eq!(
            rejection(build_window_binding(
                &empty,
                &addressing(&[], &[]),
                20,
                scratch(required - 1)
            )),
            WindowBindError::Capacity {
                resource: "window partials",
                required,
                capacity: required - 1,
            }
        );
        assert!(build_window_binding(&empty, &addressing(&[], &[]), 20, scratch(required)).is_ok());
    }

    #[test]
    fn scratch_geometry_covers_both_partial_layouts() {
        assert_eq!(WINDOW_TAIL_TENSOR_CELLS, 27);
        assert_eq!(BWD_WINDOW_ROWS_PER_TILE, 32);
        // A log-4 trace has two window rows, so one tile; the reserved tensor is
        // the second 27-cell group.
        assert_eq!(window_row_tiles(1 << 4), 1);
        assert_eq!(window_partials_len(1 << 4), 54);
        for log_trace in 4..=BWD_WINDOW_MAX_FOLDING_STEPS {
            let trace_len = 1usize << log_trace;
            let rows = trace_len >> BWD_WINDOW_COORDINATES;
            let tiles = window_row_tiles(trace_len);
            assert_eq!(tiles, rows.div_ceil(BWD_WINDOW_ROWS_PER_TILE).max(1));
            assert_eq!(
                window_partials_len(trace_len),
                WINDOW_TAIL_TENSOR_CELLS * tiles + WINDOW_TAIL_TENSOR_CELLS,
                "log {log_trace} partial layout"
            );
            let shared = max_partials_len(trace_len / 2).max(window_partials_len(trace_len));
            assert!(shared >= window_partials_len(trace_len));
            assert!(shared >= max_partials_len(trace_len / 2));
        }
        // The window layout is the larger of the two at production scale.
        assert!(window_partials_len(1 << 24) > max_partials_len((1 << 24) / 2));
    }

    #[test]
    fn dispatch_resolves_every_ruled_row_to_its_generated_kernel() {
        assert_eq!(WINDOWED_R0_KERNELS.len(), WINDOWED_R0_KERNEL_COUNT);
        assert_eq!(WINDOWED_R0_BLOCK_THREADS, 288);
        for (native, compiled, min_blocks) in WINDOWED_R0_DISPATCH {
            let entry = resolve_window_kernel(native).expect("a ruled mask dispatches");
            assert_eq!(entry.mask, compiled, "native {native:#05x} compiled mask");
            assert_eq!(entry.min_blocks, min_blocks, "native {native:#05x} bound");
            assert_eq!(
                entry.symbol_name,
                windowed_r0_kernel_symbol(compiled, min_blocks),
                "native {native:#05x} symbol"
            );
            assert_eq!(native & compiled, native, "native {native:#05x} subset");
        }
    }

    #[test]
    fn dispatch_falls_back_for_unruled_well_formed_masks() {
        let ruled: Vec<u16> = WINDOWED_R0_DISPATCH
            .iter()
            .map(|(native, ..)| *native)
            .collect();
        let fallback = resolve_window_kernel(WINDOWED_R0_FALLBACK_MASK).expect("universal kernel");
        assert_eq!(fallback.mask, WINDOWED_R0_FALLBACK_MASK);
        let mut fallbacks = 0;
        for mask in 0..=WINDOW_SHAPE_DEFINED_BITS {
            let entry = resolve_window_kernel(mask).expect("a well-formed mask always dispatches");
            let (compiled, min_blocks) =
                resolve_windowed_r0_dispatch(mask).expect("the manifest agrees");
            assert_eq!(entry.mask, compiled, "mask {mask:#05x}");
            assert_eq!(entry.min_blocks, min_blocks, "mask {mask:#05x} bound");
            if !ruled.contains(&mask) {
                assert_eq!(entry.mask, WINDOWED_R0_FALLBACK_MASK, "mask {mask:#05x}");
                assert!(mask & WINDOWED_R0_FALLBACK_MASK == mask);
                fallbacks += 1;
            }
        }
        assert_eq!(
            fallbacks,
            usize::from(WINDOW_SHAPE_DEFINED_BITS) + 1 - ruled.len()
        );
    }

    #[test]
    fn dispatch_rejects_undefined_feature_bits() {
        for mask in [0x1000u16, 0x1001, 0x8000, 0xffff] {
            assert_eq!(
                rejection(resolve_window_kernel(mask)),
                WindowBindError::UndefinedShapeBits { bits: mask },
                "mask {mask:#06x}"
            );
        }
        assert!(WindowShape::from_bits(0x1000).is_err());
    }

    #[test]
    fn generated_registry_mirrors_the_compiler_manifest() {
        assert_eq!(
            WINDOWED_R0_DISPATCH,
            gpu_gkr_compiler::WINDOWED_R0_DISPATCH,
            "dispatch map drift"
        );
        assert_eq!(
            WINDOWED_R0_FALLBACK_MASK,
            gpu_gkr_compiler::WINDOWED_R0_FALLBACK_MASK
        );
        assert_eq!(
            WINDOWED_R0_BLOCK_THREADS,
            gpu_gkr_compiler::WINDOWED_R0_BLOCK_THREADS
        );
        let bank = windowed_r0_bank();
        assert_eq!(bank.len(), WINDOWED_R0_KERNELS.len());
        for ((mask, min_blocks), entry) in bank.into_iter().zip(WINDOWED_R0_KERNELS.iter()) {
            assert_eq!(entry.mask, mask, "bank mask order");
            assert_eq!(entry.min_blocks, min_blocks, "bank bound");
            assert_eq!(
                entry.symbol_name,
                windowed_r0_kernel_symbol(mask, min_blocks)
            );
        }
    }
}
