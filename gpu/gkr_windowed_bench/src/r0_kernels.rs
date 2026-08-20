use std::ffi::c_void;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::{cudaGetSymbolAddress, cuda_struct_and_stub, CudaError};

use crate::abi::E4;
use crate::r0_abi::{R0VmDesc, R0_COEFFICIENT_CAPACITY, R0_EQ_HIGH_ELEMENTS};
use crate::r0_geometry::{R0Geometry, R0LaunchMetadata, R0LaunchPlan};

cuda_struct_and_stub! {
    static ab_gkr_windowed_r0_coeff_bank: [E4; R0_COEFFICIENT_CAPACITY];
}

cuda_struct_and_stub! {
    static ab_gkr_windowed_r0_eq_high: [E4; R0_EQ_HIGH_ELEMENTS];
}

cuda_kernel_signature_arguments_and_function!(R0Cta288Pair, desc: R0VmDesc,);

cuda_kernel_declaration!(ab_gkr_windowed_r0_cta288_pair_kernel(desc: R0VmDesc,));

cuda_kernel_signature_arguments_and_function!(R0Cta96Partitioned, desc: R0VmDesc,);

cuda_kernel_declaration!(ab_gkr_windowed_r0_cta96_partitioned_kernel(
    desc: R0VmDesc,
));

cuda_kernel_signature_arguments_and_function!(R0Cta96X0Major, desc: R0VmDesc,);

cuda_kernel_declaration!(ab_gkr_windowed_r0_cta96_x0_major_kernel(
    desc: R0VmDesc,
));

cuda_kernel_signature_arguments_and_function!(R0Cta96X1Major, desc: R0VmDesc,);

cuda_kernel_declaration!(ab_gkr_windowed_r0_cta96_x1_major_kernel(
    desc: R0VmDesc,
));

cuda_kernel_signature_arguments_and_function!(R0Cta96X2Major, desc: R0VmDesc,);

cuda_kernel_declaration!(ab_gkr_windowed_r0_cta96_x2_major_kernel(
    desc: R0VmDesc,
));

pub fn launch_r0_geometry(
    geometry: R0Geometry,
    desc: R0VmDesc,
    plan: R0LaunchPlan,
    stream: &CudaStream,
) -> CudaResult<R0LaunchMetadata> {
    validate_geometry_launch(geometry, plan)?;
    let config = CudaLaunchConfig::basic(
        (plan.grid[0], plan.grid[1], plan.grid[2]),
        (plan.block[0], plan.block[1], plan.block[2]),
        stream,
    );
    match geometry {
        R0Geometry::Cta288Pair => {
            let args = R0Cta288PairArguments::new(desc);
            R0Cta288PairFunction(ab_gkr_windowed_r0_cta288_pair_kernel).launch(&config, &args)?;
        }
        R0Geometry::Cta96Partitioned => {
            let args = R0Cta96PartitionedArguments::new(desc);
            R0Cta96PartitionedFunction(ab_gkr_windowed_r0_cta96_partitioned_kernel)
                .launch(&config, &args)?;
        }
        R0Geometry::Cta96X0Major => {
            let args = R0Cta96X0MajorArguments::new(desc);
            R0Cta96X0MajorFunction(ab_gkr_windowed_r0_cta96_x0_major_kernel)
                .launch(&config, &args)?;
        }
        R0Geometry::Cta96X1Major => {
            let args = R0Cta96X1MajorArguments::new(desc);
            R0Cta96X1MajorFunction(ab_gkr_windowed_r0_cta96_x1_major_kernel)
                .launch(&config, &args)?;
        }
        R0Geometry::Cta96X2Major => {
            let args = R0Cta96X2MajorArguments::new(desc);
            R0Cta96X2MajorFunction(ab_gkr_windowed_r0_cta96_x2_major_kernel)
                .launch(&config, &args)?;
        }
    }
    Ok(R0LaunchMetadata {
        geometry,
        symbol: r0_kernel_symbol(geometry).to_owned(),
        grid: plan.grid,
        block: plan.block,
    })
}

pub fn launch_r0_pair(
    geometry: R0Geometry,
    desc: R0VmDesc,
    plan: R0LaunchPlan,
    stream: &CudaStream,
) -> CudaResult<()> {
    validate_pair_launch(geometry, plan)?;
    launch_r0_geometry(geometry, desc, plan, stream).map(|_| ())
}

fn validate_geometry_launch(geometry: R0Geometry, plan: R0LaunchPlan) -> CudaResult<()> {
    let expected_block_x = match geometry {
        R0Geometry::Cta288Pair => 288,
        R0Geometry::Cta96Partitioned
        | R0Geometry::Cta96X0Major
        | R0Geometry::Cta96X1Major
        | R0Geometry::Cta96X2Major => 96,
    };
    let expected_grid_x = match geometry {
        R0Geometry::Cta96Partitioned => plan.row_tiles.checked_mul(3),
        _ => Some(plan.row_tiles),
    };
    if plan.geometry == geometry
        && plan.row_tiles != 0
        && plan.partial_rows == plan.row_tiles
        && expected_grid_x == Some(plan.grid[0])
        && plan.grid[1..] == [1, 1]
        && plan.block == [expected_block_x, 1, 1]
    {
        Ok(())
    } else {
        Err(CudaError::ErrorInvalidValue)
    }
}

fn r0_kernel_symbol(geometry: R0Geometry) -> &'static str {
    match geometry {
        R0Geometry::Cta288Pair => "ab_gkr_windowed_r0_cta288_pair_kernel",
        R0Geometry::Cta96Partitioned => "ab_gkr_windowed_r0_cta96_partitioned_kernel",
        R0Geometry::Cta96X0Major => "ab_gkr_windowed_r0_cta96_x0_major_kernel",
        R0Geometry::Cta96X1Major => "ab_gkr_windowed_r0_cta96_x1_major_kernel",
        R0Geometry::Cta96X2Major => "ab_gkr_windowed_r0_cta96_x2_major_kernel",
    }
}

fn validate_pair_launch(geometry: R0Geometry, plan: R0LaunchPlan) -> CudaResult<()> {
    if plan.geometry == geometry
        && matches!(
            geometry,
            R0Geometry::Cta288Pair | R0Geometry::Cta96Partitioned
        )
    {
        Ok(())
    } else {
        Err(CudaError::ErrorInvalidValue)
    }
}

pub fn r0_coefficient_bank_device_ptr() -> CudaResult<*mut E4> {
    unsafe { symbol_device_ptr(&ab_gkr_windowed_r0_coeff_bank) }
}

pub fn r0_eq_high_device_ptr() -> CudaResult<*mut E4> {
    unsafe { symbol_device_ptr(&ab_gkr_windowed_r0_eq_high) }
}

unsafe fn symbol_device_ptr<T>(symbol: *const T) -> CudaResult<*mut E4> {
    let mut ptr: *mut c_void = core::ptr::null_mut();
    unsafe { cudaGetSymbolAddress(&mut ptr, symbol.cast()) }.wrap()?;
    Ok(ptr.cast())
}

#[cfg(test)]
mod tests {
    use field::{Field, FieldExtension, PrimeField};

    use crate::abi::{BF, E4};
    use crate::r0_abi::{
        R0_CLASS_C0_LINEAR_BF, R0_CLASS_C0_LINEAR_E4, R0_CLASS_C2_PRODUCT_BF_BF,
        R0_CLASS_C2_PRODUCT_BF_E4, R0_CLASS_C2_PRODUCT_E4_E4, R0_COEFFICIENT_BANK_BIAS,
        R0_COEFFICIENT_CAPACITY, R0_COEFFICIENT_NEG_ONE, R0_COEFFICIENT_ONE,
    };
    use crate::r0_geometry::{owned_cells, R0Geometry};

    use super::{r0_kernel_symbol, validate_geometry_launch, validate_pair_launch};

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Axis {
        X0,
        X1,
        X2,
    }

    const DISTINCT_CORNERS: [u32; 8] = [1, 2, 4, 8, 16, 32, 64, 128];
    const ALL_R0_CLASSES: [u8; 5] = [
        R0_CLASS_C0_LINEAR_BF,
        R0_CLASS_C0_LINEAR_E4,
        R0_CLASS_C2_PRODUCT_BF_BF,
        R0_CLASS_C2_PRODUCT_BF_E4,
        R0_CLASS_C2_PRODUCT_E4_E4,
    ];
    const EXPECTED_FIXTURE_TENSOR: [u32; 27] = [
        2, 7, 3, 8, 64, 48, 0, 27, 27, 32, 832, 768, 128, 12_544, 12_288, 0, 6_912, 6_912, 0, 675,
        675, 0, 10_800, 10_800, 0, 6_075, 6_075,
    ];

    fn fixture_corner(x0: u32, x1: u32, x2: u32) -> u32 {
        DISTINCT_CORNERS[(4 * x0 + 2 * x1 + x2) as usize]
    }

    fn fixture_x2_delta(x0: u32, x1: u32) -> u32 {
        match (x0, x1) {
            (0 | 1, 0 | 1) => fixture_corner(x0, x1, 1) - fixture_corner(x0, x1, 0),
            (2, 0 | 1) => {
                (fixture_corner(1, x1, 1) - fixture_corner(1, x1, 0))
                    - (fixture_corner(0, x1, 1) - fixture_corner(0, x1, 0))
            }
            (0 | 1, 2) => {
                (fixture_corner(x0, 1, 1) - fixture_corner(x0, 1, 0))
                    - (fixture_corner(x0, 0, 1) - fixture_corner(x0, 0, 0))
            }
            (2, 2) => {
                let d00 = fixture_corner(0, 0, 1) - fixture_corner(0, 0, 0);
                let d01 = fixture_corner(0, 1, 1) - fixture_corner(0, 1, 0);
                let d10 = fixture_corner(1, 0, 1) - fixture_corner(1, 0, 0);
                let d11 = fixture_corner(1, 1, 1) - fixture_corner(1, 1, 0);
                d11 - d10 - d01 + d00
            }
            _ => unreachable!(),
        }
    }

    fn fixture_cell(x0: u32, x1: u32, x2: u32) -> u32 {
        ALL_R0_CLASSES
            .into_iter()
            .map(|class| match class {
                R0_CLASS_C0_LINEAR_BF | R0_CLASS_C0_LINEAR_E4 => {
                    if x0 < 2 && x1 < 2 && x2 < 2 {
                        fixture_corner(x0, x1, x2)
                    } else {
                        0
                    }
                }
                R0_CLASS_C2_PRODUCT_BF_BF
                | R0_CLASS_C2_PRODUCT_BF_E4
                | R0_CLASS_C2_PRODUCT_E4_E4 => {
                    if x2 == 0 {
                        0
                    } else {
                        fixture_x2_delta(x0, x1).pow(2)
                    }
                }
                _ => unreachable!(),
            })
            .sum()
    }

    fn fixture_tensor() -> [u32; 27] {
        core::array::from_fn(|index| {
            let x0 = index as u32 / 9;
            let x1 = index as u32 / 3 % 3;
            let x2 = index as u32 % 3;
            fixture_cell(x0, x1, x2)
        })
    }

    fn lift(value: u32) -> E4 {
        E4::from_array_of_base([
            BF::from_u32_with_reduction(value),
            BF::ZERO,
            BF::ZERO,
            BF::ZERO,
        ])
    }

    fn linear_bf(a0: BF, a1: BF, coefficient: E4, infinity: [bool; 2]) -> [E4; 3] {
        if infinity[0] || infinity[1] {
            return [E4::ZERO; 3];
        }
        let mut at_zero = coefficient;
        at_zero.mul_assign_by_base(&a0);
        let mut at_one = coefficient;
        at_one.mul_assign_by_base(&a1);
        [at_zero, at_one, E4::ZERO]
    }

    fn linear_e4(a0: E4, a1: E4, coefficient: E4, infinity: [bool; 2]) -> [E4; 3] {
        if infinity[0] || infinity[1] {
            return [E4::ZERO; 3];
        }
        let mut at_zero = a0;
        at_zero.mul_assign(&coefficient);
        let mut at_one = a1;
        at_one.mul_assign(&coefficient);
        [at_zero, at_one, E4::ZERO]
    }

    fn product_bf_bf(delta_a: BF, delta_b: BF, coefficient: E4) -> [E4; 3] {
        let mut product = delta_a;
        product.mul_assign(&delta_b);
        let mut c2 = coefficient;
        c2.mul_assign_by_base(&product);
        [E4::ZERO, c2, c2]
    }

    fn product_bf_e4(delta_a: BF, delta_b: E4, coefficient: E4) -> [E4; 3] {
        let mut c2 = delta_b;
        c2.mul_assign_by_base(&delta_a);
        c2.mul_assign(&coefficient);
        [E4::ZERO, c2, c2]
    }

    fn product_e4_e4(delta_a: E4, delta_b: E4, coefficient: E4) -> [E4; 3] {
        let mut c2 = delta_a;
        c2.mul_assign(&delta_b);
        c2.mul_assign(&coefficient);
        [E4::ZERO, c2, c2]
    }

    fn add_triplets(left: [E4; 3], right: [E4; 3]) -> [E4; 3] {
        let mut result = left;
        for (destination, value) in result.iter_mut().zip(right) {
            destination.add_assign(&value);
        }
        result
    }

    fn fixture_coefficient(id: u32, bank: &[E4], c_init: Option<u32>) -> Result<E4, ()> {
        if c_init.is_some() {
            return Err(());
        }
        match id {
            R0_COEFFICIENT_ONE => Ok(E4::ONE),
            R0_COEFFICIENT_NEG_ONE => {
                let mut value = E4::ONE;
                value.negate();
                Ok(value)
            }
            _ => bank
                .get((id - R0_COEFFICIENT_BANK_BIAS) as usize)
                .copied()
                .ok_or(()),
        }
    }

    #[test]
    fn cpu_r0_pair_model_pins_all_five_typed_classes_and_combination() {
        let coefficient = lift(2);
        let bf = BF::from_u32_with_reduction;
        let c0_bf = linear_bf(bf(3), bf(5), coefficient, [false, false]);
        let c0_e4 = linear_e4(lift(7), lift(11), coefficient, [false, false]);
        let c2_bf_bf = product_bf_bf(bf(3), bf(4), coefficient);
        let c2_bf_e4 = product_bf_e4(bf(5), lift(6), coefficient);
        let c2_e4_e4 = product_e4_e4(lift(7), lift(8), coefficient);

        assert_eq!(R0_CLASS_C0_LINEAR_BF, 0);
        assert_eq!(c0_bf, [lift(6), lift(10), E4::ZERO]);
        assert_eq!(R0_CLASS_C0_LINEAR_E4, 1);
        assert_eq!(c0_e4, [lift(14), lift(22), E4::ZERO]);
        assert_eq!(R0_CLASS_C2_PRODUCT_BF_BF, 2);
        assert_eq!(c2_bf_bf, [E4::ZERO, lift(24), lift(24)]);
        assert_eq!(R0_CLASS_C2_PRODUCT_BF_E4, 3);
        assert_eq!(c2_bf_e4, [E4::ZERO, lift(60), lift(60)]);
        assert_eq!(R0_CLASS_C2_PRODUCT_E4_E4, 4);
        assert_eq!(c2_e4_e4, [E4::ZERO, lift(112), lift(112)]);
        assert_eq!(add_triplets(c0_bf, c2_bf_bf), [lift(6), lift(34), lift(24)]);
    }

    #[test]
    fn cpu_r0_pair_model_zeroes_linear_contributions_at_x0_or_x1_infinity() {
        let finite = linear_e4(lift(3), lift(5), lift(2), [false, false]);
        assert_eq!(finite, [lift(6), lift(10), E4::ZERO]);
        assert_eq!(
            linear_e4(lift(3), lift(5), lift(2), [true, false]),
            [E4::ZERO; 3]
        );
        assert_eq!(
            linear_e4(lift(3), lift(5), lift(2), [false, true]),
            [E4::ZERO; 3]
        );
    }

    #[test]
    fn cpu_r0_pair_model_pins_literal_and_edge_banked_coefficients_without_c_init() {
        let mut bank = vec![E4::ZERO; R0_COEFFICIENT_CAPACITY];
        bank[0] = lift(17);
        bank[R0_COEFFICIENT_CAPACITY - 1] = lift(23);
        assert_eq!(fixture_coefficient(0, &bank, None).unwrap(), E4::ONE);
        let mut neg_one = E4::ONE;
        neg_one.negate();
        assert_eq!(fixture_coefficient(1, &bank, None).unwrap(), neg_one);
        assert_eq!(fixture_coefficient(2, &bank, None).unwrap(), lift(17));
        assert_eq!(
            fixture_coefficient(
                R0_COEFFICIENT_BANK_BIAS + R0_COEFFICIENT_CAPACITY as u32 - 1,
                &bank,
                None,
            )
            .unwrap(),
            lift(23)
        );
        assert!(fixture_coefficient(2, &bank, Some(0)).is_err());
    }

    #[test]
    fn cpu_r0_pair_launcher_rejects_non_pair_geometry() {
        for geometry in [
            R0Geometry::Cta96X0Major,
            R0Geometry::Cta96X1Major,
            R0Geometry::Cta96X2Major,
        ] {
            assert!(validate_pair_launch(geometry, geometry.launch_plan(3).unwrap()).is_err());
        }
        let pair = R0Geometry::Cta288Pair;
        assert!(validate_pair_launch(pair, pair.launch_plan(3).unwrap()).is_ok());
        assert!(
            validate_pair_launch(pair, R0Geometry::Cta96Partitioned.launch_plan(3).unwrap())
                .is_err()
        );
    }

    #[test]
    fn cpu_r0_axis_major_symbols_pin_mapping_and_nine_owned_indices() {
        let cases = [
            (
                R0Geometry::Cta96X0Major,
                "ab_gkr_windowed_r0_cta96_x0_major_kernel",
                Axis::X0,
                Axis::X2,
                Axis::X1,
                [
                    [0, 1, 2, 3, 4, 5, 6, 7, 8],
                    [9, 10, 11, 12, 13, 14, 15, 16, 17],
                    [18, 19, 20, 21, 22, 23, 24, 25, 26],
                ],
            ),
            (
                R0Geometry::Cta96X1Major,
                "ab_gkr_windowed_r0_cta96_x1_major_kernel",
                Axis::X1,
                Axis::X2,
                Axis::X0,
                [
                    [0, 1, 2, 9, 10, 11, 18, 19, 20],
                    [3, 4, 5, 12, 13, 14, 21, 22, 23],
                    [6, 7, 8, 15, 16, 17, 24, 25, 26],
                ],
            ),
            (
                R0Geometry::Cta96X2Major,
                "ab_gkr_windowed_r0_cta96_x2_major_kernel",
                Axis::X2,
                Axis::X1,
                Axis::X0,
                [
                    [0, 3, 6, 9, 12, 15, 18, 21, 24],
                    [1, 4, 7, 10, 13, 16, 19, 22, 25],
                    [2, 5, 8, 11, 14, 17, 20, 23, 26],
                ],
            ),
        ];
        for (geometry, symbol, fixed, triplet, enumerated, indices) in cases {
            assert_eq!(r0_kernel_symbol(geometry), symbol);
            assert_eq!(
                (fixed, triplet, enumerated),
                match geometry {
                    R0Geometry::Cta96X0Major => (Axis::X0, Axis::X2, Axis::X1),
                    R0Geometry::Cta96X1Major => (Axis::X1, Axis::X2, Axis::X0),
                    R0Geometry::Cta96X2Major => (Axis::X2, Axis::X1, Axis::X0),
                    _ => unreachable!(),
                },
            );
            let mut union = [0u8; 27];
            for (warp, expected) in indices.into_iter().enumerate() {
                assert_eq!(
                    owned_cells(geometry, warp as u32).unwrap(),
                    expected.to_vec(),
                    "{geometry:?} warp {warp}",
                );
                for index in expected {
                    union[index as usize] += 1;
                }
            }
            assert_eq!(union, [1; 27], "{geometry:?}");
            let plan = geometry.launch_plan(3).unwrap();
            assert!(validate_geometry_launch(geometry, plan).is_ok());
            assert_eq!(plan.grid, [1, 1, 1]);
            assert_eq!(plan.block, [96, 1, 1]);
        }
    }

    #[test]
    fn cpu_r0_axis_major_fixture_pins_all_five_class_arithmetic() {
        assert_eq!(ALL_R0_CLASSES, [0, 1, 2, 3, 4]);
        assert_eq!(DISTINCT_CORNERS, [1, 2, 4, 8, 16, 32, 64, 128]);
        assert_eq!(fixture_tensor(), EXPECTED_FIXTURE_TENSOR);

        let expected_x0_major = [
            [2, 7, 3, 8, 64, 48, 0, 27, 27],
            [32, 832, 768, 128, 12_544, 12_288, 0, 6_912, 6_912],
            [0, 675, 675, 0, 10_800, 10_800, 0, 6_075, 6_075],
        ];
        let expected_x1_major = [
            [2, 7, 3, 32, 832, 768, 0, 675, 675],
            [8, 64, 48, 128, 12_544, 12_288, 0, 10_800, 10_800],
            [0, 27, 27, 0, 6_912, 6_912, 0, 6_075, 6_075],
        ];
        for (geometry, expected_by_warp) in [
            (R0Geometry::Cta96X0Major, expected_x0_major),
            (R0Geometry::Cta96X1Major, expected_x1_major),
        ] {
            for (warp, expected) in expected_by_warp.into_iter().enumerate() {
                let cells = owned_cells(geometry, warp as u32).unwrap();
                let actual = core::array::from_fn(|index| fixture_tensor()[cells[index] as usize]);
                assert_eq!(actual, expected, "{geometry:?} warp {warp}");
            }
        }
    }

    #[test]
    fn cpu_r0_x2_major_fixture_pins_fixed_and_enumerated_infinities() {
        let expected_by_fixed_x2 = [
            [2, 8, 0, 32, 128, 0, 0, 0, 0],
            [7, 64, 27, 832, 12_544, 6_912, 675, 10_800, 6_075],
            [3, 48, 27, 768, 12_288, 6_912, 675, 10_800, 6_075],
        ];
        for (fixed_x2, expected) in expected_by_fixed_x2.into_iter().enumerate() {
            let cells = owned_cells(R0Geometry::Cta96X2Major, fixed_x2 as u32).unwrap();
            let actual = core::array::from_fn(|index| fixture_tensor()[cells[index] as usize]);
            assert_eq!(actual, expected, "fixed x2={fixed_x2}");
            assert_eq!(&actual[0..3], &expected[0..3], "enumerated x0=0");
            assert_eq!(&actual[3..6], &expected[3..6], "enumerated x0=1");
            assert_eq!(&actual[6..9], &expected[6..9], "enumerated x0=infinity");
        }
    }
}
