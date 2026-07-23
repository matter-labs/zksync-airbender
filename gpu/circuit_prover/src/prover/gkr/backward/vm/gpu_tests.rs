use std::collections::{HashMap, HashSet};
use std::mem::size_of;
use std::ops::{DerefMut, Range};
use std::ptr;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use era_cudart::memory::memory_copy_async;
use era_cudart::slice::DeviceSlice;
use gkr_eval_isa::bwd::batch::{pack_batch_dst, BATCH_COEFFICIENT_ONE};
use gkr_eval_isa::bwd::distill::{bind, BwdBindings};
use gkr_eval_isa::bwd::interp::{interpret_bwd_row, role_combine, sumcheck_fold_point, Role};
use gkr_eval_isa::bwd::source::{
    BwdSpecial, FoldState, MaterializationPolicy, OriginLeaf, VIRTUAL_SETUP_MATERIALIZE_DEPTH,
};
use gkr_eval_isa::eval_plan::backward_search::{SourceRoundBinding, StaticMaterialization};
use gkr_eval_isa::fwd::encode::{decode, encode};
use gkr_eval_isa::fwd::isa::{Instr, LdcSub, MovDir, OperandField, OperandLine, Program, Sign};
use gkr_eval_isa::fwd::source::virtual_setup_kind_code;
use rayon::prelude::*;

use super::compile::{load_add_sub_l0_case, AddSubBwdVmCase};
use super::desc::{
    BwdVmDesc, BwdVmSourceWindow, BWD_VM_BATCH_ACC_INIT_NONE, BWD_VM_PROGRAM_CAP,
    BWD_VM_SOURCE_READ_BASE, BWD_VM_SOURCE_READ_EXT, BWD_VM_SOURCE_VIRTUAL,
};
use super::lower::{
    artifact_static_materialization, lower_bwd_vm, BwdVmRoundBinding, ResolvedBwdSourceWindow,
    ResolvedBwdVirtualSource,
};
use super::report::{
    publish_report, time_cuda_launches, upload_incumbent_coefficients, SweepRow, SweepSelection,
    TimingSummary, SWEEP_LOG_PATH, TIMING_ITERS, WARMUP_ITERS,
};
use super::{
    bwd_vm_release_blocks_per_sm, launch_bwd_vm_release, launch_bwd_vm_validate,
    BWD_VM_ERR_SOURCE_OOB, BWD_VM_THREADS_PER_BLOCK,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::cub::device_reduce::{get_reduce_temp_storage_bytes, reduce, ReduceOperation};
use crate::ops::simple::set_by_val;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::device_structures::{DeviceVectorChunk, DeviceVectorChunkMut};
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::flat::CoefficientRecipe;
use crate::prover::gkr::backward::GpuGKRMainLayerDeferredChallengeSource;
use crate::prover::gkr::backward::{
    compact, get_eq_high_constant_device_ptr, launch_build_eq_high_and_low_groups_from_point,
    make_eq_sizes, GpuGKRMainLayerSumcheckLayerPlan, GKR_EQ_GROUP_SIZE, GKR_EQ_GROUP_TABLE_LEN,
};
use crate::prover::gkr::forward::bench_interp::fixture::CircuitFixture;
use crate::prover::gkr::forward::vm::lower::{read_place_to_gkr_address, ResolvedColumn};
use crate::prover::test_utils::make_test_context;
use crate::prover::tests::{
    prepare_basic_unrolled_async_backward_fixture, BasicUnrolledAsyncBackwardFixture,
};
use crate::prover::ProverContext;
use crate::upstream::{
    evaluate_virtual_inits_and_teardowns_base_address_setup_polys,
    evaluate_virtual_range_check_setup_poly, Field, FieldExtension, GKRAddress, PrimeField, Seed,
    TIMESTAMP_COLUMNS_NUM_BITS,
};
use cs::gkr_compiler::dag_ir::{
    BwdRegime, ChallengeRef, ChallengeResolver, LookupResolver, LookupValueKind, ReadPlace,
    ReadResolver, Resolvers, SourceKind, VirtualSetupKind, VirtualSetupResolver,
};

const BWD_VM_ERR_DESC_BOUNDS: u32 = 8192;
const BWD_VM_ERR_PROGRAM_OOB: u32 = 16384;
const BWD_VM_ERR_BAD_SPECIAL: u32 = 32;

fn bf(seed: u32) -> BF {
    BF::from_u32_with_reduction(seed)
}

fn e4(seed: u32) -> E4 {
    E4::from_array_of_base([
        bf(seed * 17 + 1),
        bf(seed * 17 + 3),
        bf(seed * 17 + 5),
        bf(seed * 17 + 7),
    ])
}

fn bit_words(value: E4) -> [u32; 4] {
    // SAFETY: E4 is the pinned four-u32 Rust/CUDA ABI field representation.
    unsafe { std::mem::transmute(value) }
}

fn assert_e4_bits(label: &str, got: &[E4], expected: &[E4]) {
    assert_eq!(got.len(), expected.len(), "{label}: length");
    for (index, (&got, &expected)) in got.iter().zip(expected).enumerate() {
        assert_eq!(
            bit_words(got),
            bit_words(expected),
            "{label}: value {index}"
        );
    }
}

fn source_program_with_first_access(field: OperandField, first_access: bool) -> Vec<u16> {
    encode(&Program {
        instrs: vec![Instr::Mov {
            dir: MovDir::AccFromSrc,
            field,
            dst: None,
            src: Some(OperandLine::Source {
                window: 0,
                column: 0,
                first_access,
            }),
        }],
    })
    .expect("synthetic source program must encode")
}

fn source_program(field: OperandField, repeated: bool) -> Vec<u16> {
    let source = |first_access| OperandLine::Source {
        window: 0,
        column: 0,
        first_access,
    };
    let mut instrs = vec![Instr::Mov {
        dir: MovDir::AccFromSrc,
        field,
        dst: None,
        src: Some(source(true)),
    }];
    if repeated {
        instrs.push(Instr::Add {
            field,
            sign: Sign::Plus,
            promote: false,
            operands: vec![source(false)],
        });
    }
    encode(&Program { instrs }).expect("synthetic source program must encode")
}

fn source_batch_program(field: OperandField, repeated: bool) -> Vec<u16> {
    let mut program = decode(&source_program(field, repeated)).unwrap();
    program
        .instrs
        .push(batch_sink(field, BATCH_COEFFICIENT_ONE));
    encode(&program).expect("synthetic source batch program must encode")
}

fn source_batch_program_with_first_access(field: OperandField, first_access: bool) -> Vec<u16> {
    let mut program = decode(&source_program_with_first_access(field, first_access)).unwrap();
    program
        .instrs
        .push(batch_sink(field, BATCH_COEFFICIENT_ONE));
    encode(&program).expect("synthetic source batch program must encode")
}

fn blank_desc(program: &[u16], n_instr: u32, logical_rows: usize) -> BwdVmDesc {
    // SAFETY: BwdVmDesc is a plain repr(C) CUDA ABI record. All-zero is valid
    // for every field, and every nonzero count/pointer used by the test is set
    // explicitly before launch.
    let mut desc: BwdVmDesc = unsafe { std::mem::zeroed() };
    desc.program[..program.len()].copy_from_slice(program);
    desc.program_lanes = program.len() as u32;
    desc.n_instr = n_instr;
    desc.logical_rows = logical_rows as u32;
    desc.batch_acc_init = BWD_VM_BATCH_ACC_INIT_NONE;
    desc
}

fn upload<T: Copy>(values: &[T], context: &ProverContext) -> DeviceAllocation<T> {
    let mut device = context
        .alloc(values.len(), AllocationPlacement::Top)
        .expect("synthetic device allocation");
    memory_copy_async(&mut device[..], values, context.get_exec_stream()).expect("synthetic H2D");
    device
}

fn download_e4(device: &DeviceAllocation<E4>, context: &ProverContext) -> Vec<E4> {
    let mut host = vec![Field::ZERO; device.len()];
    memory_copy_async(&mut host[..], &device[..], context.get_exec_stream())
        .expect("synthetic D2H");
    context
        .get_exec_stream()
        .synchronize()
        .expect("synthetic stream sync");
    host
}

fn download_u32(device: &DeviceAllocation<u32>, context: &ProverContext) -> Vec<u32> {
    let mut host = vec![0; device.len()];
    memory_copy_async(&mut host[..], &device[..], context.get_exec_stream())
        .expect("synthetic u32 D2H");
    context
        .get_exec_stream()
        .synchronize()
        .expect("synthetic u32 stream sync");
    host
}

fn expected_roles(input: &[E4], rows: usize, depth: u8, challenges: &[E4]) -> Vec<E4> {
    let mut t0 = Vec::with_capacity(rows);
    let mut t2 = Vec::with_capacity(rows);
    for row in 0..rows {
        let a = sumcheck_fold_point(&|index| input[index], 2 * row, depth, challenges)
            .expect("synthetic T0 fold");
        let b = sumcheck_fold_point(&|index| input[index], 2 * row + 1, depth, challenges)
            .expect("synthetic T2 fold");
        t0.push(role_combine(Role::T0, a, b));
        t2.push(role_combine(Role::T2, a, b));
    }
    t0.extend(t2);
    t0
}

struct ExtRun {
    diagnostic: Vec<E4>,
    published: Vec<E4>,
    error: u32,
}

fn run_ext_case(
    context: &ProverContext,
    rows: usize,
    depth: u8,
    budget_cells: u32,
    materialize: bool,
    repeated: bool,
    malformed_source_bound: bool,
) -> (ExtRun, Vec<E4>, Vec<E4>) {
    let endpoint_count = 2 * rows;
    let input = (0..endpoint_count * (1usize << depth))
        .map(|index| e4(index as u32 + 11))
        .collect::<Vec<_>>();
    let challenges = (0..depth)
        .map(|round| e4(round as u32 + 101))
        .collect::<Vec<_>>();
    let mut expected = expected_roles(&input, rows, depth, &challenges);
    if repeated {
        for value in &mut expected {
            let first = *value;
            value.add_assign(&first);
        }
    }
    let expected_published = (0..endpoint_count)
        .map(|index| {
            sumcheck_fold_point(&|source| input[source], index, depth, &challenges)
                .expect("synthetic publication fold")
        })
        .collect::<Vec<_>>();

    let input_device = upload(&input, context);
    let challenge_storage = if challenges.is_empty() {
        vec![Field::ZERO]
    } else {
        challenges.clone()
    };
    let challenge_device = upload(&challenge_storage, context);
    let poison = e4(9_999);
    let mut published_device = materialize.then(|| upload(&vec![poison; endpoint_count], context));
    let mut diagnostic_device = upload(&vec![poison; 2 * rows], context);
    let mut error_device = upload(&[0u32], context);

    let program = source_batch_program(OperandField::Ext, repeated);
    let mut desc = blank_desc(&program, if repeated { 3 } else { 2 }, rows);
    desc.round_challenges = challenge_device.as_ptr();
    desc.n_round_challenges = depth as u32;
    desc.n_source_windows = u32::from(!malformed_source_bound);
    desc.source_windows[0] = BwdVmSourceWindow {
        read_base: input_device.as_ptr().cast(),
        publish_base: published_device
            .as_mut()
            .map_or(ptr::null_mut(), |device| device.as_mut_ptr().cast()),
        read_stride_bytes: (input.len() * size_of::<E4>()) as u32,
        publish_stride_bytes: (endpoint_count * size_of::<E4>()) as u32,
        backing_depth: 0,
        target_depth: depth,
        source_kind: BWD_VM_SOURCE_READ_EXT,
        materialize: u8::from(materialize),
    };

    launch_bwd_vm_validate(
        &desc,
        budget_cells,
        error_device.as_mut_ptr(),
        diagnostic_device.as_mut_ptr(),
        context,
    )
    .expect("synthetic validate launch");
    if !malformed_source_bound {
        launch_bwd_vm_release(&desc, budget_cells, context).expect("synthetic release launch");
    }
    let diagnostic = download_e4(&diagnostic_device, context);
    let published = published_device
        .as_ref()
        .map_or_else(Vec::new, |device| download_e4(device, context));
    let mut error = [0u32];
    memory_copy_async(&mut error[..], &error_device[..], context.get_exec_stream())
        .expect("error D2H");
    context.get_exec_stream().synchronize().expect("error sync");
    (
        ExtRun {
            diagnostic,
            published,
            error: error[0],
        },
        expected,
        expected_published,
    )
}

fn run_base_plain(context: &ProverContext, rows: usize) {
    let input = (0..2 * rows)
        .map(|index| bf(index as u32 * 13 + 7))
        .collect::<Vec<_>>();
    let lifted = input
        .iter()
        .copied()
        .map(<E4 as FieldExtension<BF>>::from_base)
        .collect::<Vec<_>>();
    let expected = expected_roles(&lifted, rows, 0, &[]);
    let input_device = upload(&input, context);
    let mut diagnostic_device = upload(&vec![Field::ZERO; 2 * rows], context);
    let mut error_device = upload(&[0u32], context);
    let program = source_batch_program(OperandField::Base, false);
    let mut desc = blank_desc(&program, 2, rows);
    desc.n_source_windows = 1;
    desc.source_windows[0] = BwdVmSourceWindow {
        read_base: input_device.as_ptr().cast(),
        publish_base: ptr::null_mut(),
        read_stride_bytes: (input.len() * size_of::<BF>()) as u32,
        publish_stride_bytes: 0,
        backing_depth: 0,
        target_depth: 0,
        source_kind: BWD_VM_SOURCE_READ_BASE,
        materialize: 0,
    };
    launch_bwd_vm_validate(
        &desc,
        2,
        error_device.as_mut_ptr(),
        diagnostic_device.as_mut_ptr(),
        context,
    )
    .expect("BF validate launch");
    let diagnostic = download_e4(&diagnostic_device, context);
    assert_e4_bits("BF plain T0/T2", &diagnostic, &expected);
}

fn batch_sink(field: OperandField, coefficient: u16) -> Instr {
    Instr::Mov {
        dir: MovDir::DstFromAcc,
        field,
        dst: Some(pack_batch_dst(coefficient).expect("compact batch coefficient must encode")),
        src: None,
    }
}

fn mixed_batch_program() -> (Vec<u16>, u32) {
    let program = Program {
        instrs: vec![
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Base,
                dst: None,
                src: Some(OperandLine::Ldc {
                    sub: LdcSub::Special,
                    idx: 1,
                }),
            },
            batch_sink(OperandField::Base, BATCH_COEFFICIENT_ONE),
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Base,
                dst: None,
                src: Some(OperandLine::Ldc {
                    sub: LdcSub::Const,
                    idx: 0,
                }),
            },
            batch_sink(OperandField::Base, 0),
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Ext,
                dst: None,
                src: Some(OperandLine::Ldc {
                    sub: LdcSub::ArgDerivedE4,
                    idx: 0,
                }),
            },
            batch_sink(OperandField::Ext, BATCH_COEFFICIENT_ONE),
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Ext,
                dst: None,
                src: Some(OperandLine::Ldc {
                    sub: LdcSub::ArgDerivedE4,
                    idx: 1,
                }),
            },
            batch_sink(OperandField::Ext, 1),
        ],
    };
    let n_instr = program.instrs.len() as u32;
    (
        encode(&program).expect("mixed BF/E4 batch program must encode"),
        n_instr,
    )
}

fn expected_mixed_batch(
    coefficients: &[E4; 3],
    base: BF,
    ext_literal: E4,
    ext_weighted: E4,
    with_init: bool,
) -> E4 {
    let mut expected = if with_init { coefficients[2] } else { E4::ZERO };
    expected.add_assign(&<E4 as FieldExtension<BF>>::from_base(BF::ONE));
    let mut base_term = coefficients[0];
    base_term.mul_assign_by_base(&base);
    expected.add_assign(&base_term);
    expected.add_assign(&ext_literal);
    let mut ext_term = coefficients[1];
    ext_term.mul_assign(&ext_weighted);
    expected.add_assign(&ext_term);
    expected
}

#[test]
#[ignore] // GPU; compile unlocked, run the built executable under with_gpu_lock.sh.
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_vm_batch_accumulator_sink_parity_and_validation() {
    let context = make_test_context(16, 16);
    let rows = 5usize;
    let base = bf(37);
    let ext_literal = e4(41);
    let ext_weighted = e4(43);
    let coefficients = [e4(101), e4(103), e4(107)];
    let (program, n_instr) = mixed_batch_program();
    let eq_point = [e4(131), e4(137), e4(139)];
    let eq_sizes = make_eq_sizes(eq_point.len());
    let (eq_high, eq_low) = cpu_factored_eq(&eq_point);
    let eq_point_device = upload(&eq_point, &context);
    let mut eq_low_device = upload(&vec![E4::ZERO; GKR_EQ_GROUP_TABLE_LEN], &context);

    upload_incumbent_coefficients(&coefficients, &context)
        .expect("upload synthetic batch coefficients");
    launch_build_eq_high_and_low_groups_from_point::<E4>(
        eq_point_device.as_ptr(),
        0,
        eq_point.len(),
        get_eq_high_constant_device_ptr(),
        eq_low_device.as_mut_ptr(),
        &context,
    )
    .expect("build synthetic batch eq");
    for with_init in [false, true] {
        let poison = e4(9_999);
        let mut diagnostic_device = upload(&vec![poison; 2 * rows], &context);
        let mut contributions_device = upload(&vec![poison; 2 * rows], &context);
        let mut error_device = upload(&[0u32], &context);
        let mut desc = blank_desc(&program, n_instr, rows);
        desc.bf_constants[0] = base;
        desc.n_bf_constants = 1;
        desc.arg_derived_e4[0] = ext_literal;
        desc.arg_derived_e4[1] = ext_weighted;
        desc.n_arg_derived_e4 = 2;
        desc.n_coefficients = coefficients.len() as u32;
        desc.batch_acc_init = if with_init {
            2
        } else {
            BWD_VM_BATCH_ACC_INIT_NONE
        };
        desc.eq_low = eq_low_device.as_ptr();
        desc.eq_sizes = eq_sizes;
        desc.contributions = contributions_device.as_mut_ptr();

        launch_bwd_vm_validate(
            &desc,
            2,
            error_device.as_mut_ptr(),
            diagnostic_device.as_mut_ptr(),
            &context,
        )
        .expect("mixed batch validate launch");
        assert_eq!(
            download_u32(&error_device, &context),
            [0],
            "mixed batch validation with_init={with_init}"
        );
        let expected =
            expected_mixed_batch(&coefficients, base, ext_literal, ext_weighted, with_init);
        let expected_contributions = (0..2)
            .flat_map(|_| {
                (0..rows).map(|row| {
                    let mut value = expected;
                    value.mul_assign(&factored_eq_at(row, &eq_high, &eq_low, &eq_sizes));
                    value
                })
            })
            .collect::<Vec<_>>();
        assert_e4_bits(
            &format!("mixed batch T0/T2 with_init={with_init}"),
            &download_e4(&diagnostic_device, &context),
            &vec![expected; 2 * rows],
        );
        assert_e4_bits(
            &format!("mixed batch validate contributions with_init={with_init}"),
            &download_e4(&contributions_device, &context),
            &expected_contributions,
        );

        memory_copy_async(
            &mut contributions_device[..],
            &vec![poison; 2 * rows],
            context.get_exec_stream(),
        )
        .expect("re-poison mixed batch contributions");
        launch_bwd_vm_release(&desc, 2, &context).expect("mixed batch release launch");
        assert_e4_bits(
            &format!("mixed batch release contributions with_init={with_init}"),
            &download_e4(&contributions_device, &context),
            &expected_contributions,
        );
    }

    for (label, mut desc) in [
        {
            let invalid_coefficient = encode(&Program {
                instrs: vec![batch_sink(OperandField::Ext, 1)],
            })
            .unwrap();
            let mut desc = blank_desc(&invalid_coefficient, 1, 1);
            desc.n_coefficients = 1;
            ("invalid compact coefficient", desc)
        },
        {
            let literal = encode(&Program {
                instrs: vec![batch_sink(OperandField::Ext, BATCH_COEFFICIENT_ONE)],
            })
            .unwrap();
            let mut desc = blank_desc(&literal, 1, 1);
            desc.n_coefficients = 1;
            desc.batch_acc_init = 1;
            ("invalid batch init", desc)
        },
    ] {
        let poison = e4(8_888);
        let mut diagnostic_device = upload(&[poison; 2], &context);
        let mut error_device = upload(&[0u32], &context);
        launch_bwd_vm_validate(
            &desc,
            2,
            error_device.as_mut_ptr(),
            diagnostic_device.as_mut_ptr(),
            &context,
        )
        .unwrap_or_else(|error| panic!("{label} validate launch: {error}"));
        assert_eq!(
            download_u32(&error_device, &context),
            [BWD_VM_ERR_BAD_SPECIAL],
            "{label} error"
        );
        assert_e4_bits(
            &format!("{label} leaves diagnostics untouched"),
            &download_e4(&diagnostic_device, &context),
            &[poison; 2],
        );
    }
}

fn malformed_program_bounds_fail_before_source_access(context: &ProverContext) {
    let input = [e4(41), e4(43)];
    let input_device = upload(&input, context);
    let poison = e4(9_999);
    let mut published_device = upload(&[poison; 2], context);
    let mut diagnostic_device = upload(&[poison; 2], context);
    let mut error_device = upload(&[0u32], context);
    let program = source_program(OperandField::Ext, false);
    let mut desc = blank_desc(&program, 1, 1);
    desc.program_lanes = BWD_VM_PROGRAM_CAP as u32 + 1;
    desc.n_source_windows = 1;
    desc.source_windows[0] = BwdVmSourceWindow {
        read_base: input_device.as_ptr().cast(),
        publish_base: published_device.as_mut_ptr().cast(),
        read_stride_bytes: (input.len() * size_of::<E4>()) as u32,
        publish_stride_bytes: (2 * size_of::<E4>()) as u32,
        backing_depth: 0,
        target_depth: 0,
        source_kind: BWD_VM_SOURCE_READ_EXT,
        materialize: 1,
    };

    launch_bwd_vm_validate(
        &desc,
        2,
        error_device.as_mut_ptr(),
        diagnostic_device.as_mut_ptr(),
        context,
    )
    .expect("oversized descriptor validate launch");
    assert_eq!(
        download_u32(&error_device, context),
        [BWD_VM_ERR_DESC_BOUNDS],
        "oversized program count must report only the fatal descriptor bound"
    );
    assert_e4_bits(
        "fatal descriptor bound must prevent source publication",
        &download_e4(&published_device, context),
        &[poison; 2],
    );
}

fn truncated_multilane_instruction_fails_without_lane_oob(context: &ProverContext) {
    let input = [e4(51), e4(53)];
    let input_device = upload(&input, context);
    let poison = e4(9_999);
    let mut diagnostic_device = upload(&[poison; 2], context);
    let mut error_device = upload(&[0u32], context);
    let program = source_program(OperandField::Ext, false);
    assert_eq!(program.len(), 2, "Mov AccFromSrc is a two-lane instruction");
    let mut desc = blank_desc(&program, 1, 1);
    desc.program_lanes = 1;
    desc.n_source_windows = 1;
    desc.source_windows[0] = BwdVmSourceWindow {
        read_base: input_device.as_ptr().cast(),
        publish_base: ptr::null_mut(),
        read_stride_bytes: (input.len() * size_of::<E4>()) as u32,
        publish_stride_bytes: 0,
        backing_depth: 0,
        target_depth: 0,
        source_kind: BWD_VM_SOURCE_READ_EXT,
        materialize: 0,
    };

    launch_bwd_vm_validate(
        &desc,
        2,
        error_device.as_mut_ptr(),
        diagnostic_device.as_mut_ptr(),
        context,
    )
    .expect("truncated program validate launch");
    assert_eq!(
        download_u32(&error_device, context),
        [BWD_VM_ERR_PROGRAM_OOB],
        "truncated operand fetch must fail with the exact logical-lane bound"
    );
    assert_e4_bits(
        "truncated program must not write diagnostics",
        &download_e4(&diagnostic_device, context),
        &[poison; 2],
    );
}

fn truncated_second_operand_preflights_before_publication(context: &ProverContext) {
    let input = [e4(61), e4(63), e4(71), e4(73)];
    let input_device = upload(&input, context);
    let poison = e4(9_999);
    let mut published_device = upload(&[poison; 4], context);
    let mut diagnostic_device = upload(&[poison; 2], context);
    let mut error_device = upload(&[0u32], context);
    let program = encode(&Program {
        instrs: vec![Instr::Add {
            field: OperandField::Ext,
            sign: Sign::Plus,
            promote: true,
            operands: vec![
                OperandLine::Source {
                    window: 0,
                    column: 0,
                    first_access: true,
                },
                OperandLine::Source {
                    window: 0,
                    column: 1,
                    first_access: true,
                },
            ],
        }],
    })
    .expect("two-source Ext Add must encode");
    assert_eq!(program.len(), 3, "Add arity=2 is header plus two lanes");
    let mut desc = blank_desc(&program, 1, 1);
    desc.program_lanes = 2;
    desc.n_source_windows = 1;
    desc.source_windows[0] = BwdVmSourceWindow {
        read_base: input_device.as_ptr().cast(),
        publish_base: published_device.as_mut_ptr().cast(),
        read_stride_bytes: (2 * size_of::<E4>()) as u32,
        publish_stride_bytes: (2 * size_of::<E4>()) as u32,
        backing_depth: 0,
        target_depth: 0,
        source_kind: BWD_VM_SOURCE_READ_EXT,
        materialize: 1,
    };

    launch_bwd_vm_validate(
        &desc,
        2,
        error_device.as_mut_ptr(),
        diagnostic_device.as_mut_ptr(),
        context,
    )
    .expect("truncated second operand validate launch");
    assert_eq!(
        download_u32(&error_device, context),
        [BWD_VM_ERR_PROGRAM_OOB],
        "late logical-lane OOB must retain the dedicated exact bit"
    );
    assert_e4_bits(
        "preflight must prevent first-operand publication",
        &download_e4(&published_device, context),
        &[poison; 4],
    );
    assert_e4_bits(
        "truncated Add must not write diagnostics",
        &download_e4(&diagnostic_device, context),
        &[poison; 2],
    );

    // The same truncation in a non-final instruction makes the shared loop
    // attempt the next header. That consequential BAD_HEADER must normalize
    // to the same dedicated logical-lane error without changing poison.
    memory_copy_async(&mut error_device[..], &[0u32], context.get_exec_stream())
        .expect("non-final truncation error reset H2D");
    desc.n_instr = 2;
    launch_bwd_vm_validate(
        &desc,
        2,
        error_device.as_mut_ptr(),
        diagnostic_device.as_mut_ptr(),
        context,
    )
    .expect("non-final truncated Add validate launch");
    assert_eq!(
        download_u32(&error_device, context),
        [BWD_VM_ERR_PROGRAM_OOB],
        "non-final truncation must normalize consequential header errors"
    );
    assert_e4_bits(
        "non-final truncation must preserve publication poison",
        &download_e4(&published_device, context),
        &[poison; 4],
    );
    assert_e4_bits(
        "non-final truncation must preserve diagnostic poison",
        &download_e4(&diagnostic_device, context),
        &[poison; 2],
    );
}

fn release_publication_feeds_a_later_physical_use(context: &ProverContext) {
    let rows = 7usize;
    let depth = 2u8;
    let endpoint_count = 2 * rows;
    let original = (0..endpoint_count * (1usize << depth))
        .map(|index| e4(index as u32 + 301))
        .collect::<Vec<_>>();
    let challenges = [e4(401), e4(403)];
    let expected_roles = expected_roles(&original, rows, depth, &challenges);
    let expected_published = (0..endpoint_count)
        .map(|index| {
            sumcheck_fold_point(&|source| original[source], index, depth, &challenges)
                .expect("release publication fold")
        })
        .collect::<Vec<_>>();

    let mut input_device = upload(&original, context);
    let challenge_device = upload(&challenges, context);
    let poison = e4(9_999);
    let mut published_device = upload(&vec![poison; endpoint_count], context);
    let mut diagnostic_device = upload(&vec![poison; 2 * rows], context);
    let mut error_device = upload(&[0u32], context);
    let first_program = source_program_with_first_access(OperandField::Ext, true);
    let mut desc = blank_desc(&first_program, 1, rows);
    desc.round_challenges = challenge_device.as_ptr();
    desc.n_round_challenges = depth as u32;
    desc.n_source_windows = 1;
    desc.source_windows[0] = BwdVmSourceWindow {
        read_base: input_device.as_ptr().cast(),
        publish_base: published_device.as_mut_ptr().cast(),
        read_stride_bytes: (original.len() * size_of::<E4>()) as u32,
        publish_stride_bytes: (endpoint_count * size_of::<E4>()) as u32,
        backing_depth: 0,
        target_depth: depth,
        source_kind: BWD_VM_SOURCE_READ_EXT,
        materialize: 1,
    };

    // RELEASE runs first, with a poisoned publish backing. Its publication is
    // the observable result of this independent launch phase.
    launch_bwd_vm_release(&desc, 6, context).expect("release-only publication launch");
    assert_e4_bits(
        "release-only raw endpoint publication",
        &download_e4(&published_device, context),
        &expected_published,
    );

    // Destroy the original read values, then execute a single later physical
    // use. Correct materialization semantics must load the prior publication.
    let mutated = (0..original.len())
        .map(|index| e4(index as u32 + 7_001))
        .collect::<Vec<_>>();
    memory_copy_async(
        &mut input_device[..],
        &mutated[..],
        context.get_exec_stream(),
    )
    .expect("mutated read backing H2D");
    memory_copy_async(
        &mut diagnostic_device[..],
        &vec![poison; 2 * rows],
        context.get_exec_stream(),
    )
    .expect("diagnostic poison H2D");
    memory_copy_async(&mut error_device[..], &[0u32], context.get_exec_stream())
        .expect("error reset H2D");
    let later_program = source_batch_program_with_first_access(OperandField::Ext, false);
    desc.program.fill(0);
    desc.program[..later_program.len()].copy_from_slice(&later_program);
    desc.program_lanes = later_program.len() as u32;
    desc.n_instr = 2;
    launch_bwd_vm_validate(
        &desc,
        6,
        error_device.as_mut_ptr(),
        diagnostic_device.as_mut_ptr(),
        context,
    )
    .expect("later materialized-use validate launch");
    assert_eq!(
        download_u32(&error_device, context),
        [0],
        "later materialized source validation"
    );
    assert_e4_bits(
        "later source use must ignore mutated read backing",
        &download_e4(&diagnostic_device, context),
        &expected_roles,
    );
}

#[test]
#[ignore] // GPU; compile unlocked, run the built executable under with_gpu_lock.sh.
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_vm_synthetic_source_parity() {
    let context = make_test_context(16, 16);

    malformed_program_bounds_fail_before_source_access(&context);
    truncated_multilane_instruction_fails_without_lane_oob(&context);
    truncated_second_operand_preflights_before_publication(&context);
    release_publication_feeds_a_later_physical_use(&context);

    run_base_plain(&context, 17);

    // Every c2..c16 launch-time dynamic-smem budget, including all required
    // paired-lane tail shapes.
    let tails = [1usize, 7, 15, 16, 17];
    for budget_cells in 2..=16 {
        let rows = tails.get((budget_cells - 2) as usize).copied().unwrap_or(1);
        let (run, expected, _) = run_ext_case(&context, rows, 0, budget_cells, false, false, false);
        assert_eq!(run.error, 0, "plain E4 c{budget_cells} validation");
        assert_e4_bits(
            &format!("plain E4 c{budget_cells} rows={rows}"),
            &run.diagnostic,
            &expected,
        );
    }

    for depth in 1..=3 {
        let (run, expected, _) =
            run_ext_case(&context, 7, depth, depth as u32 + 2, false, false, false);
        assert_eq!(run.error, 0, "lazy depth 0->{depth} validation");
        assert_e4_bits(
            &format!("lazy depth 0->{depth}"),
            &run.diagnostic,
            &expected,
        );
    }

    let (materialized, expected, expected_published) =
        run_ext_case(&context, 15, 2, 6, true, true, false);
    assert_eq!(materialized.error, 0, "materializing repeated source");
    assert_e4_bits(
        "materializing repeated diagnostic",
        &materialized.diagnostic,
        &expected,
    );
    assert_e4_bits(
        "materializing raw endpoint publication",
        &materialized.published,
        &expected_published,
    );

    let (repeated, expected, _) = run_ext_case(&context, 16, 3, 7, false, true, false);
    assert_eq!(repeated.error, 0, "non-materializing repeated source");
    assert!(repeated.published.is_empty());
    assert_e4_bits(
        "non-materializing repeated diagnostic",
        &repeated.diagnostic,
        &expected,
    );

    let (malformed, _, _) = run_ext_case(&context, 1, 0, 2, false, false, true);
    assert_eq!(
        malformed.error, BWD_VM_ERR_SOURCE_OOB,
        "malformed source count must fail closed with the exact validation bit"
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_vm_virtual_setup_materialization_parity() {
    let context = make_test_context(16, 16);
    let depth_four_rows = 7usize;
    let depth_three_rows = 2 * depth_four_rows;
    let depth_three_endpoints = 2 * depth_three_rows;
    let depth_four_endpoints = 2 * depth_four_rows;
    let kinds = [
        VirtualSetupKind::RangeCheck16Bits,
        VirtualSetupKind::RangeCheckTimestamp,
        VirtualSetupKind::InitsAndTeardownsLow,
        VirtualSetupKind::InitsAndTeardownsHigh,
    ];
    let kind_codes = kinds
        .iter()
        .map(virtual_setup_kind_code)
        .collect::<Vec<_>>();
    assert_eq!(kind_codes, [0, 1, 2, 3]);
    let oracle = R0OracleResolvers {
        columns: HashMap::new(),
        challenges: HashMap::new(),
        trace_log2: 24,
    };
    let round_challenges = [e4(0x181), e4(0x183), e4(0x185), e4(0x187)];
    let mut challenge_device = upload(&round_challenges, &context);
    let program = |first_access| {
        encode(&Program {
            instrs: vec![
                Instr::Add {
                    field: OperandField::Ext,
                    sign: Sign::Plus,
                    promote: true,
                    operands: kind_codes
                        .iter()
                        .map(|&column| OperandLine::Source {
                            window: 0,
                            column: column as u8,
                            first_access,
                        })
                        .collect(),
                },
                batch_sink(OperandField::Ext, BATCH_COEFFICIENT_ONE),
            ],
        })
        .expect("four-kind virtual source program must encode")
    };
    let expected_contributions = |columns: &[Vec<E4>], rows: usize| {
        let mut expected = vec![E4::ZERO; 2 * rows];
        for values in columns {
            for row in 0..rows {
                let a = values[2 * row];
                let b = values[2 * row + 1];
                expected[row].add_assign(&role_combine(Role::T0, a, b));
                expected[rows + row].add_assign(&role_combine(Role::T2, a, b));
            }
        }
        expected
    };
    let poison = e4(0x7a00);
    let mut publications = [
        GuardedPublicationMatrix::new(4, depth_three_endpoints, poison, &context),
        GuardedPublicationMatrix::new(4, depth_three_endpoints, poison, &context),
    ];
    publications[0].poison(&context);
    let depth_three = kinds
        .iter()
        .map(|kind| {
            (0..depth_three_endpoints)
                .map(|endpoint| {
                    sumcheck_fold_point(
                        &|row| {
                            <E4 as FieldExtension<BF>>::from_base(oracle.virtual_setup(kind, row))
                        },
                        endpoint,
                        VIRTUAL_SETUP_MATERIALIZE_DEPTH,
                        &round_challenges[..VIRTUAL_SETUP_MATERIALIZE_DEPTH as usize],
                    )
                    .expect("depth-three virtual publication oracle")
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut diagnostic_device = upload(&vec![poison; 2 * depth_three_rows], &context);
    let mut error_device = upload(&[0u32], &context);
    let first_access_program = program(true);
    let mut desc = blank_desc(&first_access_program, 2, depth_three_rows);
    desc.round_challenges = challenge_device.as_ptr();
    desc.n_round_challenges = VIRTUAL_SETUP_MATERIALIZE_DEPTH as u32;
    desc.n_source_windows = 1;
    let depth_three_publish = publications[0].resolved_column(0);
    desc.source_windows[0] = BwdVmSourceWindow {
        read_base: ptr::null(),
        publish_base: depth_three_publish.matrix_base.cast(),
        read_stride_bytes: 0,
        publish_stride_bytes: depth_three_publish.stride_bytes,
        backing_depth: 0,
        target_depth: VIRTUAL_SETUP_MATERIALIZE_DEPTH,
        source_kind: BWD_VM_SOURCE_VIRTUAL,
        materialize: 1,
    };
    eprintln!("[bwd-vm-virtual] round 3/4 first-access rows={depth_three_rows}");
    launch_bwd_vm_validate(
        &desc,
        6,
        error_device.as_mut_ptr(),
        diagnostic_device.as_mut_ptr(),
        &context,
    )
    .expect("depth-three virtual first-access launch");
    assert_eq!(download_u32(&error_device, &context), [0]);
    assert_e4_bits(
        "depth-three virtual contributions",
        &download_e4(&diagnostic_device, &context),
        &expected_contributions(&depth_three, depth_three_rows),
    );
    for (&kind_code, expected) in kind_codes.iter().zip(&depth_three) {
        let column = kind_code as usize;
        assert_e4_bits(
            &format!("depth-three virtual publication kind={kind_code}"),
            &publications[0].download_column(column, depth_three_endpoints, &context),
            expected,
        );
        publications[0].assert_column_guards(column, depth_three_endpoints, &context);
    }

    let replacement_challenges = [e4(0x381), e4(0x383), e4(0x385), e4(0x387)];
    memory_copy_async(
        &mut challenge_device[..],
        &replacement_challenges,
        context.get_exec_stream(),
    )
    .expect("replace virtual challenges");
    memory_copy_async(
        &mut diagnostic_device[..],
        &vec![poison; 2 * depth_three_rows],
        context.get_exec_stream(),
    )
    .expect("re-poison virtual diagnostics");
    memory_copy_async(&mut error_device[..], &[0u32], context.get_exec_stream())
        .expect("reset virtual error");
    let cached_program = program(false);
    desc.program.fill(0);
    desc.program[..cached_program.len()].copy_from_slice(&cached_program);
    desc.program_lanes = cached_program.len() as u32;
    launch_bwd_vm_validate(
        &desc,
        6,
        error_device.as_mut_ptr(),
        diagnostic_device.as_mut_ptr(),
        &context,
    )
    .expect("depth-three cached virtual launch");
    assert_eq!(download_u32(&error_device, &context), [0]);
    assert_e4_bits(
        "depth-three cached virtual contributions ignore changed challenges",
        &download_e4(&diagnostic_device, &context),
        &expected_contributions(&depth_three, depth_three_rows),
    );

    memory_copy_async(
        &mut challenge_device[..],
        &round_challenges,
        context.get_exec_stream(),
    )
    .expect("restore virtual challenges");
    memory_copy_async(
        &mut diagnostic_device[..],
        &vec![poison; 2 * depth_three_rows],
        context.get_exec_stream(),
    )
    .expect("re-poison depth-four diagnostics");
    memory_copy_async(&mut error_device[..], &[0u32], context.get_exec_stream())
        .expect("reset depth-four virtual error");
    publications[1].poison(&context);
    let depth_four = depth_three
        .iter()
        .map(|prior| {
            (0..depth_four_endpoints)
                .map(|endpoint| {
                    let mut a = prior[2 * endpoint];
                    let mut delta = prior[2 * endpoint + 1];
                    delta.sub_assign(&a);
                    delta.mul_assign(&round_challenges[3]);
                    a.add_assign(&delta);
                    a
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let depth_four_program = program(true);
    desc.program.fill(0);
    desc.program[..depth_four_program.len()].copy_from_slice(&depth_four_program);
    desc.program_lanes = depth_four_program.len() as u32;
    desc.logical_rows = depth_four_rows as u32;
    desc.n_round_challenges = 4;
    let depth_three_read = publications[0].resolved_column(0);
    let depth_four_publish = publications[1].resolved_column(0);
    desc.source_windows[0] = BwdVmSourceWindow {
        read_base: depth_three_read.matrix_base.cast(),
        publish_base: depth_four_publish.matrix_base.cast(),
        read_stride_bytes: depth_three_read.stride_bytes,
        publish_stride_bytes: depth_four_publish.stride_bytes,
        backing_depth: VIRTUAL_SETUP_MATERIALIZE_DEPTH,
        target_depth: VIRTUAL_SETUP_MATERIALIZE_DEPTH + 1,
        source_kind: BWD_VM_SOURCE_VIRTUAL,
        materialize: 1,
    };
    eprintln!("[bwd-vm-virtual] round 4/4 materialized rows={depth_four_rows}");
    launch_bwd_vm_validate(
        &desc,
        6,
        error_device.as_mut_ptr(),
        diagnostic_device.as_mut_ptr(),
        &context,
    )
    .expect("depth-four materialized virtual launch");
    assert_eq!(download_u32(&error_device, &context), [0]);
    assert_e4_bits(
        "depth-four virtual contributions",
        &download_e4_ptr(diagnostic_device.as_ptr(), 2 * depth_four_rows, &context),
        &expected_contributions(&depth_four, depth_four_rows),
    );
    for (&kind_code, expected) in kind_codes.iter().zip(&depth_four) {
        let column = kind_code as usize;
        assert_e4_bits(
            &format!("depth-four virtual publication kind={kind_code}"),
            &publications[1].download_column(column, depth_four_endpoints, &context),
            expected,
        );
        publications[1].assert_column_guards(column, depth_four_endpoints, &context);
    }
}

enum R0HostColumn {
    Base(Vec<BF>),
    Ext(Vec<E4>),
}

struct R0OracleResolvers {
    columns: HashMap<ReadPlace, R0HostColumn>,
    challenges: HashMap<ChallengeRef, E4>,
    trace_log2: usize,
}

impl ReadResolver for R0OracleResolvers {
    fn read(&self, place: &ReadPlace, row: usize) -> E4 {
        match self
            .columns
            .get(place)
            .unwrap_or_else(|| panic!("R0 oracle missing snapshotted column {place:?}"))
        {
            R0HostColumn::Base(values) => <E4 as FieldExtension<BF>>::from_base(values[row]),
            R0HostColumn::Ext(values) => values[row],
        }
    }
}

impl LookupResolver for R0OracleResolvers {
    fn lookup(
        &self,
        kind: &LookupValueKind,
        set_index: usize,
        _evaluated_query: E4,
        row: usize,
    ) -> BF {
        panic!("R0 scalar recipe unexpectedly read lookup {kind:?} set {set_index} row {row}")
    }
}

impl VirtualSetupResolver for R0OracleResolvers {
    fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> BF {
        let value = match kind {
            VirtualSetupKind::RangeCheck16Bits => (row < (1 << 16)).then_some(row as u32),
            VirtualSetupKind::RangeCheckTimestamp => {
                (row < (1usize << TIMESTAMP_COLUMNS_NUM_BITS)).then_some(row as u32)
            }
            VirtualSetupKind::InitsAndTeardownsLow => Some(((row << 2) & 0xffff) as u32),
            VirtualSetupKind::InitsAndTeardownsHigh => Some((row >> 14) as u32),
        };
        value.map_or(Field::ZERO, BF::from_u32_unchecked)
    }

    fn virtual_setup_fold(&self, kind: &VirtualSetupKind, y: usize, ch: &[E4]) -> E4 {
        let remaining = self.trace_log2 - ch.len();
        let point = (0..self.trace_log2)
            .map(|index| {
                if index < remaining {
                    <E4 as FieldExtension<BF>>::from_base(BF::from_u32_with_reduction(
                        ((y >> (remaining - 1 - index)) & 1) as u32,
                    ))
                } else {
                    ch[self.trace_log2 - 1 - index]
                }
            })
            .collect::<Vec<_>>();
        let num_variables = self.trace_log2 as u32;
        match kind {
            VirtualSetupKind::RangeCheck16Bits => {
                evaluate_virtual_range_check_setup_poly::<BF, E4, 16>(&point, num_variables)
            }
            VirtualSetupKind::RangeCheckTimestamp => evaluate_virtual_range_check_setup_poly::<
                BF,
                E4,
                TIMESTAMP_COLUMNS_NUM_BITS,
            >(&point, num_variables),
            VirtualSetupKind::InitsAndTeardownsLow => {
                evaluate_virtual_inits_and_teardowns_base_address_setup_polys::<BF, E4, 2>(
                    &point,
                    num_variables,
                )
                .0
            }
            VirtualSetupKind::InitsAndTeardownsHigh => {
                evaluate_virtual_inits_and_teardowns_base_address_setup_polys::<BF, E4, 2>(
                    &point,
                    num_variables,
                )
                .1
            }
        }
    }
}

impl ChallengeResolver for R0OracleResolvers {
    fn challenge(&self, reference: &ChallengeRef) -> E4 {
        *self
            .challenges
            .get(reference)
            .unwrap_or_else(|| panic!("R0 oracle missing challenge {reference:?}"))
    }
}

#[test]
fn bwd_vm_virtual_setup_closed_form_matches_direct_index_fold() {
    let oracle = R0OracleResolvers {
        columns: HashMap::new(),
        challenges: HashMap::new(),
        trace_log2: 24,
    };
    let challenges = (0..6).map(|round| e4(0x160 + round)).collect::<Vec<_>>();
    let kinds = [
        VirtualSetupKind::RangeCheck16Bits,
        VirtualSetupKind::RangeCheckTimestamp,
        VirtualSetupKind::InitsAndTeardownsLow,
        VirtualSetupKind::InitsAndTeardownsHigh,
    ];
    for depth in 0..=VIRTUAL_SETUP_MATERIALIZE_DEPTH {
        let rows = 1usize << (24 - depth);
        for kind in &kinds {
            let mut sampled_rows = vec![0, 1, 3, rows - 1];
            sampled_rows.sort_unstable();
            sampled_rows.dedup();
            for row in sampled_rows {
                let direct = sumcheck_fold_point(
                    &|index| {
                        <E4 as FieldExtension<BF>>::from_base(oracle.virtual_setup(kind, index))
                    },
                    row,
                    depth,
                    &challenges,
                )
                .expect("bounded direct-index VirtualSetup fold");
                assert_eq!(
                    bit_words(oracle.virtual_setup_fold(kind, row, &challenges[..depth as usize])),
                    bit_words(direct),
                    "{kind:?} row {row} depth {depth}"
                );
            }
        }
    }
}

fn r0_source_coordinates(case: &AddSubBwdVmCase) -> Vec<(u8, u8, ReadPlace)> {
    let mut out = Vec::new();
    for (window_index, window) in case
        .compiled
        .compiled
        .source_windows
        .windows()
        .iter()
        .enumerate()
    {
        for absolute_column in window.referenced_columns() {
            let logical_column = u8::try_from(absolute_column - window.first_column)
                .expect("R0 source column must fit the wire encoding");
            let logical_window =
                u8::try_from(window_index).expect("R0 source window must fit the wire encoding");
            let place = case
                .compiled
                .compiled
                .source_windows
                .resolve_read_place(logical_window, logical_column)
                .expect("referenced R0 source must reverse to a ReadPlace");
            out.push((logical_window, logical_column, place));
        }
    }
    out
}

fn snapshot_r0_columns(
    fixture: &CircuitFixture,
    cases: &[AddSubBwdVmCase],
    elements: usize,
) -> HashMap<ReadPlace, R0HostColumn> {
    assert!(elements <= fixture.trace_len);
    let places = cases
        .iter()
        .flat_map(r0_source_coordinates)
        .map(|(_, _, place)| place)
        .collect::<HashSet<_>>();
    let mut columns = HashMap::with_capacity(places.len());
    for place in places {
        let address = read_place_to_gkr_address(&place);
        let resolved = fixture
            .resolved_storage_column(address)
            .unwrap_or_else(|| panic!("R0 source {place:?}/{address:?} is not resident"));
        let column = if resolved.is_e4 {
            let mut host = vec![E4::ZERO; elements];
            // SAFETY: `resolved.ptr` is the start of a fixture-owned E4 column
            // with exactly `trace_len` live elements. The fixture outlives the
            // copy and every later VM launch.
            let device =
                unsafe { DeviceSlice::from_raw_parts(resolved.ptr.cast::<E4>(), elements) };
            memory_copy_async(&mut host[..], device, fixture.context().get_exec_stream())
                .expect("snapshot R0 E4 source");
            fixture
                .context()
                .get_exec_stream()
                .synchronize()
                .expect("snapshot R0 E4 source sync");
            R0HostColumn::Ext(host)
        } else {
            let mut host = vec![BF::ZERO; elements];
            // SAFETY: same fixture-owned column invariant as the E4 branch,
            // with the field width established by `ResolvedColumn::is_e4`.
            let device =
                unsafe { DeviceSlice::from_raw_parts(resolved.ptr.cast::<BF>(), elements) };
            memory_copy_async(&mut host[..], device, fixture.context().get_exec_stream())
                .expect("snapshot R0 BF source");
            fixture
                .context()
                .get_exec_stream()
                .synchronize()
                .expect("snapshot R0 BF source sync");
            R0HostColumn::Base(host)
        };
        assert!(columns.insert(place, column).is_none());
    }
    columns
}

fn r0_oracle_resolvers(
    fixture: &CircuitFixture,
    cases: &[AddSubBwdVmCase],
    columns: HashMap<ReadPlace, R0HostColumn>,
) -> R0OracleResolvers {
    let references = cases
        .iter()
        .flat_map(|case| case.distilled.layer.sources.iter())
        .filter_map(|source| match &source.kind {
            SourceKind::Challenge { reference } => Some(reference.clone()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let challenges = references
        .into_iter()
        .map(|reference| {
            let value = fixture.backward_challenge_value(&reference);
            (reference, value)
        })
        .collect();
    R0OracleResolvers {
        columns,
        challenges,
        trace_log2: fixture.trace_len.trailing_zeros() as usize,
    }
}

fn resolved_r0_sources(
    fixture: &CircuitFixture,
    case: &AddSubBwdVmCase,
) -> Vec<ResolvedBwdSourceWindow> {
    r0_source_coordinates(case)
        .into_iter()
        .map(|(logical_window, logical_column, place)| {
            let read = fixture
                .resolved_storage_column(read_place_to_gkr_address(&place))
                .unwrap_or_else(|| panic!("R0 source binding missing {place:?}"));
            ResolvedBwdSourceWindow {
                logical_window,
                logical_column,
                read,
                publish: None,
                backing_depth: 0,
                target_depth: 0,
                materialize: false,
            }
        })
        .collect()
}

fn cpu_factored_eq(point: &[E4]) -> ([Vec<E4>; 2], Vec<E4>) {
    let group_count = point.len().div_ceil(GKR_EQ_GROUP_SIZE);
    assert!(
        group_count <= 3,
        "factored eq exceeds the strict 3-slot ABI"
    );
    let mut groups = Vec::with_capacity(group_count);
    let mut consumed = 0usize;
    for group in 0..group_count {
        let group_size = (point.len() - consumed).min(GKR_EQ_GROUP_SIZE);
        let mut table = vec![E4::ONE; 1usize << group_size];
        for (local, value) in table.iter_mut().enumerate() {
            for bit in 0..group_size {
                let is_one = ((local >> (group_size - 1 - bit)) & 1) != 0;
                let factor = if is_one {
                    point[consumed + bit]
                } else {
                    let mut one_minus = E4::ONE;
                    one_minus.sub_assign(&point[consumed + bit]);
                    one_minus
                };
                value.mul_assign(&factor);
            }
        }
        groups.push(table);
        consumed += group_size;
        assert_eq!(group + 1 == group_count, consumed == point.len());
    }
    let mut high = [vec![E4::ONE], vec![E4::ONE]];
    let mut low = vec![E4::ONE];
    if let Some(last) = groups.pop() {
        low = last;
    }
    for (slot, group) in groups.into_iter().enumerate() {
        high[slot] = group;
    }
    (high, low)
}

fn factored_eq_at(
    row: usize,
    high: &[Vec<E4>; 2],
    low: &[E4],
    sizes: &crate::prover::gkr::backward::GkrEqSizes,
) -> E4 {
    let shift1 = sizes.low as usize;
    let shift0 = shift1 + sizes.high[1] as usize;
    let hi0 = (row >> shift0) & ((1usize << sizes.high[0]) - 1);
    let hi1 = (row >> shift1) & ((1usize << sizes.high[1]) - 1);
    let lo = row & ((1usize << sizes.low) - 1);
    let mut value = high[0][hi0];
    value.mul_assign(&high[1][hi1]);
    value.mul_assign(&low[lo]);
    value
}

fn r0_expected_contributions(
    case: &AddSubBwdVmCase,
    oracle: &R0OracleResolvers,
    bindings: &BwdBindings,
    round_challenges: &[E4],
    high: &[Vec<E4>; 2],
    low: &[E4],
    eq_sizes: &crate::prover::gkr::backward::GkrEqSizes,
) -> Vec<E4> {
    const ROWS_PER_PROGRESS: usize = 1 << 20;
    let rows = case.trace_len / 2;
    let mut expected = vec![E4::ZERO; 2 * rows];
    let (q0, q2) = expected.split_at_mut(rows);
    let completed = AtomicUsize::new(0);
    let started = Instant::now();
    q0.par_chunks_mut(ROWS_PER_PROGRESS)
        .zip(q2.par_chunks_mut(ROWS_PER_PROGRESS))
        .enumerate()
        .for_each(|(chunk, (q0_chunk, q2_chunk))| {
            for offset in 0..q0_chunk.len() {
                let row = chunk * ROWS_PER_PROGRESS + offset;
                let resolvers = Resolvers {
                    read: oracle,
                    lookup: oracle,
                    virtual_setup: oracle,
                    challenge: oracle,
                };
                let eq = factored_eq_at(row, high, low, eq_sizes);
                let mut t0 = interpret_bwd_row(
                    &case.compiled.compiled,
                    &case.distilled,
                    bindings,
                    &resolvers,
                    Role::T0,
                    row,
                    round_challenges,
                )
                .unwrap_or_else(|error| {
                    panic!("c{} R0 row {row} T0: {error:?}", case.budget_cells)
                });
                let mut t2 = interpret_bwd_row(
                    &case.compiled.compiled,
                    &case.distilled,
                    bindings,
                    &resolvers,
                    Role::T2,
                    row,
                    round_challenges,
                )
                .unwrap_or_else(|error| {
                    panic!("c{} R0 row {row} T2: {error:?}", case.budget_cells)
                });
                t0.mul_assign(&eq);
                t2.mul_assign(&eq);
                q0_chunk[offset] = t0;
                q2_chunk[offset] = t2;
            }
            let done = completed.fetch_add(q0_chunk.len(), Ordering::Relaxed) + q0_chunk.len();
            eprintln!(
                "[bwd-vm-r0] c{} oracle rows {done}/{rows} elapsed={:.2}s",
                case.budget_cells,
                started.elapsed().as_secs_f64()
            );
        });
    expected
}

fn available_physical_cores() -> usize {
    let mut cores = HashSet::new();
    if let Ok(entries) = std::fs::read_dir("/sys/devices/system/cpu") {
        for entry in entries.flatten() {
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if !name.strip_prefix("cpu").is_some_and(|suffix| {
                !suffix.is_empty() && suffix.bytes().all(|b| b.is_ascii_digit())
            }) {
                continue;
            }
            let topology = entry.path().join("topology");
            let package = std::fs::read_to_string(topology.join("physical_package_id"));
            let core = std::fs::read_to_string(topology.join("core_id"));
            if let (Ok(package), Ok(core)) = (package, core) {
                cores.insert((package.trim().to_owned(), core.trim().to_owned()));
            }
        }
    }
    let available = std::thread::available_parallelism()
        .map(|count| count.get())
        .unwrap_or(1);
    cores.len().max(1).min(available)
}

fn assert_semantic_identity(reference: &AddSubBwdVmCase, cases: &[AddSubBwdVmCase]) {
    let reference_fragments = reference
        .distilled
        .fragments
        .stable_view(&reference.distilled);
    let reference_c_init = reference
        .distilled
        .fragments
        .stable_c_init(&reference.distilled);
    let reference_specials = (0..reference.distilled.specials.len())
        .map(|desc| {
            reference
                .distilled
                .specials
                .get(desc as u16)
                .expect("dense reference special")
                .clone()
        })
        .collect::<Vec<_>>();
    for case in cases {
        assert_eq!(case.regime, reference.regime, "semantic regime identity");
        assert_eq!(
            case.trace_len, reference.trace_len,
            "semantic trace identity"
        );
        assert_eq!(
            case.distilled.fragments.stable_view(&case.distilled),
            reference_fragments,
            "c{} stable distilled fragment identity before oracle reuse",
            case.budget_cells
        );
        assert_eq!(
            case.distilled.fragments.stable_c_init(&case.distilled),
            reference_c_init,
            "c{} stable distilled c_init identity before oracle reuse",
            case.budget_cells
        );
        let specials = (0..case.distilled.specials.len())
            .map(|desc| {
                case.distilled
                    .specials
                    .get(desc as u16)
                    .expect("dense case special")
                    .clone()
            })
            .collect::<Vec<_>>();
        assert_eq!(
            specials, reference_specials,
            "c{} distilled source/special identity before oracle reuse",
            case.budget_cells
        );
    }
}

fn ext_read_descriptors(case: &AddSubBwdVmCase) -> Vec<(u16, ReadPlace)> {
    (0..case.distilled.specials.len())
        .filter_map(|desc| {
            let desc = desc as u16;
            match case.distilled.specials.get(desc) {
                Some(BwdSpecial::FoldSource {
                    origin: OriginLeaf::Read(place),
                }) => Some((desc, place.clone())),
                _ => None,
            }
        })
        .collect()
}

fn ext_virtual_descriptors(case: &AddSubBwdVmCase) -> Vec<(u16, u8)> {
    let mut descriptors = (0..case.distilled.specials.len())
        .filter_map(|desc| {
            let desc = desc as u16;
            match case.distilled.specials.get(desc) {
                Some(BwdSpecial::FoldSource {
                    origin: OriginLeaf::VirtualSetup { kind },
                }) => Some((desc, virtual_setup_kind_code(kind) as u8)),
                _ => None,
            }
        })
        .collect::<Vec<_>>();
    descriptors.sort_unstable_by_key(|&(_, kind_code)| kind_code);
    let kind_codes = descriptors
        .iter()
        .map(|&(_, kind_code)| kind_code)
        .collect::<Vec<_>>();
    assert_eq!(
        kind_codes.iter().copied().collect::<HashSet<_>>().len(),
        kind_codes.len(),
        "Ext virtual descriptors must have unique stable kind codes"
    );
    assert!(
        kind_codes.iter().all(|&kind_code| kind_code < 4),
        "Ext virtual descriptor kind codes must index the fixed four-column matrix"
    );
    // The add/sub artifacts reference the two range-check setup kinds. The
    // focused raw-ABI parity test above separately covers all four stable kind
    // codes, while runtime storage remains one fixed four-column matrix pair.
    assert_eq!(kind_codes, [0, 1], "add/sub virtual descriptor identity");
    descriptors
}

fn virtual_round_binding(round: u8) -> SourceRoundBinding {
    SourceRoundBinding {
        state: if round > VIRTUAL_SETUP_MATERIALIZE_DEPTH {
            FoldState::Materialized
        } else {
            FoldState::LazyFromOriginals { depth: round }
        },
        store_for_next_round: round >= VIRTUAL_SETUP_MATERIALIZE_DEPTH,
    }
}

#[test]
fn bwd_vm_virtual_round_binding_materializes_at_exact_boundary() {
    for round in 0..=2 {
        assert_eq!(
            virtual_round_binding(round),
            SourceRoundBinding {
                state: FoldState::LazyFromOriginals { depth: round },
                store_for_next_round: false,
            }
        );
    }
    assert_eq!(
        virtual_round_binding(3),
        SourceRoundBinding {
            state: FoldState::LazyFromOriginals { depth: 3 },
            store_for_next_round: true,
        }
    );
    assert_eq!(
        virtual_round_binding(4),
        SourceRoundBinding {
            state: FoldState::Materialized,
            store_for_next_round: true,
        }
    );
}

const ORACLE_MAX_ROWS_PER_CHUNK: usize = 1 << 20;
const PREFLIGHT_ROWS: usize = 1 << 12;
const INDEPENDENT_ORACLE_MAX_DEPTH: u8 = 3;

fn independent_oracle_rows(round: u8, logical_rows: usize) -> Option<usize> {
    (round <= INDEPENDENT_ORACLE_MAX_DEPTH).then(|| logical_rows.min(PREFLIGHT_ROWS))
}

fn sample_direct_publication_identity(round: u8) -> bool {
    round <= VIRTUAL_SETUP_MATERIALIZE_DEPTH
}

fn oracle_chunk_ranges(rows: usize, target_workers: usize) -> Vec<Range<usize>> {
    if rows == 0 {
        return Vec::new();
    }
    let chunk_count =
        (rows.div_ceil(ORACLE_MAX_ROWS_PER_CHUNK)).max(rows.min(target_workers.max(1)));
    let rows_per_chunk = rows / chunk_count;
    let larger_chunk_count = rows % chunk_count;
    (0..chunk_count)
        .map(|chunk| {
            let start = chunk * rows_per_chunk + chunk.min(larger_chunk_count);
            let len = rows_per_chunk + usize::from(chunk < larger_chunk_count);
            start..start + len
        })
        .collect()
}

#[test]
fn bwd_vm_oracle_chunk_plan_targets_workers_and_preserves_domain() {
    let ranges = oracle_chunk_ranges(4096, 4);

    assert_eq!(ranges.len(), 4, "one task per requested worker");
    assert!(ranges.len() > 1, "bounded oracle work must be splittable");
    assert_eq!(ranges.first().map(|range| range.start), Some(0));
    assert_eq!(ranges.last().map(|range| range.end), Some(4096));
    assert!(ranges.iter().all(|range| !range.is_empty()));
    assert!(ranges.windows(2).all(|pair| pair[0].end == pair[1].start));
}

#[test]
fn bwd_vm_oracle_chunk_plan_handles_short_and_empty_domains() {
    assert_eq!(oracle_chunk_ranges(3, 4), vec![0..1, 1..2, 2..3]);
    assert!(oracle_chunk_ranges(0, 4).is_empty());

    let large = oracle_chunk_ranges(ORACLE_MAX_ROWS_PER_CHUNK + 1, 1);
    assert_eq!(large.len(), 2);
    assert!(large
        .iter()
        .all(|range| range.len() <= ORACLE_MAX_ROWS_PER_CHUNK));
}

#[test]
fn bwd_vm_oracle_chunk_plan_keeps_non_divisible_worker_ranges_in_bounds() {
    let ranges = oracle_chunk_ranges(32, 24);

    assert_eq!(ranges.len(), 24, "target the available workers");
    assert!(ranges.len() <= 24);
    assert_eq!(ranges.first().map(|range| range.start), Some(0));
    assert_eq!(ranges.last().map(|range| range.end), Some(32));
    assert!(ranges.iter().all(|range| !range.is_empty()));
    assert!(ranges.windows(2).all(|pair| pair[0].end == pair[1].start));
}

#[test]
fn bwd_vm_independent_oracle_policy_caps_depth_without_dropping_timing_rounds() {
    assert_eq!(independent_oracle_rows(3, 1 << 20), Some(PREFLIGHT_ROWS));
    assert_eq!(independent_oracle_rows(4, 1 << 20), None);
    assert_eq!(independent_oracle_rows(23, 1), None);
    assert!((0..=VIRTUAL_SETUP_MATERIALIZE_DEPTH).all(sample_direct_publication_identity));
    assert!(!(VIRTUAL_SETUP_MATERIALIZE_DEPTH + 1..=23).any(sample_direct_publication_identity));

    assert!((1..=23).all(|round| SweepSelection::All.includes("Ext", 2, round)));
}

struct RoundVirtualResolver<'a> {
    oracle: &'a R0OracleResolvers,
    descriptors: &'a [(u16, u8)],
    publications: &'a HashMap<u16, PublishedHostColumn>,
}

impl VirtualSetupResolver for RoundVirtualResolver<'_> {
    fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> BF {
        self.oracle.virtual_setup(kind, row)
    }

    fn virtual_setup_fold(&self, kind: &VirtualSetupKind, row: usize, ch: &[E4]) -> E4 {
        if ch.len() <= VIRTUAL_SETUP_MATERIALIZE_DEPTH as usize {
            return self.oracle.virtual_setup_fold(kind, row, ch);
        }
        let kind_code = virtual_setup_kind_code(kind) as u8;
        let desc = self
            .descriptors
            .iter()
            .find_map(|&(desc, code)| (code == kind_code).then_some(desc))
            .unwrap_or_else(|| panic!("missing virtual descriptor for kind code {kind_code}"));
        let publication = self.publications.get(&desc).unwrap_or_else(|| {
            panic!(
                "missing materialized virtual publication desc {desc} depth {}",
                ch.len()
            )
        });
        assert_eq!(
            publication.depth as usize,
            ch.len(),
            "virtual contribution oracle must consume the current publication"
        );
        publication.values[row]
    }
}

struct RoundReadResolver<'a> {
    oracle: &'a R0OracleResolvers,
    descriptors: &'a [(u16, ReadPlace)],
    publications: &'a HashMap<u16, PublishedHostColumn>,
}

impl ReadResolver for RoundReadResolver<'_> {
    fn read(&self, place: &ReadPlace, row: usize) -> E4 {
        if self.publications.is_empty() {
            return self.oracle.read(place, row);
        }
        let desc = self
            .descriptors
            .iter()
            .find_map(|(desc, candidate)| (candidate == place).then_some(*desc))
            .unwrap_or_else(|| panic!("materialized read oracle missing descriptor for {place:?}"));
        self.publications
            .get(&desc)
            .unwrap_or_else(|| panic!("materialized read oracle missing publication desc {desc}"))
            .values[row]
    }
}

#[allow(clippy::too_many_arguments)]
fn all_round_expected_contributions(
    case: &AddSubBwdVmCase,
    oracle: &R0OracleResolvers,
    round: u8,
    rows: usize,
    round_challenges: &[E4],
    high: &[Vec<E4>; 2],
    low: &[E4],
    eq_sizes: &crate::prover::gkr::backward::GkrEqSizes,
    pool: &rayon::ThreadPool,
    total_rounds: usize,
    read_descriptors: &[(u16, ReadPlace)],
    read_publications: &HashMap<u16, PublishedHostColumn>,
    virtual_descriptors: &[(u16, u8)],
    virtual_publications: &HashMap<u16, PublishedHostColumn>,
) -> Vec<E4> {
    let bindings = bind(
        &case.distilled,
        MaterializationPolicy::LazyUpTo(VIRTUAL_SETUP_MATERIALIZE_DEPTH),
        round,
    );
    let ranges = oracle_chunk_ranges(rows, pool.current_num_threads());
    let chunk_count = ranges.len();
    let started = Instant::now();
    let chunks = pool.install(|| {
        ranges
            .into_par_iter()
            .map(|range| {
                let start = range.start;
                let end = range.end;
                let virtual_resolver = RoundVirtualResolver {
                    oracle,
                    descriptors: virtual_descriptors,
                    publications: virtual_publications,
                };
                let read_resolver = RoundReadResolver {
                    oracle,
                    descriptors: read_descriptors,
                    publications: read_publications,
                };
                let resolvers = Resolvers {
                    read: &read_resolver,
                    lookup: oracle,
                    virtual_setup: &virtual_resolver,
                    challenge: oracle,
                };
                let mut q0 = Vec::with_capacity(end - start);
                let mut q2 = Vec::with_capacity(end - start);
                for row in start..end {
                    let eq = factored_eq_at(row, high, low, eq_sizes);
                    let mut t0 = interpret_bwd_row(
                        &case.compiled.compiled,
                        &case.distilled,
                        &bindings,
                        &resolvers,
                        Role::T0,
                        row,
                        round_challenges,
                    )
                    .unwrap_or_else(|error| panic!("round {round} row {row} T0: {error:?}"));
                    let mut t2 = interpret_bwd_row(
                        &case.compiled.compiled,
                        &case.distilled,
                        &bindings,
                        &resolvers,
                        Role::T2,
                        row,
                        round_challenges,
                    )
                    .unwrap_or_else(|error| panic!("round {round} row {row} T2: {error:?}"));
                    t0.mul_assign(&eq);
                    t2.mul_assign(&eq);
                    q0.push(t0);
                    q2.push(t2);
                }
                (q0, q2)
            })
            .collect::<Vec<_>>()
    });
    eprintln!(
        "[bwd-vm-parity] oracle round {round}/{total_rounds} complete rows={rows} tasks={chunk_count} elapsed={:.2}s",
        started.elapsed().as_secs_f64()
    );
    let mut expected = Vec::with_capacity(2 * rows);
    expected.extend(chunks.iter().flat_map(|(q0, _)| q0.iter().copied()));
    expected.extend(chunks.iter().flat_map(|(_, q2)| q2.iter().copied()));
    assert_eq!(expected.len(), 2 * rows, "ordered oracle collection");
    expected
}

const SENTINEL_GUARD: usize = 8;

struct GuardedPublicationMatrix {
    device: DeviceAllocation<E4>,
    columns: usize,
    max_column_elements: usize,
    stride_elements: usize,
    sentinel: E4,
}

impl GuardedPublicationMatrix {
    fn new(
        columns: usize,
        max_column_elements: usize,
        sentinel: E4,
        context: &ProverContext,
    ) -> Self {
        let stride_elements = max_column_elements + 2 * SENTINEL_GUARD;
        let allocation_elements = SENTINEL_GUARD + columns * stride_elements + SENTINEL_GUARD;
        assert!(
            stride_elements
                .checked_mul(size_of::<E4>())
                .is_some_and(|bytes| bytes <= u32::MAX as usize),
            "publication stride must fit the descriptor ABI"
        );
        let mut device = context
            .alloc(allocation_elements, AllocationPlacement::Top)
            .expect("maximum-sized Ext publication matrix");
        set_by_val(sentinel, device.deref_mut(), context.get_exec_stream())
            .expect("initialize Ext publication sentinels");
        Self {
            device,
            columns,
            max_column_elements,
            stride_elements,
            sentinel,
        }
    }

    fn poison(&mut self, context: &ProverContext) {
        set_by_val(
            self.sentinel,
            self.device.deref_mut(),
            context.get_exec_stream(),
        )
        .expect("poison Ext publication matrix");
    }

    fn poison_columns(
        &mut self,
        columns: impl IntoIterator<Item = usize>,
        live: usize,
        context: &ProverContext,
    ) -> era_cudart::result::CudaResult<()> {
        assert!(live <= self.max_column_elements);
        for column in columns {
            assert!(column < self.columns);
            // SAFETY: each requested column's live prefix is inside its
            // guarded stride; callers pass unique descriptor columns.
            let dst = unsafe {
                DeviceSlice::from_raw_parts_mut(self.column_ptr(column).cast_mut(), live)
            };
            set_by_val(self.sentinel, dst, context.get_exec_stream())?;
        }
        Ok(())
    }

    fn column_ptr(&self, column: usize) -> *const E4 {
        assert!(column < self.columns);
        // SAFETY: the allocation includes a leading guard and `columns`
        // complete strides. The returned pointer starts this column's live
        // region and leaves both neighboring sentinel regions in-bounds.
        unsafe {
            self.device
                .as_ptr()
                .add(SENTINEL_GUARD + column * self.stride_elements)
        }
    }

    fn resolved_column(&self, column: usize) -> ResolvedColumn {
        let matrix_base = self.column_ptr(0).cast_mut().cast::<u8>();
        ResolvedColumn {
            is_e4: true,
            ptr: self.column_ptr(column).cast::<u8>(),
            matrix_base,
            stride_bytes: (self.stride_elements * size_of::<E4>()) as u32,
        }
    }

    fn download_column(&self, column: usize, elements: usize, context: &ProverContext) -> Vec<E4> {
        assert!(elements <= self.max_column_elements);
        download_e4_ptr(self.column_ptr(column), elements, context)
    }

    fn upload_column(&mut self, column: usize, values: &[E4], context: &ProverContext) {
        assert!(values.len() <= self.max_column_elements);
        // SAFETY: the uniquely borrowed matrix owns this complete column
        // range, which is disjoint from every other stride.
        let device = unsafe {
            DeviceSlice::from_raw_parts_mut(self.column_ptr(column).cast_mut(), values.len())
        };
        memory_copy_async(device, values, context.get_exec_stream())
            .expect("upload lifted Ext original column");
    }

    fn assert_column_guards(&self, column: usize, live: usize, context: &ProverContext) {
        assert!(live <= self.max_column_elements);
        let ptr = self.column_ptr(column);
        // SAFETY: `column_ptr` documents the leading sentinel capacity.
        let prefix = download_e4_ptr(unsafe { ptr.sub(SENTINEL_GUARD) }, SENTINEL_GUARD, context);
        // SAFETY: every stride reserves two complete guard regions after the
        // maximum live extent, and `live <= max_column_elements`.
        let suffix = download_e4_ptr(unsafe { ptr.add(live) }, SENTINEL_GUARD, context);
        assert_e4_bits(
            "publication prefix sentinel",
            &prefix,
            &[self.sentinel; SENTINEL_GUARD],
        );
        assert_e4_bits(
            "publication suffix sentinel",
            &suffix,
            &[self.sentinel; SENTINEL_GUARD],
        );
    }
}

fn upload_ext_original_matrix(
    read_descriptors: &[(u16, ReadPlace)],
    desc_columns: &HashMap<u16, usize>,
    oracle: &R0OracleResolvers,
    elements: usize,
    sentinel: E4,
    context: &ProverContext,
) -> GuardedPublicationMatrix {
    assert!(elements <= 1usize << oracle.trace_log2);
    let mut matrix =
        GuardedPublicationMatrix::new(read_descriptors.len(), elements, sentinel, context);
    for &(desc, ref place) in read_descriptors {
        match oracle
            .columns
            .get(place)
            .unwrap_or_else(|| panic!("missing snapshotted Ext origin {place:?}"))
        {
            R0HostColumn::Base(values) => {
                let lifted = values[..elements]
                    .iter()
                    .copied()
                    .map(<E4 as FieldExtension<BF>>::from_base)
                    .collect::<Vec<_>>();
                matrix.upload_column(desc_columns[&desc], &lifted, context);
            }
            R0HostColumn::Ext(values) => {
                matrix.upload_column(desc_columns[&desc], &values[..elements], context);
            }
        }
        eprintln!("[bwd-vm-parity] original Ext binding desc={desc} rows={elements} field=lifted");
    }
    context
        .get_exec_stream()
        .synchronize()
        .expect("lifted Ext originals upload sync");
    matrix
}

fn download_e4_ptr(ptr: *const E4, len: usize, context: &ProverContext) -> Vec<E4> {
    let mut host = vec![E4::ZERO; len];
    // SAFETY: every caller supplies a live device range of `len` E4 values and
    // synchronizes before the owning allocation can be dropped or reused.
    let device = unsafe { DeviceSlice::from_raw_parts(ptr, len) };
    memory_copy_async(&mut host[..], device, context.get_exec_stream()).expect("guarded E4 D2H");
    context
        .get_exec_stream()
        .synchronize()
        .expect("guarded E4 D2H sync");
    host
}

struct PublishedHostColumn {
    depth: u8,
    values: Vec<E4>,
}

fn build_publication_oracle(
    read_descriptors: &[(u16, ReadPlace)],
    materialization: &StaticMaterialization,
    round: u8,
    rows: usize,
    oracle: &R0OracleResolvers,
    round_challenges: &[E4],
    previous: &HashMap<u16, PublishedHostColumn>,
    pool: &rayon::ThreadPool,
    total_rounds: usize,
) -> HashMap<u16, PublishedHostColumn> {
    const ELEMENTS_PER_CHUNK: usize = 1 << 20;
    let elements = 2 * rows;
    let mut current = HashMap::new();
    for &(desc, ref place) in read_descriptors {
        let binding = materialization.binding(desc, round).unwrap_or_else(|| {
            panic!("missing static publication binding desc {desc} round {round}")
        });
        if !binding.store_for_next_round {
            continue;
        }
        let chunk_count = elements.div_ceil(ELEMENTS_PER_CHUNK);
        let started = Instant::now();
        let chunks = pool.install(|| {
            (0..chunk_count)
                .into_par_iter()
                .map(|chunk| {
                    let start = chunk * ELEMENTS_PER_CHUNK;
                    let end = (start + ELEMENTS_PER_CHUNK).min(elements);
                    let values = (start..end)
                        .map(|index| match binding.state {
                            FoldState::LazyFromOriginals { depth } => sumcheck_fold_point(
                                &|source| oracle.read(place, source),
                                index,
                                depth,
                                round_challenges,
                            )
                            .expect("lazy publication oracle"),
                            FoldState::Materialized => {
                                let prior = previous.get(&desc).unwrap_or_else(|| {
                                    panic!(
                                        "materialized desc {desc} round {round} lacks prior publication"
                                    )
                                });
                                assert!(prior.depth < round, "materialized depth must advance");
                                sumcheck_fold_point(
                                    &|source| prior.values[source],
                                    index,
                                    round - prior.depth,
                                    &round_challenges[prior.depth as usize..round as usize],
                                )
                                .expect("materialized publication catch-up oracle")
                            }
                        })
                        .collect::<Vec<_>>();
                    eprintln!(
                        "[bwd-vm-parity] publication round {round}/{total_rounds} desc={desc} chunk={}/{chunk_count} elapsed={:.2}s",
                        chunk + 1,
                        started.elapsed().as_secs_f64()
                    );
                    values
                })
                .collect::<Vec<_>>()
        });
        let values = chunks.into_iter().flatten().collect::<Vec<_>>();
        assert_eq!(values.len(), elements);
        // Direct-from-original identity is deliberately sampled only while its
        // exponential reference remains bounded. Later rounds are derived by
        // the identical one-step recurrence from the previously proved full
        // publication array.
        if sample_direct_publication_identity(round) {
            for index in [0, elements / 2, elements - 1] {
                let direct = sumcheck_fold_point(
                    &|source| oracle.read(place, source),
                    index,
                    round,
                    round_challenges,
                )
                .expect("direct publication identity sample");
                assert_eq!(
                    bit_words(values[index]),
                    bit_words(direct),
                    "desc {desc} round {round} publication must equal sumcheck_fold_point"
                );
            }
        }
        assert!(current
            .insert(
                desc,
                PublishedHostColumn {
                    depth: round,
                    values
                }
            )
            .is_none());
    }
    current
}

fn build_virtual_publication_oracle(
    virtual_descriptors: &[(u16, u8)],
    round: u8,
    rows: usize,
    oracle: &R0OracleResolvers,
    round_challenges: &[E4],
    previous: &HashMap<u16, PublishedHostColumn>,
    pool: &rayon::ThreadPool,
    total_rounds: usize,
) -> HashMap<u16, PublishedHostColumn> {
    let binding = virtual_round_binding(round);
    if !binding.store_for_next_round {
        return HashMap::new();
    }
    const ELEMENTS_PER_CHUNK: usize = 1 << 20;
    let elements = 2 * rows;
    virtual_descriptors
        .iter()
        .map(|&(desc, kind_code)| {
            let kind = match kind_code {
                0 => VirtualSetupKind::RangeCheck16Bits,
                1 => VirtualSetupKind::RangeCheckTimestamp,
                2 => VirtualSetupKind::InitsAndTeardownsLow,
                3 => VirtualSetupKind::InitsAndTeardownsHigh,
                _ => unreachable!("stable virtual kind code"),
            };
            let chunk_count = elements.div_ceil(ELEMENTS_PER_CHUNK);
            let started = Instant::now();
            let chunks = pool.install(|| {
                (0..chunk_count)
                    .into_par_iter()
                    .map(|chunk| {
                        let start = chunk * ELEMENTS_PER_CHUNK;
                        let end = (start + ELEMENTS_PER_CHUNK).min(elements);
                        let values = match binding.state {
                            FoldState::LazyFromOriginals { depth } => {
                                assert_eq!(depth, VIRTUAL_SETUP_MATERIALIZE_DEPTH);
                                (start..end)
                                    .map(|endpoint| {
                                        sumcheck_fold_point(
                                            &|row| {
                                                <E4 as FieldExtension<BF>>::from_base(
                                                    oracle.virtual_setup(&kind, row),
                                                )
                                            },
                                            endpoint,
                                            VIRTUAL_SETUP_MATERIALIZE_DEPTH,
                                            &round_challenges
                                                [..VIRTUAL_SETUP_MATERIALIZE_DEPTH as usize],
                                        )
                                        .expect("depth-three virtual publication oracle")
                                    })
                                    .collect::<Vec<_>>()
                            }
                            FoldState::Materialized => {
                                let prior = previous.get(&desc).unwrap_or_else(|| {
                                    panic!(
                                        "materialized virtual desc {desc} round {round} lacks prior publication"
                                    )
                                });
                                assert_eq!(
                                    prior.depth.checked_add(1),
                                    Some(round),
                                    "virtual materialization advances exactly one round"
                                );
                                assert_eq!(
                                    prior.values.len(),
                                    2 * elements,
                                    "prior virtual publication is the exact two-endpoint backing"
                                );
                                (start..end)
                                    .map(|endpoint| {
                                        let mut a = prior.values[2 * endpoint];
                                        let mut delta = prior.values[2 * endpoint + 1];
                                        delta.sub_assign(&a);
                                        delta.mul_assign(&round_challenges[round as usize - 1]);
                                        a.add_assign(&delta);
                                        a
                                    })
                                    .collect::<Vec<_>>()
                            }
                        };
                        eprintln!(
                            "[bwd-vm-parity] virtual publication round {round}/{total_rounds} desc={desc} kind={kind_code} chunk={}/{chunk_count} elapsed={:.2}s",
                            chunk + 1,
                            started.elapsed().as_secs_f64()
                        );
                        values
                    })
                    .collect::<Vec<_>>()
            });
            let values = chunks.into_iter().flatten().collect::<Vec<_>>();
            assert_eq!(values.len(), elements);
            (
                desc,
                PublishedHostColumn {
                    depth: round,
                    values,
                },
            )
        })
        .collect()
}

#[derive(Clone, Copy)]
struct PublishedDeviceColumn {
    matrix: usize,
    depth: u8,
}

fn resolved_ext_round_sources(
    case: &AddSubBwdVmCase,
    materialization: &StaticMaterialization,
    round: u8,
    desc_columns: &HashMap<u16, usize>,
    original_matrix: &GuardedPublicationMatrix,
    publication_matrices: &[GuardedPublicationMatrix; 2],
    current_matrix: usize,
    previous: &HashMap<u16, PublishedDeviceColumn>,
) -> (
    Vec<ResolvedBwdSourceWindow>,
    HashMap<GKRAddress, ResolvedColumn>,
    Vec<u16>,
    &'static str,
) {
    let mut resolved_by_address = HashMap::new();
    let mut stored = Vec::new();
    let mut any_materialized = false;
    let sources = r0_source_coordinates(case)
        .into_iter()
        .map(|(logical_window, logical_column, place)| {
            let desc = case
                .compiled
                .compiled
                .source_windows
                .fold_desc(logical_window, logical_column)
                .expect("Ext source coordinate must carry its read-origin fold descriptor");
            let binding = materialization.binding(desc, round).unwrap_or_else(|| {
                panic!("missing literal static binding desc {desc} round {round}")
            });
            let (read, backing_depth) = match binding.state {
                FoldState::LazyFromOriginals { depth } => {
                    assert_eq!(
                        depth, round,
                        "LazyFromOriginals depth is the literal artifact round"
                    );
                    (original_matrix.resolved_column(desc_columns[&desc]), 0)
                }
                FoldState::Materialized => {
                    any_materialized = true;
                    let prior = previous.get(&desc).unwrap_or_else(|| {
                        panic!("materialized desc {desc} round {round} lacks prior publication")
                    });
                    assert_ne!(
                        prior.matrix, current_matrix,
                        "ping-pong write matrix must not alias the named prior backing"
                    );
                    (
                        publication_matrices[prior.matrix].resolved_column(desc_columns[&desc]),
                        prior.depth,
                    )
                }
            };
            // A materialized source names exactly the prior published backing.
            // Its depth remains the depth actually stored there; the VM catches
            // up to `round` itself, which is the no-eager-fold contract.
            assert!(backing_depth <= round);
            let publish = binding.store_for_next_round.then(|| {
                stored.push(desc);
                publication_matrices[current_matrix].resolved_column(desc_columns[&desc])
            });
            let address = read_place_to_gkr_address(&place);
            if let Some(prior) = resolved_by_address.insert(address, read) {
                assert_eq!(
                    (
                        prior.is_e4,
                        prior.ptr,
                        prior.matrix_base,
                        prior.stride_bytes
                    ),
                    (read.is_e4, read.ptr, read.matrix_base, read.stride_bytes),
                    "one source address must resolve to one round backing"
                );
            }
            ResolvedBwdSourceWindow {
                logical_window,
                logical_column,
                read,
                publish,
                backing_depth,
                target_depth: round,
                materialize: binding.store_for_next_round,
            }
        })
        .collect::<Vec<_>>();
    stored.sort_unstable();
    stored.dedup();
    (
        sources,
        resolved_by_address,
        stored,
        if any_materialized {
            "materialized"
        } else {
            "lazy"
        },
    )
}

fn resolved_ext_virtual_sources(
    virtual_descriptors: &[(u16, u8)],
    round: u8,
    virtual_publications: &[GuardedPublicationMatrix; 2],
    current_matrix: usize,
    previous_virtual: &HashMap<u16, PublishedDeviceColumn>,
) -> Vec<ResolvedBwdVirtualSource> {
    virtual_descriptors
        .iter()
        .map(|&(desc, kind_code)| {
            let binding = virtual_round_binding(round);
            match binding.state {
                FoldState::LazyFromOriginals { depth } => {
                    assert!(depth <= VIRTUAL_SETUP_MATERIALIZE_DEPTH);
                    ResolvedBwdVirtualSource {
                        desc,
                        read: None,
                        publish: binding.store_for_next_round.then(|| {
                            virtual_publications[current_matrix].resolved_column(kind_code as usize)
                        }),
                        backing_depth: 0,
                        target_depth: round,
                        materialize: binding.store_for_next_round,
                    }
                }
                FoldState::Materialized => {
                    let prior = previous_virtual[&desc];
                    assert_ne!(
                        prior.matrix, current_matrix,
                        "virtual ping-pong write matrix must not alias prior backing"
                    );
                    ResolvedBwdVirtualSource {
                        desc,
                        read: Some(
                            virtual_publications[prior.matrix].resolved_column(kind_code as usize),
                        ),
                        publish: Some(
                            virtual_publications[current_matrix]
                                .resolved_column(kind_code as usize),
                        ),
                        backing_depth: prior.depth,
                        target_depth: round,
                        materialize: true,
                    }
                }
            }
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn run_all_budget_coordinate(
    fixture: &CircuitFixture,
    cases: &[AddSubBwdVmCase],
    expected: &[E4],
    round: u8,
    total_rounds: usize,
    z: E4,
    round_challenges: &[E4],
    eq_low_device: &DeviceAllocation<E4>,
    eq_sizes: crate::prover::gkr::backward::GkrEqSizes,
    materialization: Option<&StaticMaterialization>,
    desc_columns: &HashMap<u16, usize>,
    original_matrix: Option<&GuardedPublicationMatrix>,
    publication_matrices: Option<&mut [GuardedPublicationMatrix; 2]>,
    previous_device: &HashMap<u16, PublishedDeviceColumn>,
    current_host: &HashMap<u16, PublishedHostColumn>,
    virtual_descriptors: &[(u16, u8)],
    virtual_publications: Option<&mut [GuardedPublicationMatrix; 2]>,
    previous_virtual: &HashMap<u16, PublishedDeviceColumn>,
    current_virtual: &HashMap<u16, PublishedHostColumn>,
) {
    let context = fixture.context();
    let rows = expected.len() / 2;
    assert_eq!(expected.len(), 2 * rows);
    let contribution_sentinel = e4(0x7300 + round as u32);
    let mut contributions_device = context
        .alloc(2 * rows + 2 * SENTINEL_GUARD, AllocationPlacement::Top)
        .expect("guarded all-round contributions");
    set_by_val(
        contribution_sentinel,
        contributions_device.deref_mut(),
        context.get_exec_stream(),
    )
    .expect("initialize contribution guards");
    let mut error_device = upload(&[0u32], context);
    let temp_bytes = get_reduce_temp_storage_bytes::<E4>(ReduceOperation::Sum, rows as i32)
        .expect("all-round two-half reduction temp size");
    let mut reduction_temp = context
        .alloc(temp_bytes, AllocationPlacement::Top)
        .expect("all-round two-half reduction temp");
    let mut reduction_output = upload(&[E4::ZERO; 2], context);
    let contribution_ptr = unsafe {
        // SAFETY: the allocation reserves a complete leading guard followed by
        // exactly `2 * rows` live E4 values.
        contributions_device.as_mut_ptr().add(SENTINEL_GUARD)
    };
    let expected_q0 = sum_half(&expected[..rows]);
    let expected_q2 = sum_half(&expected[rows..]);
    let current_matrix = (round as usize) & 1;
    let is_ext = materialization.is_some();
    let mut publication_matrices = publication_matrices;
    let mut virtual_publications = virtual_publications;

    for case in cases {
        let (sources, resolved_by_address, stored, mode) =
            if let (Some(materialization), Some(original_matrix), Some(matrices)) = (
                materialization,
                original_matrix,
                publication_matrices.as_deref(),
            ) {
                resolved_ext_round_sources(
                    case,
                    materialization,
                    round,
                    desc_columns,
                    original_matrix,
                    matrices,
                    current_matrix,
                    previous_device,
                )
            } else {
                let sources = resolved_r0_sources(fixture, case);
                let resolved = r0_source_coordinates(case)
                    .into_iter()
                    .map(|(_, _, place)| {
                        let address = read_place_to_gkr_address(&place);
                        let column = fixture
                            .resolved_storage_column(address)
                            .unwrap_or_else(|| panic!("R0 source binding missing {place:?}"));
                        (address, column)
                    })
                    .collect();
                (sources, resolved, Vec::new(), "lazy")
            };
        let virtual_sources = virtual_publications
            .as_deref()
            .map_or_else(Vec::new, |matrices| {
                resolved_ext_virtual_sources(
                    virtual_descriptors,
                    round,
                    matrices,
                    current_matrix,
                    previous_virtual,
                )
            });
        let mut expected_stored = current_host.keys().copied().collect::<Vec<_>>();
        expected_stored.sort_unstable();
        assert_eq!(
            stored, expected_stored,
            "c{} round {round} publication policy",
            case.budget_cells
        );
        eprintln!(
            "[bwd-vm-parity] budget c{} round {round}/{total_rounds} rows={rows} mode={mode}",
            case.budget_cells
        );
        let resolve_source = |address| resolved_by_address.get(&address).copied();
        let runtime = BwdVmRoundBinding {
            round,
            rows: rows as u32,
            round_challenges,
            sources: &sources,
            virtual_sources: &virtual_sources,
            resolve_source: &resolve_source,
            eq_low: eq_low_device.as_ptr(),
            eq_sizes,
            contributions: contribution_ptr,
        };
        let setup = lower_bwd_vm(
            &case.compiled,
            &case.distilled,
            &runtime,
            &|reference| fixture.backward_challenge_value(reference),
            &|recipe| fixture.evaluate_backward_recipe(&case.distilled.layer, recipe),
        )
        .unwrap_or_else(|error| {
            panic!(
                "lower add/sub {:?} c{} round {round}: {error:?}",
                case.regime, case.budget_cells
            )
        });
        if round == 0 {
            eprintln!(
                "[bwd-vm-parity] descriptor {:?} c{} instr={} lanes={} windows={} specials={} cells={} rows={}",
                case.regime,
                case.budget_cells,
                setup.desc.n_instr,
                setup.desc.program_lanes,
                setup.desc.n_source_windows,
                setup.desc.n_specials,
                setup.desc.cell_count,
                setup.desc.logical_rows,
            );
        }

        let mut first_release: Option<Vec<E4>> = None;
        for phase in 0..3 {
            {
                let mut live =
                    DeviceVectorChunkMut::new(&mut contributions_device, SENTINEL_GUARD, 2 * rows);
                set_by_val(contribution_sentinel, &mut live, context.get_exec_stream())
                    .expect("poison all-round contributions");
            }
            if is_ext {
                publication_matrices
                    .as_deref_mut()
                    .expect("Ext publication matrices")[current_matrix]
                    .poison(context);
                if virtual_round_binding(round).store_for_next_round {
                    virtual_publications
                        .as_deref_mut()
                        .expect("Ext virtual publication matrices")[current_matrix]
                        .poison(context);
                }
            }
            memory_copy_async(&mut error_device[..], &[0u32], context.get_exec_stream())
                .expect("reset all-round validation error");
            setup
                .upload_constant_banks(context)
                .expect("upload all-round VM constant banks");
            if phase == 0 {
                launch_bwd_vm_validate(
                    &setup.desc,
                    case.budget_cells as u32,
                    error_device.as_mut_ptr(),
                    ptr::null_mut(),
                    context,
                )
                .expect("all-round validate launch");
                assert_eq!(
                    download_u32(&error_device, context),
                    [0],
                    "c{} round {round} validation error",
                    case.budget_cells
                );
            } else {
                launch_bwd_vm_release(&setup.desc, case.budget_cells as u32, context)
                    .expect("all-round release launch");
            }

            let got = download_e4_ptr(contribution_ptr, 2 * rows, context);
            assert_e4_bits(
                &format!("c{} round {round} phase {phase} q0", case.budget_cells),
                &got[..rows],
                &expected[..rows],
            );
            assert_e4_bits(
                &format!("c{} round {round} phase {phase} q2", case.budget_cells),
                &got[rows..],
                &expected[rows..],
            );
            let prefix = download_e4_ptr(contributions_device.as_ptr(), SENTINEL_GUARD, context);
            let suffix = download_e4_ptr(
                unsafe { contribution_ptr.add(2 * rows) },
                SENTINEL_GUARD,
                context,
            );
            assert_e4_bits(
                "contribution prefix sentinel",
                &prefix,
                &[contribution_sentinel; SENTINEL_GUARD],
            );
            assert_e4_bits(
                "contribution suffix sentinel",
                &suffix,
                &[contribution_sentinel; SENTINEL_GUARD],
            );

            if let Some(matrices) = publication_matrices.as_deref() {
                for &desc in &stored {
                    let expected_publication = &current_host[&desc].values;
                    let matrix = &matrices[current_matrix];
                    assert_e4_bits(
                        &format!(
                            "c{} round {round} phase {phase} first-access publication desc {desc}",
                            case.budget_cells
                        ),
                        &matrix.download_column(
                            desc_columns[&desc],
                            expected_publication.len(),
                            context,
                        ),
                        expected_publication,
                    );
                    matrix.assert_column_guards(
                        desc_columns[&desc],
                        expected_publication.len(),
                        context,
                    );
                }
            }
            if let Some(matrices) = virtual_publications.as_deref() {
                for &(desc, kind_code) in virtual_descriptors {
                    let Some(expected_publication) = current_virtual.get(&desc) else {
                        continue;
                    };
                    let matrix = &matrices[current_matrix];
                    assert_e4_bits(
                        &format!(
                            "c{} round {round} phase {phase} virtual publication desc {desc}",
                            case.budget_cells
                        ),
                        &matrix.download_column(
                            kind_code as usize,
                            expected_publication.values.len(),
                            context,
                        ),
                        &expected_publication.values,
                    );
                    matrix.assert_column_guards(
                        kind_code as usize,
                        expected_publication.values.len(),
                        context,
                    );
                }
            }

            if phase > 0 {
                if let Some(first) = &first_release {
                    assert_e4_bits(
                        &format!(
                            "c{} round {round} poisoned release determinism",
                            case.budget_cells
                        ),
                        &got,
                        first,
                    );
                } else {
                    first_release = Some(got);
                }
            }
        }

        // SAFETY: one temporary mutable view covers the live reduction temp;
        // the two CUB reductions use it serially on exec_stream.
        let reduction_temp_slice = unsafe {
            DeviceSlice::from_raw_parts_mut(reduction_temp.as_mut_ptr(), reduction_temp.len())
        };
        let q0_half = DeviceVectorChunk::new(&contributions_device, SENTINEL_GUARD, rows);
        reduce(
            ReduceOperation::Sum,
            reduction_temp_slice,
            &q0_half,
            &mut reduction_output[0],
            context.get_exec_stream(),
        )
        .expect("all-round q0 reduction");
        let q2_half = DeviceVectorChunk::new(&contributions_device, SENTINEL_GUARD + rows, rows);
        reduce(
            ReduceOperation::Sum,
            reduction_temp_slice,
            &q2_half,
            &mut reduction_output[1],
            context.get_exec_stream(),
        )
        .expect("all-round q2 reduction");
        let reduced = download_e4(&reduction_output, context);
        assert_e4_bits(
            &format!("c{} round {round} exact reductions", case.budget_cells),
            &reduced,
            &[expected_q0, expected_q2],
        );
        assert_recovery_and_production_coefficients(
            case.budget_cells,
            round,
            reduced[0],
            reduced[1],
            z,
            context,
        );
        eprintln!(
            "[bwd-vm-parity] budget c{} round {round}/{total_rounds} complete",
            case.budget_cells
        );
    }
}

fn sum_half(values: &[E4]) -> E4 {
    values.iter().copied().fold(E4::ZERO, |mut sum, value| {
        sum.add_assign(&value);
        sum
    })
}

fn independent_lagrange_round_oracle(q0: E4, q1: E4, q2: E4, z: E4) -> ([E4; 3], [E4; 4]) {
    let mut two = E4::ONE;
    two.add_assign(&E4::ONE);
    let points = [E4::ZERO, E4::ONE, two];
    let evaluations = [q0, q1, q2];
    let mut q_coefficients = [E4::ZERO; 3];

    // Construct each Lagrange basis polynomial from its roots. This deliberately
    // avoids the closed-form c/d recovery equations exercised below.
    for basis_index in 0..points.len() {
        let mut basis = [E4::ZERO; 3];
        basis[0] = E4::ONE;
        let mut basis_degree = 0;
        let mut denominator = E4::ONE;
        for other_index in 0..points.len() {
            if basis_index == other_index {
                continue;
            }

            let mut next_basis = [E4::ZERO; 3];
            for degree in 0..=basis_degree {
                let mut constant_term = basis[degree];
                constant_term.mul_assign(&points[other_index]);
                constant_term.negate();
                next_basis[degree].add_assign(&constant_term);
                next_basis[degree + 1].add_assign(&basis[degree]);
            }
            basis = next_basis;
            basis_degree += 1;

            let mut denominator_factor = points[basis_index];
            denominator_factor.sub_assign(&points[other_index]);
            denominator.mul_assign(&denominator_factor);
        }

        let mut scale = evaluations[basis_index];
        scale.mul_assign(&denominator.inverse().expect("distinct Lagrange points"));
        for (coefficient, basis_coefficient) in q_coefficients.iter_mut().zip(basis) {
            let mut term = basis_coefficient;
            term.mul_assign(&scale);
            coefficient.add_assign(&term);
        }
    }

    let mut eq_constant = E4::ONE;
    eq_constant.sub_assign(&z);
    let mut eq_linear = z;
    eq_linear.double();
    eq_linear.sub_assign(&E4::ONE);
    let eq_coefficients = [eq_constant, eq_linear];
    let mut round_coefficients = [E4::ZERO; 4];
    for (q_degree, q_coefficient) in q_coefficients.iter().enumerate() {
        for (eq_degree, eq_coefficient) in eq_coefficients.iter().enumerate() {
            let mut term = *q_coefficient;
            term.mul_assign(eq_coefficient);
            round_coefficients[q_degree + eq_degree].add_assign(&term);
        }
    }

    (q_coefficients, round_coefficients)
}

fn assert_recovery_and_production_coefficients(
    budget_cells: usize,
    round: u8,
    q0: E4,
    q2: E4,
    z: E4,
    context: &ProverContext,
) {
    let coordinate = budget_cells as u32 + 32 * round as u32;
    let label = format!("c{budget_cells} r{round}");
    let q1_oracle = e4(0x5100 + coordinate);
    let eq_prefactor = e4(0x6100 + coordinate);
    assert_ne!(z, E4::ZERO);
    assert_ne!(eq_prefactor, E4::ZERO);

    let mut one_minus_z = E4::ONE;
    one_minus_z.sub_assign(&z);
    let mut normalized_claim = one_minus_z;
    normalized_claim.mul_assign(&q0);
    let mut zq1 = z;
    zq1.mul_assign(&q1_oracle);
    normalized_claim.add_assign(&zq1);
    let mut identity = one_minus_z;
    identity.mul_assign(&q0);
    identity.add_assign(&zq1);
    assert_eq!(identity, normalized_claim, "{label} claim identity");

    let mut claim = normalized_claim;
    claim.mul_assign(&eq_prefactor);
    let mut recovered_q1 = claim;
    recovered_q1.mul_assign(&eq_prefactor.inverse().expect("nonzero eq prefactor"));
    let mut bq0 = one_minus_z;
    bq0.mul_assign(&q0);
    recovered_q1.sub_assign(&bq0);
    recovered_q1.mul_assign(&z.inverse().expect("nonzero z"));
    assert_eq!(recovered_q1, q1_oracle, "{label} recovered q1");

    let mut two_q1 = recovered_q1;
    two_q1.double();
    let mut recovered_c = q2;
    recovered_c.sub_assign(&two_q1);
    recovered_c.add_assign(&q0);
    let mut two = E4::ONE;
    two.add_assign(&E4::ONE);
    recovered_c.mul_assign(&two.inverse().expect("nonzero two"));
    let mut recovered_d = recovered_q1;
    recovered_d.sub_assign(&q0);
    recovered_d.sub_assign(&recovered_c);

    let (oracle_q_coefficients, oracle_round_coefficients) =
        independent_lagrange_round_oracle(q0, q1_oracle, q2, z);
    let oracle_d = oracle_q_coefficients[1];
    let oracle_c = oracle_q_coefficients[2];
    assert_eq!(recovered_c, oracle_c, "{label} recovered c");
    assert_eq!(recovered_d, oracle_d, "{label} recovered d");

    let mut oracle_q2 = oracle_c;
    oracle_q2.double();
    oracle_q2.double();
    let mut two_d = oracle_d;
    two_d.double();
    oracle_q2.add_assign(&two_d);
    oracle_q2.add_assign(&q0);
    assert_eq!(oracle_q2, q2, "{label} recovered c/d oracle");

    let cpu_coefficients = prover::gkr::sumcheck::output_univariate_monomial_form_max_quadratic::<
        BF,
        E4,
    >(z, normalized_claim, q0, recovered_c);
    assert_e4_bits(
        &format!("{label} independent CPU coefficients"),
        &cpu_coefficients,
        &oracle_round_coefficients,
    );

    let reduction_device = upload(&[q0, recovered_c], context);
    let prev_coord_device = upload(&[z], context);
    let mut seed_device = upload(&Seed::default().0[..], context);
    let mut claim_device = upload(&[claim], context);
    let mut eq_prefactor_device = upload(&[eq_prefactor], context);
    let mut coefficients_device = upload(&[E4::ZERO; 4], context);
    let mut challenge_device = upload(&[E4::ZERO], context);
    crate::ops::gkr_ops::backward_sumcheck_round_update(
        &reduction_device,
        &prev_coord_device,
        &mut seed_device,
        &mut claim_device,
        &mut eq_prefactor_device,
        &mut coefficients_device,
        &mut challenge_device,
        context.get_exec_stream(),
    )
    .expect("production backward round-update launch");
    let gpu_coefficients = download_e4(&coefficients_device, context);
    assert_e4_bits(
        &format!("{label} independent GPU coefficients"),
        &gpu_coefficients,
        &oracle_round_coefficients,
    );
    assert_e4_bits(
        &format!("{label} production four coefficients"),
        &gpu_coefficients,
        &cpu_coefficients,
    );
}

fn run_add_sub_r0_budget(
    fixture: &CircuitFixture,
    case: &AddSubBwdVmCase,
    oracle: &R0OracleResolvers,
    claim_point: &[E4],
    round_challenges: &[E4],
) {
    let context = fixture.context();
    let rows = case.trace_len / 2;
    assert_eq!(rows, 1usize << claim_point[1..].len());
    let eq_sizes = make_eq_sizes(claim_point[1..].len());
    let (cpu_eq_high, cpu_eq_low) = cpu_factored_eq(&claim_point[1..]);
    let bindings = bind(&case.distilled, MaterializationPolicy::LazyUpTo(0), 0);
    eprintln!(
        "[bwd-vm-r0] c{} phase=oracle rows={rows}",
        case.budget_cells
    );
    let expected = r0_expected_contributions(
        case,
        oracle,
        &bindings,
        round_challenges,
        &cpu_eq_high,
        &cpu_eq_low,
        &eq_sizes,
    );

    let claim_point_device = upload(claim_point, context);
    let mut eq_low_device = upload(&vec![E4::ZERO; GKR_EQ_GROUP_TABLE_LEN], context);
    launch_build_eq_high_and_low_groups_from_point::<E4>(
        claim_point_device.as_ptr(),
        1,
        claim_point[1..].len(),
        get_eq_high_constant_device_ptr(),
        eq_low_device.as_mut_ptr(),
        context,
    )
    .expect("build production factored eq");

    let poison = e4(0x7f00 + case.budget_cells as u32);
    let poison_values = vec![poison; 2 * rows];
    let mut contributions_device = upload(&poison_values, context);
    let mut error_device = upload(&[0u32], context);
    let sources = resolved_r0_sources(fixture, case);
    let resolve_source = |address| fixture.resolved_storage_column(address);
    let runtime = BwdVmRoundBinding {
        round: 0,
        rows: rows as u32,
        round_challenges,
        sources: &sources,
        virtual_sources: &[],
        resolve_source: &resolve_source,
        eq_low: eq_low_device.as_ptr(),
        eq_sizes,
        contributions: contributions_device.as_mut_ptr(),
    };
    let setup = lower_bwd_vm(
        &case.compiled,
        &case.distilled,
        &runtime,
        &|reference| fixture.backward_challenge_value(reference),
        &|recipe| fixture.evaluate_backward_recipe(&case.distilled.layer, recipe),
    )
    .unwrap_or_else(|error| panic!("lower add/sub R0 c{}: {error:?}", case.budget_cells));

    setup
        .upload_constant_banks(context)
        .expect("upload R0 VM coefficient/derived banks before validate");
    launch_bwd_vm_validate(
        &setup.desc,
        case.budget_cells as u32,
        error_device.as_mut_ptr(),
        ptr::null_mut(),
        context,
    )
    .expect("real R0 validate launch");
    assert_eq!(
        download_u32(&error_device, context),
        [0],
        "c{} validation error",
        case.budget_cells
    );
    assert_e4_bits(
        &format!("c{} validate contributions", case.budget_cells),
        &download_e4(&contributions_device, context),
        &expected,
    );

    let mut first_release: Option<Vec<E4>> = None;
    for launch in 1..=3 {
        memory_copy_async(
            &mut contributions_device[..],
            &poison_values[..],
            context.get_exec_stream(),
        )
        .expect("fresh contribution poison H2D");
        setup
            .upload_constant_banks(context)
            .expect("upload R0 VM coefficient/derived banks before release");
        launch_bwd_vm_release(&setup.desc, case.budget_cells as u32, context)
            .expect("real R0 release launch");
        let got = download_e4(&contributions_device, context);
        assert_e4_bits(
            &format!("c{} release {launch} contributions", case.budget_cells),
            &got,
            &expected,
        );
        if let Some(first) = &first_release {
            assert_e4_bits(
                &format!("c{} release {launch} determinism", case.budget_cells),
                &got,
                first,
            );
        } else {
            first_release = Some(got);
        }
    }

    let temp_bytes = get_reduce_temp_storage_bytes::<E4>(ReduceOperation::Sum, rows as i32)
        .expect("compact two-half reduction temp size");
    let mut reduction_temp = context
        .alloc(temp_bytes, AllocationPlacement::Top)
        .expect("compact two-half reduction temp");
    let mut reduction_output = upload(&[E4::ZERO; 2], context);
    // SAFETY: this is one temporary mutable view over the complete live temp
    // allocation, used serially by the incumbent pair of CUB reductions.
    let reduction_temp_slice = unsafe {
        DeviceSlice::from_raw_parts_mut(reduction_temp.as_mut_ptr(), reduction_temp.len())
    };
    let q0_half = DeviceVectorChunk::new(&contributions_device, 0, rows);
    reduce(
        ReduceOperation::Sum,
        reduction_temp_slice,
        &q0_half,
        &mut reduction_output[0],
        context.get_exec_stream(),
    )
    .expect("compact q0 reduction");
    let q2_half = DeviceVectorChunk::new(&contributions_device, rows, rows);
    reduce(
        ReduceOperation::Sum,
        reduction_temp_slice,
        &q2_half,
        &mut reduction_output[1],
        context.get_exec_stream(),
    )
    .expect("compact q2 reduction");
    let reduced = download_e4(&reduction_output, context);
    let expected_q0 = sum_half(&expected[..rows]);
    let expected_q2 = sum_half(&expected[rows..]);
    assert_e4_bits(
        &format!("c{} compact reductions", case.budget_cells),
        &reduced,
        &[expected_q0, expected_q2],
    );
    assert_recovery_and_production_coefficients(
        case.budget_cells,
        0,
        reduced[0],
        reduced[1],
        claim_point[0],
        context,
    );
    eprintln!(
        "[bwd-vm-r0] c{} phase=complete rows={rows}",
        case.budget_cells
    );
}

#[test]
#[ignore] // GPU; compile unlocked, run the exact built executable under with_gpu_lock.sh.
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_vm_add_sub_l0_r0_parity() {
    let cases = [2usize, 5, 16].map(|budget| load_add_sub_l0_case(BwdRegime::R0, budget));
    assert!(cases
        .iter()
        .all(|case| case.trace_len == cases[0].trace_len));
    let fixture = CircuitFixture::build("add_sub_lui_auipc_mop");
    assert_eq!(fixture.trace_len, cases[0].trace_len);
    eprintln!(
        "[bwd-vm-r0] phase=snapshot trace_len={} source_columns={}",
        fixture.trace_len,
        cases
            .iter()
            .flat_map(r0_source_coordinates)
            .map(|(_, _, place)| place)
            .collect::<HashSet<_>>()
            .len()
    );
    let columns = snapshot_r0_columns(&fixture, &cases, fixture.trace_len);
    let oracle = r0_oracle_resolvers(&fixture, &cases, columns);
    let folding_steps = fixture.trace_len.trailing_zeros() as usize;
    let mut claim_point = Vec::with_capacity(folding_steps);
    claim_point.push(e4(0x4100));
    claim_point.extend((1..folding_steps).map(|index| e4(0x4200 + index as u32)));
    assert!(claim_point.iter().all(|value| *value != E4::ZERO));
    let round_challenges = (0..folding_steps)
        .map(|round| e4(0x4300 + round as u32))
        .collect::<Vec<_>>();
    assert!(round_challenges.iter().all(|value| *value != E4::ZERO));

    for case in &cases {
        run_add_sub_r0_budget(&fixture, case, &oracle, &claim_point, &round_challenges);
    }
}

#[test]
#[ignore] // GPU; bounded one-block diagnostic for the full all-round gate.
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_vm_add_sub_l0_ext_round_zero_single_block_parity() {
    const ROWS: usize = 16;
    const SOURCE_ELEMENTS: usize = 2 * ROWS;

    let r0_case = load_add_sub_l0_case(BwdRegime::R0, 2);
    let ext_case = load_add_sub_l0_case(BwdRegime::Ext, 2);
    eprintln!(
        "[bwd-vm-tiny] compiled R0 instr={} lanes={} windows={} Ext instr={} lanes={} windows={}",
        r0_case.compiled.compiled.program.instrs.len(),
        r0_case.compiled.encoded.len(),
        r0_case.compiled.compiled.source_windows.len(),
        ext_case.compiled.compiled.program.instrs.len(),
        ext_case.compiled.encoded.len(),
        ext_case.compiled.compiled.source_windows.len(),
    );
    let materialization = artifact_static_materialization(
        &ext_case.canonical,
        &ext_case.distilled,
        ext_case.trace_len,
        ext_case.budget_cells,
    )
    .expect("artifact-certified tiny Ext bindings");

    let fixture = CircuitFixture::build("add_sub_lui_auipc_mop");
    let columns = snapshot_r0_columns(&fixture, std::slice::from_ref(&r0_case), SOURCE_ELEMENTS);
    let oracle = r0_oracle_resolvers(&fixture, std::slice::from_ref(&r0_case), columns);
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .build()
        .expect("single-thread tiny oracle pool");
    let claim_point = (0..5)
        .map(|index| e4(0x5100 + index as u32))
        .collect::<Vec<_>>();
    let round_challenges = (0..24)
        .map(|round| e4(0x5300 + round as u32))
        .collect::<Vec<_>>();
    let eq_sizes = make_eq_sizes(claim_point.len() - 1);
    let (cpu_high, cpu_low) = cpu_factored_eq(&claim_point[1..]);
    let claim_point_device = upload(&claim_point, fixture.context());
    let mut eq_low_device = upload(&vec![E4::ZERO; GKR_EQ_GROUP_TABLE_LEN], fixture.context());
    launch_build_eq_high_and_low_groups_from_point::<E4>(
        claim_point_device.as_ptr(),
        1,
        claim_point.len() - 1,
        get_eq_high_constant_device_ptr(),
        eq_low_device.as_mut_ptr(),
        fixture.context(),
    )
    .expect("build tiny Ext factored eq");
    let expected = all_round_expected_contributions(
        &ext_case,
        &oracle,
        0,
        ROWS,
        &round_challenges,
        &cpu_high,
        &cpu_low,
        &eq_sizes,
        &pool,
        23,
        &[],
        &HashMap::new(),
        &[],
        &HashMap::new(),
    );

    let read_descriptors = ext_read_descriptors(&ext_case);
    let virtual_descriptors = ext_virtual_descriptors(&ext_case);
    let desc_columns = read_descriptors
        .iter()
        .enumerate()
        .map(|(column, (desc, _))| (*desc, column))
        .collect::<HashMap<_, _>>();
    let sentinel = e4(0x7d10);
    let original_matrix = upload_ext_original_matrix(
        &read_descriptors,
        &desc_columns,
        &oracle,
        SOURCE_ELEMENTS,
        sentinel,
        fixture.context(),
    );
    let mut publication_matrices = [
        GuardedPublicationMatrix::new(
            read_descriptors.len(),
            SOURCE_ELEMENTS,
            sentinel,
            fixture.context(),
        ),
        GuardedPublicationMatrix::new(
            read_descriptors.len(),
            SOURCE_ELEMENTS,
            sentinel,
            fixture.context(),
        ),
    ];
    let mut virtual_publications = [
        GuardedPublicationMatrix::new(4, SOURCE_ELEMENTS, sentinel, fixture.context()),
        GuardedPublicationMatrix::new(4, SOURCE_ELEMENTS, sentinel, fixture.context()),
    ];
    let current_host = build_publication_oracle(
        &read_descriptors,
        &materialization,
        0,
        ROWS,
        &oracle,
        &round_challenges,
        &HashMap::new(),
        &pool,
        23,
    );
    run_all_budget_coordinate(
        &fixture,
        std::slice::from_ref(&ext_case),
        &expected,
        0,
        23,
        claim_point[0],
        &round_challenges,
        &eq_low_device,
        eq_sizes,
        Some(&materialization),
        &desc_columns,
        Some(&original_matrix),
        Some(&mut publication_matrices),
        &HashMap::new(),
        &current_host,
        &virtual_descriptors,
        Some(&mut virtual_publications),
        &HashMap::new(),
        &HashMap::new(),
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_vm_add_sub_l0_all_budgets_all_rounds_parity() {
    let started = Instant::now();
    let r0_cases = (2usize..=16)
        .map(|budget| load_add_sub_l0_case(BwdRegime::R0, budget))
        .collect::<Vec<_>>();
    let ext_cases = (2usize..=16)
        .map(|budget| load_add_sub_l0_case(BwdRegime::Ext, budget))
        .collect::<Vec<_>>();
    let trace_len = r0_cases[0].trace_len;
    assert!(
        r0_cases
            .iter()
            .chain(&ext_cases)
            .all(|case| case.trace_len == trace_len),
        "all artifact cases must share one trace domain"
    );
    assert_semantic_identity(&r0_cases[0], &r0_cases);
    assert_semantic_identity(&ext_cases[0], &ext_cases);

    let materializations = ext_cases
        .iter()
        .map(|case| {
            artifact_static_materialization(
                &case.canonical,
                &case.distilled,
                case.trace_len,
                case.budget_cells,
            )
            .unwrap_or_else(|error| {
                panic!(
                    "artifact-certified Ext source-round bindings c{}: {error:?}",
                    case.budget_cells
                )
            })
        })
        .collect::<Vec<_>>();
    for (case, materialization) in ext_cases.iter().zip(&materializations) {
        assert_eq!(
            materialization, &materializations[0],
            "c{} static publication policy identity before cross-budget reuse",
            case.budget_cells
        );
    }
    let materialization = &materializations[0];
    assert!(
        (0..r0_cases[0].distilled.specials.len()).any(|desc| matches!(
            r0_cases[0].distilled.specials.get(desc as u16),
            Some(BwdSpecial::VirtualSetup { .. })
        ))
    );

    let fixture = CircuitFixture::build("add_sub_lui_auipc_mop");
    assert_eq!(fixture.trace_len, trace_len);
    eprintln!(
        "[bwd-vm-parity] snapshot trace_len={trace_len} source_columns={} elapsed={:.2}s",
        r0_cases
            .iter()
            .flat_map(r0_source_coordinates)
            .map(|(_, _, place)| place)
            .collect::<HashSet<_>>()
            .len(),
        started.elapsed().as_secs_f64()
    );
    let columns = snapshot_r0_columns(&fixture, &r0_cases, fixture.trace_len);
    let oracle = r0_oracle_resolvers(&fixture, &r0_cases, columns);
    let physical_cores = available_physical_cores();
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(physical_cores)
        .thread_name(|index| format!("bwd-vm-oracle-{index}"))
        .build()
        .expect("bounded backward VM oracle pool");
    eprintln!("[bwd-vm-parity] rayon physical_cores={physical_cores}");

    let folding_steps = trace_len.trailing_zeros() as usize;
    let last_round = folding_steps - 1;
    let claim_point = (0..folding_steps)
        .map(|index| e4(0x4100 + index as u32))
        .collect::<Vec<_>>();
    let round_challenges = (0..folding_steps)
        .map(|round| e4(0x4300 + round as u32))
        .collect::<Vec<_>>();
    assert!(claim_point
        .iter()
        .chain(&round_challenges)
        .all(|value| *value != E4::ZERO));
    let claim_point_device = upload(&claim_point, fixture.context());

    // R0 is a separate typed regime. Its distilled semantics are identical
    // across c2..c16 (asserted above), so one ordered CPU row oracle is reused.
    let r0_reference = r0_cases
        .iter()
        .min_by_key(|case| case.compiled.encoded.len())
        .expect("R0 artifact cases");
    let r0_rows = trace_len / 2;
    let r0_eq_sizes = make_eq_sizes(folding_steps - 1);
    let (r0_high, r0_low) = cpu_factored_eq(&claim_point[1..]);
    let mut r0_eq_low_device = upload(&vec![E4::ZERO; GKR_EQ_GROUP_TABLE_LEN], fixture.context());
    launch_build_eq_high_and_low_groups_from_point::<E4>(
        claim_point_device.as_ptr(),
        1,
        folding_steps - 1,
        get_eq_high_constant_device_ptr(),
        r0_eq_low_device.as_mut_ptr(),
        fixture.context(),
    )
    .expect("build R0 factored eq");
    let r0_expected = all_round_expected_contributions(
        r0_reference,
        &oracle,
        0,
        r0_rows,
        &round_challenges,
        &r0_high,
        &r0_low,
        &r0_eq_sizes,
        &pool,
        last_round,
        &[],
        &HashMap::new(),
        &[],
        &HashMap::new(),
    );
    run_all_budget_coordinate(
        &fixture,
        &r0_cases,
        &r0_expected,
        0,
        last_round,
        claim_point[0],
        &round_challenges,
        &r0_eq_low_device,
        r0_eq_sizes,
        None,
        &HashMap::new(),
        None,
        None,
        &HashMap::new(),
        &HashMap::new(),
        &[],
        None,
        &HashMap::new(),
        &HashMap::new(),
    );
    drop(r0_expected);
    drop(r0_eq_low_device);

    // Ext source operands consume E4 originals even when their ReadPlace is a
    // base column. Lift every distinct original once, then keep exactly two
    // maximum-sized publication matrices for the literal static schedule.
    let read_descriptors = ext_read_descriptors(&ext_cases[0]);
    let virtual_descriptors = ext_virtual_descriptors(&ext_cases[0]);
    let desc_columns = read_descriptors
        .iter()
        .enumerate()
        .map(|(column, (desc, _))| (*desc, column))
        .collect::<HashMap<_, _>>();
    assert_eq!(desc_columns.len(), read_descriptors.len());
    let publication_sentinel = e4(0x7d00);
    let original_matrix = upload_ext_original_matrix(
        &read_descriptors,
        &desc_columns,
        &oracle,
        trace_len,
        publication_sentinel,
        fixture.context(),
    );
    let mut publication_matrices = [
        GuardedPublicationMatrix::new(
            read_descriptors.len(),
            trace_len,
            publication_sentinel,
            fixture.context(),
        ),
        GuardedPublicationMatrix::new(
            read_descriptors.len(),
            trace_len,
            publication_sentinel,
            fixture.context(),
        ),
    ];
    let virtual_max_elements = trace_len >> VIRTUAL_SETUP_MATERIALIZE_DEPTH;
    assert_eq!(
        virtual_max_elements,
        2 * (trace_len >> (VIRTUAL_SETUP_MATERIALIZE_DEPTH as usize + 1)),
        "depth-three publication is the maximum virtual endpoint domain"
    );
    let mut virtual_publications = [
        GuardedPublicationMatrix::new(
            4,
            virtual_max_elements,
            publication_sentinel,
            fixture.context(),
        ),
        GuardedPublicationMatrix::new(
            4,
            virtual_max_elements,
            publication_sentinel,
            fixture.context(),
        ),
    ];
    let matrix_bytes = original_matrix.device.len() * size_of::<E4>();
    eprintln!(
        "[bwd-vm-parity] ext_columns={} matrix_bytes={} lifted_plus_pingpong_bytes={} elapsed={:.2}s",
        read_descriptors.len(),
        matrix_bytes,
        matrix_bytes * 3,
        started.elapsed().as_secs_f64()
    );

    let ext_reference = ext_cases
        .iter()
        .min_by_key(|case| case.compiled.encoded.len())
        .expect("Ext artifact cases");
    let mut previous_host = HashMap::<u16, PublishedHostColumn>::new();
    let mut previous_device = HashMap::<u16, PublishedDeviceColumn>::new();
    let mut previous_virtual_host = HashMap::<u16, PublishedHostColumn>::new();
    let mut previous_virtual_device = HashMap::<u16, PublishedDeviceColumn>::new();
    for round in 0..=last_round as u8 {
        for &(desc, _) in &read_descriptors {
            assert!(
                materialization.binding(desc, round).is_some(),
                "Ext desc {desc} round {round} must have a literal static binding"
            );
        }
        let rows = trace_len >> (round as usize + 1);
        let remaining_point = &claim_point[round as usize + 1..];
        assert_eq!(rows, 1usize << remaining_point.len());
        let eq_sizes = make_eq_sizes(remaining_point.len());
        let (cpu_high, cpu_low) = cpu_factored_eq(remaining_point);
        let mut eq_low_host = vec![E4::ZERO; GKR_EQ_GROUP_TABLE_LEN];
        eq_low_host[0] = E4::ONE;
        let mut eq_low_device = upload(&eq_low_host, fixture.context());
        launch_build_eq_high_and_low_groups_from_point::<E4>(
            claim_point_device.as_ptr(),
            round as usize + 1,
            remaining_point.len(),
            get_eq_high_constant_device_ptr(),
            eq_low_device.as_mut_ptr(),
            fixture.context(),
        )
        .expect("build Ext factored eq");
        let current_virtual = build_virtual_publication_oracle(
            &virtual_descriptors,
            round,
            rows,
            &oracle,
            &round_challenges,
            &previous_virtual_host,
            &pool,
            last_round,
        );
        let current_host = build_publication_oracle(
            &read_descriptors,
            materialization,
            round,
            rows,
            &oracle,
            &round_challenges,
            &previous_host,
            &pool,
            last_round,
        );
        if round > VIRTUAL_SETUP_MATERIALIZE_DEPTH {
            assert_eq!(
                current_host.len(),
                read_descriptors.len(),
                "later contribution oracles require every current Read publication"
            );
        }
        let no_read_publications = HashMap::new();
        let oracle_read_publications = if round > VIRTUAL_SETUP_MATERIALIZE_DEPTH {
            &current_host
        } else {
            &no_read_publications
        };
        let expected = all_round_expected_contributions(
            ext_reference,
            &oracle,
            round,
            rows,
            &round_challenges,
            &cpu_high,
            &cpu_low,
            &eq_sizes,
            &pool,
            last_round,
            &read_descriptors,
            oracle_read_publications,
            &virtual_descriptors,
            &current_virtual,
        );
        run_all_budget_coordinate(
            &fixture,
            &ext_cases,
            &expected,
            round,
            last_round,
            claim_point[round as usize],
            &round_challenges,
            &eq_low_device,
            eq_sizes,
            Some(materialization),
            &desc_columns,
            Some(&original_matrix),
            Some(&mut publication_matrices),
            &previous_device,
            &current_host,
            &virtual_descriptors,
            Some(&mut virtual_publications),
            &previous_virtual_device,
            &current_virtual,
        );

        // Static `store_for_next_round` is the sole retention authority.
        // Drop every older host array and name only this round's publications
        // when the next actual round explicitly binds them as Materialized.
        if round as usize == last_round {
            previous_host.clear();
            previous_device.clear();
        } else {
            for &desc in current_host.keys() {
                assert_eq!(
                    materialization
                        .binding(desc, round + 1)
                        .map(|binding| binding.state),
                    Some(FoldState::Materialized),
                    "stored desc {desc} must be explicitly named next round"
                );
            }
            previous_device = current_host
                .keys()
                .map(|&desc| {
                    (
                        desc,
                        PublishedDeviceColumn {
                            matrix: (round as usize) & 1,
                            depth: round,
                        },
                    )
                })
                .collect();
            previous_host = current_host;
        }
        if round as usize == last_round {
            previous_virtual_host.clear();
            previous_virtual_device.clear();
        } else if virtual_round_binding(round).store_for_next_round {
            assert_eq!(
                current_virtual.len(),
                virtual_descriptors.len(),
                "all virtual descriptors publish together"
            );
            previous_virtual_device = current_virtual
                .keys()
                .map(|&desc| {
                    (
                        desc,
                        PublishedDeviceColumn {
                            matrix: (round as usize) & 1,
                            depth: round,
                        },
                    )
                })
                .collect();
            previous_virtual_host = current_virtual;
        }
        drop(expected);
        drop(eq_low_device);
        eprintln!(
            "[bwd-vm-parity] semantic round {round}/{last_round} complete elapsed={:.2}s",
            started.elapsed().as_secs_f64()
        );
    }

    eprintln!(
        "[bwd-vm-parity] complete budgets=15 r0=1 ext_rounds={} elapsed={:.2}s",
        last_round + 1,
        started.elapsed().as_secs_f64()
    );
}

fn evaluate_incumbent_recipes(
    recipes: &[CoefficientRecipe<E4>],
    batch_base: E4,
    lookup_multiplicative: E4,
    lookup_additive: E4,
    external_challenges: &[E4],
) -> Vec<E4> {
    recipes
        .iter()
        .map(|recipe| {
            let immediate = if recipe.negate {
                recipe.immediate_recipe.negated()
            } else {
                recipe.immediate_recipe.clone()
            };
            let mut coefficient = batch_base.pow(recipe.batch_power);
            coefficient.mul_assign(&immediate.evaluate(external_challenges));
            for group in &recipe.prefactors {
                let mut group_sum = E4::ZERO;
                for term in group {
                    let challenge = match term.source {
                        GpuGKRMainLayerDeferredChallengeSource::LookupMultiplicative => {
                            lookup_multiplicative
                        }
                        GpuGKRMainLayerDeferredChallengeSource::LookupAdditive => lookup_additive,
                    };
                    let mut value = challenge.pow(term.power);
                    value.mul_assign_by_base(&term.coeff);
                    group_sum.add_assign(&value);
                }
                coefficient.mul_assign(&group_sum);
            }
            coefficient
        })
        .collect()
}

fn incumbent_launch_sizes(
    plan: &GpuGKRMainLayerSumcheckLayerPlan<E4>,
    step: usize,
    acc_size: usize,
) -> (u32, u32) {
    let continuation = plan
        .flat_continuation_plan
        .as_ref()
        .expect("add/sub incumbent continuation plan");
    let mut sizes = None;
    for assignment in &continuation.source_assignments {
        if step < 3 && !assignment.is_ext {
            continue;
        }
        let source = match step {
            1 => plan.kernel_plans[assignment.gate_idx]
                .round1_prepared
                .extension_field_inputs
                .get(assignment.input_idx),
            2 => plan.kernel_plans[assignment.gate_idx]
                .round2_prepared
                .extension_field_inputs
                .get(assignment.input_idx),
            step => {
                let prepared = plan.kernel_plans[assignment.gate_idx]
                    .round3_and_beyond_prepared
                    .iter()
                    .find(|prepared| prepared.step == step)
                    .unwrap_or_else(|| panic!("missing incumbent prepared round {step}"));
                if assignment.is_ext {
                    prepared
                        .prepared
                        .extension_field_inputs
                        .get(assignment.input_idx)
                } else {
                    prepared
                        .prepared
                        .base_field_inputs
                        .get(assignment.input_idx)
                }
            }
        };
        let Some(source) = source else {
            panic!("incumbent source assignment out of bounds at round {step}")
        };
        if source.this_layer_size == 0 || source.next_layer_size == 0 {
            continue;
        }
        let candidate = (source.this_layer_size as u32, source.next_layer_size as u32);
        if let Some(previous) = sizes {
            assert_eq!(
                candidate, previous,
                "mixed incumbent source geometry at round {step}"
            );
        } else {
            sizes = Some(candidate);
        }
    }
    sizes.unwrap_or((acc_size as u32, acc_size as u32))
}

fn poison_e4_ptr(
    ptr: *mut E4,
    len: usize,
    value: E4,
    context: &ProverContext,
) -> era_cudart::result::CudaResult<()> {
    // SAFETY: every caller supplies a live device allocation/symbol span of
    // exactly `len` E4 values and serializes access on `exec_stream`.
    let slice = unsafe { DeviceSlice::from_raw_parts_mut(ptr, len) };
    set_by_val(value, slice, context.get_exec_stream())
}

fn upload_main_layer_challenges(values: &[E4], context: &ProverContext) {
    // SAFETY: the add/sub trace has fewer entries than the statically guarded
    // main-layer claim-point symbol capacity; the production plan asserted the
    // same bound while it was prepared.
    let dst = unsafe {
        DeviceSlice::from_raw_parts_mut(
            compact::get_main_layer_claim_point_device_ptr(),
            values.len(),
        )
    };
    memory_copy_async(dst, values, context.get_exec_stream())
        .expect("upload incumbent folding challenges");
}

fn time_incumbent_add_sub_rounds(selection: SweepSelection) -> HashMap<u8, TimingSummary> {
    let BasicUnrolledAsyncBackwardFixture {
        context,
        compiled_circuit,
        external_challenges,
        mut gpu_backward_state,
        batching_challenge,
        lookup_multiplicative_part,
        lookup_additive_part,
        ..
    } = prepare_basic_unrolled_async_backward_fixture(8);

    while let Some(plan) = gpu_backward_state
        .prepare_next_layer_static(&context)
        .expect("prepare incumbent dimension-reducing layer")
    {
        drop(plan);
    }
    let mut main_state = gpu_backward_state.into_main_layer_backward_state(
        compiled_circuit,
        external_challenges.clone(),
        lookup_multiplicative_part,
        lookup_additive_part,
        false,
    );
    let mut plan = loop {
        let Some(plan) = main_state
            .prepare_next_layer(batching_challenge, &context)
            .expect("prepare incumbent main layer")
        else {
            panic!("missing incumbent add/sub layer 0")
        };
        if plan.layer_idx == 0 {
            break plan;
        }
        drop(plan);
    };

    assert!(
        plan.flat_use_constant,
        "add/sub R0 must use constant coefficients"
    );
    assert!(
        plan.flat_cont_use_constant,
        "add/sub continuation must use constant coefficients"
    );
    assert!(plan.flat_coeff_device_buf.is_none());
    assert!(plan.flat_cont_coeff_device_buf.is_none());
    assert!(plan.flat_round1_terms_device.is_none());
    assert!(plan.flat_round2_terms_device.is_none());
    assert!(plan.flat_continuation_terms_device.is_empty());

    let mut external_values = external_challenges
        .permutation_argument_linearization_challenges
        .to_vec();
    external_values.push(external_challenges.permutation_argument_additive_part);
    let round0_coefficients = evaluate_incumbent_recipes(
        &plan
            .flat_round0_template_compact
            .as_ref()
            .expect("incumbent round0 descriptor")
            .recipes,
        batching_challenge,
        lookup_multiplicative_part,
        lookup_additive_part,
        &external_values,
    );
    let continuation_coefficients = evaluate_incumbent_recipes(
        &plan
            .flat_continuation_plan
            .as_ref()
            .expect("incumbent continuation descriptor")
            .recipes,
        batching_challenge,
        lookup_multiplicative_part,
        lookup_additive_part,
        &external_values,
    );

    let folding_steps = plan.folding_steps;
    let last_round = folding_steps - 1;
    let point = (0..folding_steps)
        .map(|index| e4(0x4100 + index as u32))
        .collect::<Vec<_>>();
    upload_main_layer_challenges(&point, &context);
    let point_device = upload(&point, &context);
    let claim_point_symbol = compact::get_main_layer_claim_point_device_ptr() as *const E4;
    let output_ptr = plan.round_scratch.accumulator.as_mut_ptr();
    let mut timings = HashMap::new();

    for round in 0..=last_round {
        if !selection.needs_incumbent_round(round as u8) {
            continue;
        }
        let rows = plan.trace_len >> (round + 1);
        let remaining = folding_steps - round - 1;
        let eq_sizes = make_eq_sizes(remaining);
        let mut eq_low = upload(&vec![E4::ZERO; GKR_EQ_GROUP_TABLE_LEN], &context);
        launch_build_eq_high_and_low_groups_from_point::<E4>(
            point_device.as_ptr(),
            round + 1,
            remaining,
            get_eq_high_constant_device_ptr(),
            eq_low.as_mut_ptr(),
            &context,
        )
        .expect("build incumbent factored eq");
        let coefficients = if round == 0 {
            &round0_coefficients
        } else {
            &continuation_coefficients
        };
        upload_incumbent_coefficients(coefficients, &context)
            .expect("upload incumbent host-evaluated coefficients");
        let (fold_stride, next_layer_size) = if round == 0 {
            (rows as u32, rows as u32)
        } else {
            incumbent_launch_sizes(&plan, round, rows)
        };
        let launch = || match round {
            0 => compact::launch_main_round0_constant::<E4>(
                &plan
                    .flat_round0_template_compact
                    .as_ref()
                    .expect("incumbent round0 descriptor")
                    .static_desc,
                eq_low.as_ptr(),
                &eq_sizes,
                output_ptr,
                rows as u32,
                &context,
            ),
            1 => compact::launch_main_round1_unified::<E4>(
                plan.flat_round1_unified_desc_compact
                    .as_ref()
                    .expect("incumbent round1 descriptor"),
                ptr::null(),
                fold_stride,
                next_layer_size,
                eq_low.as_ptr(),
                &eq_sizes,
                output_ptr,
                rows as u32,
                &context,
            ),
            2 => compact::launch_main_round2_unified::<E4>(
                plan.flat_round2_unified_desc_compact
                    .as_ref()
                    .expect("incumbent round2 descriptor"),
                // The direct compact launcher includes
                // `launch_round2_challenges_prelude` on the same stream. Keep
                // that cost in this incumbent sequence, rather than timing
                // only the dependent evaluator kernel.
                claim_point_symbol,
                fold_stride,
                next_layer_size,
                eq_low.as_ptr(),
                &eq_sizes,
                output_ptr,
                rows as u32,
                &context,
            ),
            step => {
                // The prepared incumbent invokes every add/sub continuation
                // round in monomial form; only a prepared final explicit round
                // could set this flag. Keep this pin adjacent to the direct
                // compact launcher so a production-plan change fails setup.
                const PREPARED_FINAL_EXPLICIT_FORM: bool = false;
                let final_round = step == last_round;
                let explicit_form = final_round && PREPARED_FINAL_EXPLICIT_FORM;
                assert!(
                    !explicit_form || final_round,
                    "only the prepared final round may use the explicit compact variant"
                );
                let desc = &plan
                    .flat_continuation_unified_descs_compact
                    .iter()
                    .find(|(candidate, _)| *candidate == step)
                    .unwrap_or_else(|| panic!("missing incumbent round {step} descriptor"))
                    .1;
                compact::launch_main_round3_unified::<E4>(
                    desc,
                    ptr::null(),
                    fold_stride,
                    next_layer_size,
                    (step - 1) as u32,
                    eq_low.as_ptr(),
                    &eq_sizes,
                    output_ptr,
                    rows as u32,
                    explicit_form,
                    &context,
                )
            }
        };

        let preflight_poison = e4(0xa100 + round as u32);
        poison_e4_ptr(output_ptr, 2 * rows, preflight_poison, &context)
            .expect("poison incumbent preflight output");
        launch().expect("incumbent correctness launch");
        context
            .get_exec_stream()
            .synchronize()
            .expect("incumbent correctness synchronization");
        assert!(
            download_e4_ptr(output_ptr, 2 * rows, &context)
                .iter()
                .any(|value| *value != preflight_poison),
            "incumbent round {round} correctness launch left all outputs poisoned"
        );
        let timing = time_cuda_launches(
            context.get_exec_stream(),
            WARMUP_ITERS,
            TIMING_ITERS,
            || poison_e4_ptr(output_ptr, 2 * rows, e4(0xa200 + round as u32), &context),
            launch,
        )
        .expect("time incumbent launch sequence");
        assert!(timings.insert(round as u8, timing).is_none());
    }
    timings
}

fn predicted_source_bytes(desc: &BwdVmDesc) -> u128 {
    let program = decode(&desc.program[..desc.program_lanes as usize])
        .expect("lowered timing program must decode");
    let mut bytes_per_row = 0u128;
    let mut visit = |operand: &OperandLine| {
        let OperandLine::Source { window, column, .. } = operand else {
            return;
        };
        let source = desc.source_windows[*window as usize];
        let origin_bytes = match (source.source_kind, source.backing_depth) {
            (BWD_VM_SOURCE_READ_BASE, _) => size_of::<BF>(),
            (BWD_VM_SOURCE_READ_EXT, _) => size_of::<E4>(),
            (BWD_VM_SOURCE_VIRTUAL, 0) => 0,
            (BWD_VM_SOURCE_VIRTUAL, _) => size_of::<E4>(),
            (kind, _) => panic!("invalid timing source kind {kind}"),
        };
        assert!((*column as usize) < 64, "encoded source column bound");
        let delta = source
            .target_depth
            .checked_sub(source.backing_depth)
            .expect("fold target cannot precede backing");
        bytes_per_row += 3u128 * (1u128 << delta) * origin_bytes as u128;
    };
    for instr in &program.instrs {
        match instr {
            Instr::Mov { src: Some(src), .. } => visit(src),
            Instr::Mov { src: None, .. } => {}
            Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
                for operand in operands {
                    visit(operand);
                }
            }
            Instr::Fma { pairs, .. } => {
                for (lhs, rhs) in pairs {
                    visit(lhs);
                    visit(rhs);
                }
            }
        }
    }
    bytes_per_row * u128::from(desc.logical_rows)
}

fn incumbent_sequence(round: u8) -> &'static str {
    if round == 2 {
        "round2_challenges_prelude+launch_main_round2_unified"
    } else {
        "compact evaluator launcher"
    }
}

fn time_vm_setup(
    setup: &super::lower::BwdVmSetup,
    budget_cells: usize,
    contribution_ptr: *mut E4,
    rows: usize,
    expected_prefix: Option<&[E4]>,
    context: &ProverContext,
    mut poison_extra_outputs: impl FnMut(usize) -> era_cudart::result::CudaResult<()>,
) -> TimingSummary {
    assert_vm_setup_parity(
        setup,
        budget_cells,
        contribution_ptr,
        expected_prefix,
        context,
        &mut poison_extra_outputs,
    );
    let poison = e4(0xb000 + budget_cells as u32 + setup.desc.logical_rows.trailing_zeros());
    time_cuda_launches(
        context.get_exec_stream(),
        WARMUP_ITERS,
        TIMING_ITERS,
        || {
            poison_e4_ptr(contribution_ptr, 2 * rows, poison, context)?;
            poison_extra_outputs(rows)
        },
        || launch_bwd_vm_release(&setup.desc, budget_cells as u32, context),
    )
    .expect("time VM release launch")
}

/// Exact bounded-domain parity for the real lowered descriptor. This is not a
/// sparse output probe: both complete contribution halves for the first
/// `expected_prefix.len() / 2` rows are compared against the independent CPU
/// interpreter through fold depth 3. Later rounds validate and release the
/// actual artifact-resolved path twice, comparing the complete bounded halves
/// bit-for-bit without recomputing original cones on the CPU. The full-domain
/// Task 7 gate remains the separate exhaustive proof.
fn assert_vm_setup_parity(
    setup: &super::lower::BwdVmSetup,
    budget_cells: usize,
    contribution_ptr: *mut E4,
    expected_prefix: Option<&[E4]>,
    context: &ProverContext,
    poison_extra_outputs: &mut impl FnMut(usize) -> era_cudart::result::CudaResult<()>,
) {
    let preflight_rows = expected_prefix.map_or_else(
        || (setup.desc.logical_rows as usize).min(PREFLIGHT_ROWS),
        |expected| {
            assert!(
                expected.len().is_multiple_of(2),
                "preflight needs two complete contribution halves"
            );
            expected.len() / 2
        },
    );
    assert!(preflight_rows > 0 && preflight_rows <= setup.desc.logical_rows as usize);
    let mut preflight_desc = setup.desc;
    preflight_desc.logical_rows = preflight_rows as u32;
    let mut error = upload(&[0u32], context);
    let poison = e4(0xb000 + budget_cells as u32 + setup.desc.logical_rows.trailing_zeros());
    poison_e4_ptr(contribution_ptr, 2 * preflight_rows, poison, context)
        .expect("poison VM preflight contributions");
    poison_extra_outputs(preflight_rows).expect("poison VM preflight publications");
    setup
        .upload_constant_banks(context)
        .expect("upload VM timing constant banks");
    launch_bwd_vm_validate(
        &preflight_desc,
        budget_cells as u32,
        error.as_mut_ptr(),
        ptr::null_mut(),
        context,
    )
    .expect("VM timing validation launch");
    assert_eq!(
        download_u32(&error, context),
        [0],
        "c{budget_cells} VM timing setup validation"
    );
    let validate_output = download_e4_ptr(contribution_ptr, 2 * preflight_rows, context);
    match expected_prefix {
        Some(expected) => assert_e4_bits(
            &format!("c{budget_cells} bounded CPU-oracle validation preflight"),
            &validate_output,
            expected,
        ),
        None => assert!(
            validate_output.iter().any(|value| *value != poison),
            "c{budget_cells} actual-path validation left all preflight outputs poisoned"
        ),
    }

    poison_e4_ptr(contribution_ptr, 2 * preflight_rows, poison, context)
        .expect("poison VM correctness contributions");
    poison_extra_outputs(preflight_rows).expect("poison VM correctness publications");
    launch_bwd_vm_release(&preflight_desc, budget_cells as u32, context)
        .expect("VM untimed correctness launch");
    context
        .get_exec_stream()
        .synchronize()
        .expect("VM correctness synchronization");
    let release_output = download_e4_ptr(contribution_ptr, 2 * preflight_rows, context);
    match expected_prefix {
        Some(expected) => assert_e4_bits(
            &format!("c{budget_cells} bounded CPU-oracle release preflight"),
            &release_output,
            expected,
        ),
        None => {
            assert_e4_bits(
                &format!("c{budget_cells} actual-path validate/release preflight"),
                &release_output,
                &validate_output,
            );
            assert!(
                release_output.iter().any(|value| *value != poison),
                "c{budget_cells} actual-path release left all preflight outputs poisoned"
            );
        }
    }
    assert!(
        release_output.iter().any(|value| *value != poison),
        "c{budget_cells} correctness launch left all preflight outputs poisoned"
    );
}

fn vm_occupancy_metadata(budget_cells: usize, max_threads_per_sm: i32) -> (usize, i32, f32) {
    let dynamic_smem_bytes = budget_cells * size_of::<E4>() * BWD_VM_THREADS_PER_BLOCK as usize;
    let active_blocks =
        bwd_vm_release_blocks_per_sm(budget_cells as u32).expect("query backward VM occupancy");
    let occupancy =
        active_blocks as f32 * BWD_VM_THREADS_PER_BLOCK as f32 / max_threads_per_sm as f32;
    (dynamic_smem_bytes, active_blocks, occupancy)
}

#[test]
#[ignore] // GPU timing; compile unlocked and run the exact executable under with_gpu_lock.sh.
#[cfg(not(no_cuda))]
#[serial_test::serial]
fn bwd_vm_add_sub_l0_budget_sweep_report() {
    use era_cudart::device::{device_get_attribute, get_device};
    use era_cudart_sys::CudaDeviceAttr;
    use std::path::Path;

    let selection = SweepSelection::from_env();
    let incumbent = time_incumbent_add_sub_rounds(selection);

    let max_threads_per_sm = device_get_attribute(
        CudaDeviceAttr::MaxThreadsPerMultiProcessor,
        get_device().expect("active CUDA device"),
    )
    .expect("query max threads per SM");
    let r0_cases = (2usize..=16)
        .map(|budget| load_add_sub_l0_case(BwdRegime::R0, budget))
        .collect::<Vec<_>>();
    let ext_cases = (2usize..=16)
        .map(|budget| load_add_sub_l0_case(BwdRegime::Ext, budget))
        .collect::<Vec<_>>();
    assert_semantic_identity(&r0_cases[0], &r0_cases);
    assert_semantic_identity(&ext_cases[0], &ext_cases);
    let trace_len = r0_cases[0].trace_len;
    let folding_steps = trace_len.trailing_zeros() as usize;
    let last_round = folding_steps - 1;
    let claim_point = (0..folding_steps)
        .map(|index| e4(0x4100 + index as u32))
        .collect::<Vec<_>>();
    let round_challenges = (0..folding_steps)
        .map(|round| e4(0x4300 + round as u32))
        .collect::<Vec<_>>();
    let fixture = CircuitFixture::build("add_sub_lui_auipc_mop");
    let context = fixture.context();
    let claim_point_device = upload(&claim_point, context);
    let columns = snapshot_r0_columns(&fixture, &r0_cases, trace_len);
    let oracle = r0_oracle_resolvers(&fixture, &r0_cases, columns);
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(available_physical_cores())
        .thread_name(|index| format!("bwd-vm-timing-oracle-{index}"))
        .build()
        .expect("bounded timing oracle pool");
    let max_rows = trace_len / 2;
    let mut contributions = context
        .alloc::<E4>(2 * max_rows, AllocationPlacement::Top)
        .expect("sweep contribution halves");
    let contribution_ptr = contributions.as_mut_ptr();
    let mut report_rows = Vec::with_capacity(15 * folding_steps);

    let r0_rows = trace_len / 2;
    let r0_eq_sizes = make_eq_sizes(folding_steps - 1);
    let mut r0_eq_low = upload(&vec![E4::ZERO; GKR_EQ_GROUP_TABLE_LEN], context);
    launch_build_eq_high_and_low_groups_from_point::<E4>(
        claim_point_device.as_ptr(),
        1,
        folding_steps - 1,
        get_eq_high_constant_device_ptr(),
        r0_eq_low.as_mut_ptr(),
        context,
    )
    .expect("build R0 sweep factored eq");
    let (r0_high, r0_low) = cpu_factored_eq(&claim_point[1..]);
    let r0_expected_prefix = all_round_expected_contributions(
        &r0_cases[0],
        &oracle,
        0,
        r0_rows.min(PREFLIGHT_ROWS),
        &round_challenges,
        &r0_high,
        &r0_low,
        &r0_eq_sizes,
        &pool,
        last_round,
        &[],
        &HashMap::new(),
        &[],
        &HashMap::new(),
    );
    eprintln!("[bwd-vm-sweep] R0 round 0/{last_round} rows={r0_rows}");
    for case in &r0_cases {
        if !selection.includes("R0", case.budget_cells, 0) {
            continue;
        }
        let sources = resolved_r0_sources(&fixture, case);
        let resolve_source = |address| fixture.resolved_storage_column(address);
        let runtime = BwdVmRoundBinding {
            round: 0,
            rows: r0_rows as u32,
            round_challenges: &round_challenges,
            sources: &sources,
            virtual_sources: &[],
            resolve_source: &resolve_source,
            eq_low: r0_eq_low.as_ptr(),
            eq_sizes: r0_eq_sizes,
            contributions: contribution_ptr,
        };
        let setup = lower_bwd_vm(
            &case.compiled,
            &case.distilled,
            &runtime,
            &|reference| fixture.backward_challenge_value(reference),
            &|recipe| fixture.evaluate_backward_recipe(&case.distilled.layer, recipe),
        )
        .unwrap_or_else(|error| panic!("lower R0 c{} sweep: {error:?}", case.budget_cells));
        let timing = time_vm_setup(
            &setup,
            case.budget_cells,
            contribution_ptr,
            r0_rows,
            Some(&r0_expected_prefix),
            context,
            |_| Ok(()),
        );
        let (dynamic_smem_bytes, active_blocks_per_sm, theoretical_occupancy) =
            vm_occupancy_metadata(case.budget_cells, max_threads_per_sm);
        report_rows.push(SweepRow {
            budget_cells: case.budget_cells,
            regime: "R0",
            round: 0,
            rows: r0_rows,
            dynamic_smem_bytes,
            active_blocks_per_sm,
            theoretical_occupancy,
            program_instructions: setup.desc.n_instr as usize,
            program_lanes: setup.desc.program_lanes as usize,
            predicted_source_bytes: predicted_source_bytes(&setup.desc),
            incumbent_sequence: incumbent_sequence(0),
            vm: timing,
            incumbent: incumbent[&0],
        });
    }

    if !selection.needs_ext_setup() {
        selection.assert_report_rows(&report_rows);
        publish_report(&report_rows, Path::new(SWEEP_LOG_PATH));
        return;
    }

    let materializations = ext_cases
        .iter()
        .map(|case| {
            artifact_static_materialization(
                &case.canonical,
                &case.distilled,
                case.trace_len,
                case.budget_cells,
            )
            .expect("artifact-certified sweep materialization")
        })
        .collect::<Vec<_>>();
    assert!(materializations
        .iter()
        .all(|materialization| materialization == &materializations[0]));
    let materialization = &materializations[0];
    let read_descriptors = ext_read_descriptors(&ext_cases[0]);
    let virtual_descriptors = ext_virtual_descriptors(&ext_cases[0]);
    let desc_columns = read_descriptors
        .iter()
        .enumerate()
        .map(|(column, (desc, _))| (*desc, column))
        .collect::<HashMap<_, _>>();
    let publication_sentinel = e4(0x7d80);
    let original_matrix = upload_ext_original_matrix(
        &read_descriptors,
        &desc_columns,
        &oracle,
        trace_len,
        publication_sentinel,
        context,
    );
    let mut publication_matrices = [
        GuardedPublicationMatrix::new(
            read_descriptors.len(),
            trace_len,
            publication_sentinel,
            context,
        ),
        GuardedPublicationMatrix::new(
            read_descriptors.len(),
            trace_len,
            publication_sentinel,
            context,
        ),
    ];
    let virtual_max_elements = trace_len >> VIRTUAL_SETUP_MATERIALIZE_DEPTH;
    assert_eq!(
        virtual_max_elements,
        2 * (trace_len >> (VIRTUAL_SETUP_MATERIALIZE_DEPTH as usize + 1)),
        "depth-three publication is the maximum virtual endpoint domain"
    );
    let mut virtual_publications = [
        GuardedPublicationMatrix::new(4, virtual_max_elements, publication_sentinel, context),
        GuardedPublicationMatrix::new(4, virtual_max_elements, publication_sentinel, context),
    ];

    // Ext round 0 is the setup predecessor for the first actual Ext timing
    // coordinate (round 1). Run it once, untimed, solely to populate any
    // static `Materialized` bindings named by round 1.
    let prep_case = &ext_cases[0];
    let prep_rows = trace_len / 2;
    let mut prep_eq_low = upload(&vec![E4::ZERO; GKR_EQ_GROUP_TABLE_LEN], context);
    launch_build_eq_high_and_low_groups_from_point::<E4>(
        claim_point_device.as_ptr(),
        1,
        folding_steps - 1,
        get_eq_high_constant_device_ptr(),
        prep_eq_low.as_mut_ptr(),
        context,
    )
    .expect("build Ext predecessor factored eq");
    let (prep_sources, prep_resolve, prep_stored, _) = resolved_ext_round_sources(
        prep_case,
        materialization,
        0,
        &desc_columns,
        &original_matrix,
        &publication_matrices,
        0,
        &HashMap::new(),
    );
    let prep_virtual_sources = resolved_ext_virtual_sources(
        &virtual_descriptors,
        0,
        &virtual_publications,
        0,
        &HashMap::new(),
    );
    let prep_resolver = |address| prep_resolve.get(&address).copied();
    let prep_runtime = BwdVmRoundBinding {
        round: 0,
        rows: prep_rows as u32,
        round_challenges: &round_challenges,
        sources: &prep_sources,
        virtual_sources: &prep_virtual_sources,
        resolve_source: &prep_resolver,
        eq_low: prep_eq_low.as_ptr(),
        eq_sizes: make_eq_sizes(folding_steps - 1),
        contributions: contribution_ptr,
    };
    let prep_setup = lower_bwd_vm(
        &prep_case.compiled,
        &prep_case.distilled,
        &prep_runtime,
        &|reference| fixture.backward_challenge_value(reference),
        &|recipe| fixture.evaluate_backward_recipe(&prep_case.distilled.layer, recipe),
    )
    .expect("lower Ext predecessor");
    let (prep_high, prep_low) = cpu_factored_eq(&claim_point[1..]);
    let prep_expected_prefix = all_round_expected_contributions(
        prep_case,
        &oracle,
        0,
        prep_rows.min(PREFLIGHT_ROWS),
        &round_challenges,
        &prep_high,
        &prep_low,
        &prep_runtime.eq_sizes,
        &pool,
        last_round,
        &read_descriptors,
        &HashMap::new(),
        &virtual_descriptors,
        &HashMap::new(),
    );
    let prep_columns = prep_stored
        .iter()
        .map(|desc| desc_columns[desc])
        .collect::<Vec<_>>();
    assert_vm_setup_parity(
        &prep_setup,
        prep_case.budget_cells,
        contribution_ptr,
        Some(&prep_expected_prefix),
        context,
        &mut |live| {
            publication_matrices[0].poison_columns(prep_columns.iter().copied(), live, context)
        },
    );
    prep_setup
        .upload_constant_banks(context)
        .expect("upload Ext predecessor timing banks");
    launch_bwd_vm_release(&prep_setup.desc, prep_case.budget_cells as u32, context)
        .expect("launch full Ext predecessor publication");
    context
        .get_exec_stream()
        .synchronize()
        .expect("full Ext predecessor synchronization");
    let mut previous_device = prep_stored
        .into_iter()
        .map(|desc| {
            (
                desc,
                PublishedDeviceColumn {
                    matrix: 0,
                    depth: 0,
                },
            )
        })
        .collect::<HashMap<_, _>>();
    let mut previous_virtual_device = HashMap::<u16, PublishedDeviceColumn>::new();

    for round in 1..=last_round as u8 {
        let rows = trace_len >> (round as usize + 1);
        eprintln!("[bwd-vm-sweep] Ext round {round}/{last_round} rows={rows}");
        let remaining = folding_steps - round as usize - 1;
        let eq_sizes = make_eq_sizes(remaining);
        let mut eq_low = upload(&vec![E4::ZERO; GKR_EQ_GROUP_TABLE_LEN], context);
        launch_build_eq_high_and_low_groups_from_point::<E4>(
            claim_point_device.as_ptr(),
            round as usize + 1,
            remaining,
            get_eq_high_constant_device_ptr(),
            eq_low.as_mut_ptr(),
            context,
        )
        .expect("build Ext sweep factored eq");
        let expected_prefix = independent_oracle_rows(round, rows).map(|preflight_rows| {
            let (cpu_high, cpu_low) = cpu_factored_eq(&claim_point[round as usize + 1..]);
            all_round_expected_contributions(
                &ext_cases[0],
                &oracle,
                round,
                preflight_rows,
                &round_challenges,
                &cpu_high,
                &cpu_low,
                &eq_sizes,
                &pool,
                last_round,
                &read_descriptors,
                &HashMap::new(),
                &virtual_descriptors,
                &HashMap::new(),
            )
        });
        if expected_prefix.is_none() {
            eprintln!(
                "[bwd-vm-parity] preflight round {round}/{last_round} actual-path rows={} independent_oracle=skipped",
                rows.min(PREFLIGHT_ROWS)
            );
        }
        let current_matrix = round as usize & 1;
        let virtual_sources = resolved_ext_virtual_sources(
            &virtual_descriptors,
            round,
            &virtual_publications,
            current_matrix,
            &previous_virtual_device,
        );
        let mut stored_reference = None;
        for case in &ext_cases {
            if !selection.includes("Ext", case.budget_cells, round) {
                continue;
            }
            let (sources, resolved, stored, _) = resolved_ext_round_sources(
                case,
                materialization,
                round,
                &desc_columns,
                &original_matrix,
                &publication_matrices,
                current_matrix,
                &previous_device,
            );
            if let Some(reference) = &stored_reference {
                assert_eq!(&stored, reference, "cross-budget publication identity");
            } else {
                stored_reference = Some(stored.clone());
            }
            let resolver = |address| resolved.get(&address).copied();
            let runtime = BwdVmRoundBinding {
                round,
                rows: rows as u32,
                round_challenges: &round_challenges,
                sources: &sources,
                virtual_sources: &virtual_sources,
                resolve_source: &resolver,
                eq_low: eq_low.as_ptr(),
                eq_sizes,
                contributions: contribution_ptr,
            };
            let setup = lower_bwd_vm(
                &case.compiled,
                &case.distilled,
                &runtime,
                &|reference| fixture.backward_challenge_value(reference),
                &|recipe| fixture.evaluate_backward_recipe(&case.distilled.layer, recipe),
            )
            .unwrap_or_else(|error| {
                panic!("lower Ext c{} round {round}: {error:?}", case.budget_cells)
            });
            let columns = stored
                .iter()
                .map(|desc| desc_columns[desc])
                .collect::<Vec<_>>();
            let timing = time_vm_setup(
                &setup,
                case.budget_cells,
                contribution_ptr,
                rows,
                expected_prefix.as_deref(),
                context,
                |live| {
                    publication_matrices[current_matrix].poison_columns(
                        columns.iter().copied(),
                        live,
                        context,
                    )?;
                    if virtual_round_binding(round).store_for_next_round {
                        virtual_publications[current_matrix].poison_columns(
                            0..virtual_descriptors.len(),
                            live,
                            context,
                        )?;
                    }
                    Ok(())
                },
            );
            let (dynamic_smem_bytes, active_blocks_per_sm, theoretical_occupancy) =
                vm_occupancy_metadata(case.budget_cells, max_threads_per_sm);
            report_rows.push(SweepRow {
                budget_cells: case.budget_cells,
                regime: "Ext",
                round,
                rows,
                dynamic_smem_bytes,
                active_blocks_per_sm,
                theoretical_occupancy,
                program_instructions: setup.desc.n_instr as usize,
                program_lanes: setup.desc.program_lanes as usize,
                predicted_source_bytes: predicted_source_bytes(&setup.desc),
                incumbent_sequence: incumbent_sequence(round),
                vm: timing,
                incumbent: incumbent[&round],
            });
        }
        previous_device = stored_reference
            .unwrap_or_else(|| panic!("selected Ext coordinate missing at round {round}"))
            .into_iter()
            .map(|desc| {
                (
                    desc,
                    PublishedDeviceColumn {
                        matrix: current_matrix,
                        depth: round,
                    },
                )
            })
            .collect();
        if virtual_round_binding(round).store_for_next_round {
            previous_virtual_device = virtual_descriptors
                .iter()
                .map(|&(desc, _)| {
                    (
                        desc,
                        PublishedDeviceColumn {
                            matrix: current_matrix,
                            depth: round,
                        },
                    )
                })
                .collect();
        }
        if selection.stops_after_ext_round(round) {
            break;
        }
    }

    selection.assert_report_rows(&report_rows);
    publish_report(&report_rows, Path::new(SWEEP_LOG_PATH));
}
