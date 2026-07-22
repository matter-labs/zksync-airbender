use std::mem::size_of;
use std::ptr;

use era_cudart::memory::memory_copy_async;
use gkr_eval_isa::bwd::interp::{role_combine, sumcheck_fold_point, Role};
use gkr_eval_isa::fwd::encode::encode;
use gkr_eval_isa::fwd::isa::{Instr, MovDir, OperandField, OperandLine, Program, Sign};

use super::desc::{
    BwdVmDesc, BwdVmSourceWindow, BWD_VM_ORIGIN_FIELD_BASE, BWD_VM_ORIGIN_FIELD_EXT,
    BWD_VM_PROGRAM_CAP,
};
use super::{launch_bwd_vm_release, launch_bwd_vm_validate, BWD_VM_ERR_SOURCE_OOB};
use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::{BF, E4};
use crate::prover::test_utils::make_test_context;
use crate::prover::ProverContext;
use crate::upstream::{Field, FieldExtension, PrimeField};

const BWD_VM_ERR_DESC_BOUNDS: u32 = 8192;
const BWD_VM_ERR_PROGRAM_OOB: u32 = 16384;

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

fn blank_desc(program: &[u16], n_instr: u32, logical_rows: usize) -> BwdVmDesc {
    // SAFETY: BwdVmDesc is a plain repr(C) CUDA ABI record. All-zero is valid
    // for every field, and every nonzero count/pointer used by the test is set
    // explicitly before launch.
    let mut desc: BwdVmDesc = unsafe { std::mem::zeroed() };
    desc.program[..program.len()].copy_from_slice(program);
    desc.program_lanes = program.len() as u32;
    desc.n_instr = n_instr;
    desc.logical_rows = logical_rows as u32;
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

    let program = source_program(OperandField::Ext, repeated);
    let mut desc = blank_desc(&program, if repeated { 2 } else { 1 }, rows);
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
        origin_field: BWD_VM_ORIGIN_FIELD_EXT,
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
    let program = source_program(OperandField::Base, false);
    let mut desc = blank_desc(&program, 1, rows);
    desc.n_source_windows = 1;
    desc.source_windows[0] = BwdVmSourceWindow {
        read_base: input_device.as_ptr().cast(),
        publish_base: ptr::null_mut(),
        read_stride_bytes: (input.len() * size_of::<BF>()) as u32,
        publish_stride_bytes: 0,
        backing_depth: 0,
        target_depth: 0,
        origin_field: BWD_VM_ORIGIN_FIELD_BASE,
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
        origin_field: BWD_VM_ORIGIN_FIELD_EXT,
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
        origin_field: BWD_VM_ORIGIN_FIELD_EXT,
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
        origin_field: BWD_VM_ORIGIN_FIELD_EXT,
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
    let later_program = source_program_with_first_access(OperandField::Ext, false);
    desc.program.fill(0);
    desc.program[..later_program.len()].copy_from_slice(&later_program);
    desc.program_lanes = later_program.len() as u32;
    desc.n_instr = 1;
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
