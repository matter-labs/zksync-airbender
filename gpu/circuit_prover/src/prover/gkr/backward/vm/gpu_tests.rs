use std::collections::{HashMap, HashSet};
use std::mem::size_of;
use std::ptr;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use era_cudart::memory::memory_copy_async;
use era_cudart::slice::DeviceSlice;
use gkr_eval_isa::bwd::distill::{bind, BwdBindings};
use gkr_eval_isa::bwd::interp::{interpret_bwd_row, role_combine, sumcheck_fold_point, Role};
use gkr_eval_isa::bwd::source::MaterializationPolicy;
use gkr_eval_isa::fwd::encode::encode;
use gkr_eval_isa::fwd::isa::{Instr, MovDir, OperandField, OperandLine, Program, Sign};
use rayon::prelude::*;

use super::compile::{load_add_sub_l0_case, AddSubBwdVmCase};
use super::desc::{
    BwdVmDesc, BwdVmSourceWindow, BWD_VM_ORIGIN_FIELD_BASE, BWD_VM_ORIGIN_FIELD_EXT,
    BWD_VM_PROGRAM_CAP,
};
use super::lower::{lower_bwd_vm, BwdVmRoundBinding, ResolvedBwdSourceWindow};
use super::{launch_bwd_vm_release, launch_bwd_vm_validate, BWD_VM_ERR_SOURCE_OOB};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::cub::device_reduce::{get_reduce_temp_storage_bytes, reduce, ReduceOperation};
use crate::primitives::context::DeviceAllocation;
use crate::primitives::device_structures::DeviceVectorChunk;
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::{
    get_eq_high_constant_device_ptr, launch_build_eq_high_and_low_groups_from_point, make_eq_sizes,
    GKR_EQ_GROUP_SIZE, GKR_EQ_GROUP_TABLE_LEN,
};
use crate::prover::gkr::forward::bench_interp::fixture::CircuitFixture;
use crate::prover::gkr::forward::vm::lower::read_place_to_gkr_address;
use crate::prover::test_utils::make_test_context;
use crate::prover::ProverContext;
use crate::upstream::{Field, FieldExtension, PrimeField, Seed, TIMESTAMP_COLUMNS_NUM_BITS};
use cs::gkr_compiler::dag_ir::{
    BwdRegime, ChallengeRef, ChallengeResolver, LookupResolver, LookupValueKind, ReadPlace,
    ReadResolver, Resolvers, SourceKind, VirtualSetupKind, VirtualSetupResolver,
};

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

enum R0HostColumn {
    Base(Vec<BF>),
    Ext(Vec<E4>),
}

struct R0OracleResolvers {
    columns: HashMap<ReadPlace, R0HostColumn>,
    challenges: HashMap<ChallengeRef, E4>,
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
}

impl ChallengeResolver for R0OracleResolvers {
    fn challenge(&self, reference: &ChallengeRef) -> E4 {
        *self
            .challenges
            .get(reference)
            .unwrap_or_else(|| panic!("R0 oracle missing challenge {reference:?}"))
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
) -> HashMap<ReadPlace, R0HostColumn> {
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
            let mut host = vec![E4::ZERO; fixture.trace_len];
            // SAFETY: `resolved.ptr` is the start of a fixture-owned E4 column
            // with exactly `trace_len` live elements. The fixture outlives the
            // copy and every later VM launch.
            let device = unsafe {
                DeviceSlice::from_raw_parts(resolved.ptr.cast::<E4>(), fixture.trace_len)
            };
            memory_copy_async(&mut host[..], device, fixture.context().get_exec_stream())
                .expect("snapshot R0 E4 source");
            fixture
                .context()
                .get_exec_stream()
                .synchronize()
                .expect("snapshot R0 E4 source sync");
            R0HostColumn::Ext(host)
        } else {
            let mut host = vec![BF::ZERO; fixture.trace_len];
            // SAFETY: same fixture-owned column invariant as the E4 branch,
            // with the field width established by `ResolvedColumn::is_e4`.
            let device = unsafe {
                DeviceSlice::from_raw_parts(resolved.ptr.cast::<BF>(), fixture.trace_len)
            };
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
    assert_eq!(
        group_count, 3,
        "add/sub R0 must use the incumbent 3-slot eq geometry"
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
    let low = groups.pop().expect("low eq group");
    let high1 = groups.pop().expect("second high eq group");
    let high0 = groups.pop().expect("first high eq group");
    ([high0, high1], low)
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
    q0: E4,
    q2: E4,
    z: E4,
    context: &ProverContext,
) {
    let q1_oracle = e4(0x5100 + budget_cells as u32);
    let eq_prefactor = e4(0x6100 + budget_cells as u32);
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
    assert_eq!(identity, normalized_claim, "c{budget_cells} claim identity");

    let mut claim = normalized_claim;
    claim.mul_assign(&eq_prefactor);
    let mut recovered_q1 = claim;
    recovered_q1.mul_assign(&eq_prefactor.inverse().expect("nonzero eq prefactor"));
    let mut bq0 = one_minus_z;
    bq0.mul_assign(&q0);
    recovered_q1.sub_assign(&bq0);
    recovered_q1.mul_assign(&z.inverse().expect("nonzero z"));
    assert_eq!(recovered_q1, q1_oracle, "c{budget_cells} recovered q1");

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
    assert_eq!(recovered_c, oracle_c, "c{budget_cells} recovered c");
    assert_eq!(recovered_d, oracle_d, "c{budget_cells} recovered d");

    let mut oracle_q2 = oracle_c;
    oracle_q2.double();
    oracle_q2.double();
    let mut two_d = oracle_d;
    two_d.double();
    oracle_q2.add_assign(&two_d);
    oracle_q2.add_assign(&q0);
    assert_eq!(oracle_q2, q2, "c{budget_cells} recovered c/d oracle");

    let cpu_coefficients = prover::gkr::sumcheck::output_univariate_monomial_form_max_quadratic::<
        BF,
        E4,
    >(z, normalized_claim, q0, recovered_c);
    assert_e4_bits(
        &format!("c{budget_cells} independent CPU coefficients"),
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
        &format!("c{budget_cells} independent GPU coefficients"),
        &gpu_coefficients,
        &oracle_round_coefficients,
    );
    assert_e4_bits(
        &format!("c{budget_cells} production four coefficients"),
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
    let columns = snapshot_r0_columns(&fixture, &cases);
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
