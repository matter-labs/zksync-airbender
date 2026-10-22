use std::sync::Arc;

use era_cudart::slice::DeviceSlice;
use field::Field;
use gpu_core::primitives::field::PR;
use gpu_prover_context::{ProverContext, ProverContextConfig};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use super::super::{read_back, upload};
use crate::backward::window_dr::DrWindowBindError;
use crate::proth120::backward::window_dr::{
    compile_dr_window_programs_pr, schedule_dr_batch_challenge_table_pr, unwrap_dr_window_pr,
    DrWindowLayerHookPr,
};
use crate::upstream::GKRAddress;
use crate::{DrWindowLayerProgram, GpuExtensionFieldPoly, GpuGKRStorage};

const PAIRWISE_SLOTS: u32 = (1 << 0) | (1 << 4);
const CELLS: usize = 27;

fn dr_context() -> ProverContext {
    ProverContext::new(&ProverContextConfig {
        device_allocation_blocks_count: Some(2048),
        host_allocator_blocks_count: 128,
        ..Default::default()
    })
    .unwrap()
}

fn add(a: PR, b: PR) -> PR {
    *a.clone().add_assign(&b)
}

fn sub(a: PR, b: PR) -> PR {
    *a.clone().sub_assign(&b)
}

fn mul(a: PR, b: PR) -> PR {
    *a.clone().mul_assign(&b)
}

fn random_pr(rng: &mut StdRng) -> PR {
    PR::from_u128_with_reduction(rng.random())
}

fn eq_rows(tau: &[PR]) -> Vec<PR> {
    let mut rows = vec![PR::ONE];
    for (k, &coordinate) in tau.iter().enumerate() {
        let zero = sub(PR::ONE, coordinate);
        let mut next = vec![PR::ZERO; rows.len() << 1];
        for (index, value) in next.iter_mut().enumerate() {
            let factor = if (index >> k) & 1 == 1 {
                coordinate
            } else {
                zero
            };
            *value = mul(rows[index & ((1 << k) - 1)], factor);
        }
        rows = next;
    }
    rows
}

fn lsb_fold(column: &[PR], challenge: PR) -> Vec<PR> {
    (0..column.len() / 2)
        .map(|cell| {
            let ancestor = 4 * (cell / 2) + (cell & 1);
            add(
                column[ancestor],
                mul(challenge, sub(column[ancestor + 2], column[ancestor])),
            )
        })
        .collect()
}

fn extend(f0: PR, f1: PR, x: usize) -> PR {
    match x {
        0 => f0,
        1 => f1,
        _ => sub(f1, f0),
    }
}

fn gate_tensor(column: &[PR], row: usize, gate: usize) -> [PR; CELLS] {
    let cell = |b0: usize, b1: usize, b2: usize| {
        column[2 * ((row << 3) | (b0 << 2) | (b1 << 1) | b2) + gate]
    };
    let mut tensor = [PR::ZERO; CELLS];
    for x0 in 0..3 {
        for x1 in 0..3 {
            for x2 in 0..3 {
                let at = |b0: usize, b1: usize| extend(cell(b0, b1, 0), cell(b0, b1, 1), x2);
                let along_x1 = |b0: usize| extend(at(b0, 0), at(b0, 1), x1);
                tensor[9 * x2 + 3 * x1 + x0] = extend(along_x1(0), along_x1(1), x0);
            }
        }
    }
    tensor
}

fn product(a: &[PR; CELLS], b: &[PR; CELLS]) -> [PR; CELLS] {
    std::array::from_fn(|cell| mul(a[cell], b[cell]))
}

fn window_rows(
    program: &DrWindowLayerProgram,
    columns: &[Vec<PR>],
    table: &[PR],
    eq: &[PR],
    rows: std::ops::Range<usize>,
) -> [PR; CELLS] {
    let projection = program.input_projection();
    let mut total = [PR::ZERO; CELLS];
    for row in rows {
        let mut acc = [PR::ZERO; CELLS];
        let mut accumulate = |weight: PR, values: [PR; CELLS]| {
            for (sum, value) in acc.iter_mut().zip(values) {
                *sum = add(*sum, mul(weight, value));
            }
        };
        for (dense_slot, slot) in program.program().slots().iter().enumerate() {
            let column = |operand: usize| {
                &columns[usize::from(projection.publication_index(dense_slot, operand).unwrap())]
            };
            let weights = (*slot.batch_exponents()).map(|exponent| table[usize::from(exponent)]);
            if PAIRWISE_SLOTS & (1 << slot.slot()) != 0 {
                for tower in 0..2 {
                    let values = product(
                        &gate_tensor(column(tower), row, 0),
                        &gate_tensor(column(tower), row, 1),
                    );
                    accumulate(weights[tower], values);
                }
            } else {
                let [n0, n1] = [0, 1].map(|gate| gate_tensor(column(0), row, gate));
                let [d0, d1] = [0, 1].map(|gate| gate_tensor(column(1), row, gate));
                let lhs = product(&n0, &d1);
                let rhs = product(&n1, &d0);
                accumulate(
                    weights[0],
                    std::array::from_fn(|cell| add(lhs[cell], rhs[cell])),
                );
                accumulate(weights[1], product(&d0, &d1));
            }
        }
        for (sum, value) in total.iter_mut().zip(acc) {
            *sum = add(*sum, mul(eq[row], value));
        }
    }
    total
}

fn host_window_tensor(
    program: &DrWindowLayerProgram,
    columns: &[Vec<PR>],
    table: &[PR],
    point: &[PR],
    eq_offset: usize,
    log_rows: usize,
) -> [PR; CELLS] {
    let eq = eq_rows(&point[eq_offset..eq_offset + log_rows]);
    let rows = 1usize << log_rows;
    let threads = std::thread::available_parallelism()
        .map(|count| count.get())
        .unwrap_or(1)
        .min(32)
        .min(rows);
    let chunk = rows.div_ceil(threads);
    std::thread::scope(|scope| {
        let handles: Vec<_> = (0..rows)
            .step_by(chunk)
            .map(|start| {
                let eq = &eq;
                scope.spawn(move || {
                    window_rows(
                        program,
                        columns,
                        table,
                        eq,
                        start..(start + chunk).min(rows),
                    )
                })
            })
            .collect();
        handles
            .into_iter()
            .fold([PR::ZERO; CELLS], |total, handle| {
                let part = handle.join().unwrap();
                std::array::from_fn(|cell| add(total[cell], part[cell]))
            })
    })
}

fn device_tensor(partials: *const PR, rows: usize, context: &ProverContext) -> [PR; CELLS] {
    let slice = unsafe { DeviceSlice::from_raw_parts(partials, rows * CELLS) };
    let host = read_back(slice, PR::ZERO, context);
    host.as_chunks::<CELLS>()
        .0
        .iter()
        .fold([PR::ZERO; CELLS], |total, tile| {
            std::array::from_fn(|cell| add(total[cell], tile[cell]))
        })
}

struct DrFixture {
    storage: GpuGKRStorage<PR, PR>,
    columns: Vec<Vec<PR>>,
}

fn dr_fixture(
    program: &DrWindowLayerProgram,
    aliases: &std::collections::BTreeMap<GKRAddress, GKRAddress>,
    rng: &mut StdRng,
    context: &ProverContext,
) -> DrFixture {
    let canonical = program.input_projection().canonical_sources();
    let len = 1usize << (program.folding_steps() + 1);
    let columns: Vec<Vec<PR>> = canonical
        .iter()
        .map(|_| (0..len).map(|_| random_pr(rng)).collect())
        .collect();
    #[allow(clippy::arc_with_non_send_sync)]
    let backing = Arc::new(upload(&columns.concat(), context));
    let mut storage = GpuGKRStorage::<PR, PR>::default();
    let mut inserted = std::collections::BTreeSet::new();
    for &address in canonical.iter().chain(program.program().sources()) {
        if !inserted.insert(address) {
            continue;
        }
        let target = aliases.get(&address).copied().unwrap_or(address);
        let index = canonical.binary_search(&target).unwrap();
        storage.insert_extension_at_layer(
            GpuGKRStorage::<PR, PR>::ext_poly_layer(address).unwrap(),
            address,
            GpuExtensionFieldPoly::from_arc(Arc::clone(&backing), index * len, len),
        );
    }
    DrFixture { storage, columns }
}

fn check_layer(
    program: &Arc<DrWindowLayerProgram>,
    aliases: &std::collections::BTreeMap<GKRAddress, GKRAddress>,
    entry_round: usize,
    rng: &mut StdRng,
    context: &ProverContext,
) {
    let n = program.folding_steps();
    let label = format!(
        "DR layer {} (n = {n}, entry = {entry_round})",
        program.layer()
    );
    let fixture = dr_fixture(program, aliases, rng, context);
    let point: Vec<PR> = (0..n + 2).map(|_| random_pr(rng)).collect();
    let d_point = upload(&point, context);
    let d_table =
        schedule_dr_batch_challenge_table_pr(unsafe { d_point.as_ptr().add(n) }, context).unwrap();
    let mut table = vec![PR::ONE];
    for _ in 1..10 {
        table.push(mul(*table.last().unwrap(), point[n]));
    }
    let hook = unwrap_dr_window_pr(DrWindowLayerHookPr::bind(
        program,
        &fixture.storage,
        entry_round,
        d_table.as_ptr(),
        d_point.as_ptr(),
        context,
    ))
    .unwrap();
    assert_eq!(hook.folding_steps(), n);
    assert_eq!(hook.entry_round(), entry_round);
    assert_eq!(hook.continuations().len(), (entry_round - 3) / 3);

    hook.launch_r0(context).unwrap();
    let device = device_tensor(hook.r0_binding().partials, hook.r0_row_tiles(), context);
    let host = host_window_tensor(program, &fixture.columns, &table, &point, 3, n - 3);
    assert_eq!(device, host, "{label}: R0 tensor");

    for pass in hook.continuations() {
        let start_round = pass.geometry.start_round;
        pass.launch(context).unwrap();
        let device = device_tensor(pass.binding().partials, pass.partial_rows(), context);
        let folded: Vec<Vec<PR>> = fixture
            .columns
            .iter()
            .map(|column| {
                point[..start_round]
                    .iter()
                    .fold(column.clone(), |column, &challenge| {
                        lsb_fold(&column, challenge)
                    })
            })
            .collect();
        let host = host_window_tensor(
            program,
            &folded,
            &table,
            &point,
            start_round + 3,
            n - start_round - 3,
        );
        assert_eq!(device, host, "{label}: continuation {start_round} tensor");
    }

    println!(
        "M6_DR_WINDOW {label}: sources={} r0_row_tiles={} passes={:?} tensors=match",
        fixture.columns.len(),
        hook.r0_row_tiles(),
        hook.continuations()
            .iter()
            .map(|pass| (pass.geometry.start_round, pass.partial_rows()))
            .collect::<Vec<_>>()
    );
    let sources =
        unwrap_dr_window_pr(hook.megakernel_source_pointers(program, &fixture.storage)).unwrap();
    let published = match hook.continuations().last() {
        Some(last) => last.geometry.start_round,
        None => 0,
    };
    let len = 1usize << (n + 1 - published);
    for (index, (&pointer, column)) in sources.iter().zip(&fixture.columns).enumerate() {
        let expected = point[..published]
            .iter()
            .fold(column.clone(), |column, &challenge| {
                lsb_fold(&column, challenge)
            });
        let slice = unsafe { DeviceSlice::from_raw_parts(pointer, len) };
        assert_eq!(
            read_back(slice, PR::ZERO, context),
            expected,
            "{label}: tail source {index}"
        );
    }
}

#[test]
#[cfg(not(no_cuda))]
fn pr_dr_window_matches_host() {
    let context = dr_context();
    let programs = super::super::cpu_abi::programs();
    let final_log = crate::proth120::backward::dr_tail::PR_DR_FINAL_TRACE_LOG_2;
    let window_programs = compile_dr_window_programs_pr(&programs, final_log);
    let trace_log = prover::gkr::prover_config::example_configs::l1_wrap_2p21::TRACE_LEN_LOG2;
    assert_eq!(window_programs.len(), trace_log - final_log as usize);
    let aliases = &programs.storage_layout.aliases;
    let mut rng = StdRng::seed_from_u64(0xd2_0e1d);
    let by_width = |width: usize| {
        window_programs
            .values()
            .find(|program| program.folding_steps() == width)
            .unwrap()
    };
    for (width, entry_round) in [(9, 3), (12, 6), (15, 9), (trace_log - 1, 15)] {
        check_layer(by_width(width), aliases, entry_round, &mut rng, &context);
    }

    let program = by_width(12);
    let fixture = dr_fixture(program, aliases, &mut rng, &context);
    let d_point = upload(&vec![PR::ONE; 14], &context);
    let bind = |program: &DrWindowLayerProgram, entry_round: usize| {
        DrWindowLayerHookPr::bind(
            program,
            &fixture.storage,
            entry_round,
            d_point.as_ptr(),
            d_point.as_ptr(),
            &context,
        )
        .err()
    };
    assert_eq!(
        bind(program, 18),
        Some(DrWindowBindError::InvalidTailEntry { entry_round: 18 })
    );
    assert_eq!(
        bind(program, 4),
        Some(DrWindowBindError::InvalidTailEntry { entry_round: 4 })
    );
    let oversized = DrWindowLayerProgram::new(
        program.layer(),
        25,
        program.program().clone(),
        program.input_projection().clone(),
    );
    assert_eq!(
        bind(&oversized, 6),
        Some(DrWindowBindError::UnsupportedFoldingSteps { folding_steps: 25 })
    );
}
