use std::collections::BTreeSet;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::{memory_copy, memory_copy_async, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::{MutPtrAndStride, PtrAndStride};
use gpu_core::primitives::field::PR;
use rand::{rngs::StdRng, Rng, SeedableRng};

use super::hypercube::MobiusPolicy;
use super::lde::{
    launch_transform, set_max_dynamic_smem, ChunkMap, DitPolicy, TransformPass, TransformPolicy,
};
use super::prefix::{
    chunk_plan, dispatch, l2_working_set_budget, launch_prefix_chunked, narrow_groups,
    prefix_groups, twiddle_bytes, ChunkPlan, CosetSource, Dispatch, DispatchError, FirstPassScale,
    PrefixPass, ScaleArgs, MAX_CHUNK_BYTES, MAX_TILE_BYTES,
};
use super::DeviceContext;
use crate::upstream::{domain_generator_for_size, Field};

const MIB: usize = 1 << 20;
const CHUNK_16_MIB: usize = 16 << 20;
const L2_RTX_PRO_6000: usize = 128 << 20;
const L2_RTX_5090: usize = 96 << 20;

fn groups_text(plan: &ChunkPlan) -> String {
    plan.passes
        .iter()
        .map(|p| format!("{}{}", p.stages, if p.narrow { "n" } else { "" }))
        .collect::<Vec<_>>()
        .join(",")
}

// Literal replica of the `nonfinal` load and store address loops (transform.cuh).
fn nonfinal_block_rows(
    log_n: u32,
    pass: &PrefixPass,
    x: usize,
    y: usize,
) -> (Vec<usize>, Vec<usize>) {
    let region = 1usize << (log_n - pass.start);
    let stride = region >> pass.tile_bits();
    let block_start = region * x + 8 * y;
    let threads = pass.threads() as usize;
    let mut loads = Vec::with_capacity(4 * threads);
    let mut stores = Vec::with_capacity(4 * threads);
    for tid in 0..threads {
        let tile_in_block = tid >> 3;
        let lane = tid & 7;
        for i in 0..4 {
            loads.push(block_start + lane + tile_in_block * stride + i * (region >> 2));
        }
        let warp = tid >> 5;
        let tile_in_store = (tid & 31) >> 3;
        let base = stride * (tile_in_store + 16 * warp) + lane;
        for i in 0..4 {
            stores.push(block_start + base + i * 4 * stride);
        }
    }
    (loads, stores)
}

fn mapped_y(map: ChunkMap, block_y: u32) -> u32 {
    ((block_y / map.strip_blocks) << map.strip_domain_bits)
        | (map.strip_base + block_y % map.strip_blocks)
}

// (a) per pass, the strips' block sets partition the full grid; (b) every block of strip k
// touches only rows whose bits [3, 3 + d) lie in strip k, so later passes read only rows the
// earlier passes of the same strip wrote; literal addresses are checked on boundary blocks, or on
// every block when `exhaustive`.
fn assert_closure(plan: &ChunkPlan, exhaustive: bool) {
    let n = plan.log_n;
    let d = plan.strip_domain_bits;
    let mut strip_rows: Vec<Option<BTreeSet<usize>>> = vec![None; plan.strips as usize];
    for pass in &plan.passes {
        let y_bits = pass.y_bits(n);
        assert!(y_bits >= d, "pass {pass:?} y bits below the strip domain");
        assert_eq!(pass.start + pass.tile_bits() + y_bits + 3, n);
        let grid_y = plan.grid_y(pass);
        let mut seen = vec![false; 1 << y_bits];
        let mut covered = exhaustive.then(|| vec![false; 1 << n]);
        for strip in 0..plan.strips {
            let map = plan.map(strip);
            let low = (strip * plan.strip_blocks) as usize;
            let high = low + plan.strip_blocks as usize;
            let mut rows = BTreeSet::new();
            for block_y in 0..grid_y {
                let y = mapped_y(map, block_y) as usize;
                assert!(!seen[y], "pass {pass:?} y {y} launched twice");
                seen[y] = true;
                assert!((low..high).contains(&(y & ((1 << d) - 1))));
                let xs: Vec<usize> = if exhaustive {
                    (0..1usize << pass.start).collect()
                } else {
                    vec![0, (1 << pass.start) - 1]
                };
                let boundary = block_y == 0 || block_y == grid_y - 1;
                if !exhaustive && !boundary {
                    continue;
                }
                for x in xs {
                    let (loads, stores) = nonfinal_block_rows(n, pass, x, y);
                    let load_set: BTreeSet<usize> = loads.iter().copied().collect();
                    let store_set: BTreeSet<usize> = stores.iter().copied().collect();
                    assert_eq!(load_set.len(), loads.len());
                    assert_eq!(load_set, store_set);
                    for &row in &loads {
                        assert!(row < 1 << n);
                        assert!((low..high).contains(&((row >> 3) & ((1 << d) - 1))));
                        if let Some(covered) = covered.as_mut() {
                            assert!(!covered[row]);
                            covered[row] = true;
                        }
                    }
                    if exhaustive {
                        rows.extend(load_set);
                    }
                }
            }
            if exhaustive {
                let slot = &mut strip_rows[strip as usize];
                match slot {
                    None => *slot = Some(rows),
                    Some(previous) => assert_eq!(previous, &rows, "strip {strip} rows differ"),
                }
            }
        }
        assert!(seen.iter().all(|&s| s), "pass {pass:?} grid not covered");
        if let Some(covered) = covered {
            assert!(covered.iter().all(|&c| c));
        }
    }
}

struct Family {
    name: &'static str,
    columns: usize,
    log_v: u32,
    skip_bottom: u32,
    logs: std::ops::RangeInclusive<u32>,
}

fn chunk_plan_table(l2: usize) -> Vec<(String, Result<Dispatch, DispatchError>)> {
    let families = [
        Family {
            name: "base_today",
            columns: 7,
            log_v: 2,
            skip_bottom: 10,
            logs: 16..=26,
        },
        Family {
            name: "base_d",
            columns: 13,
            log_v: 1,
            skip_bottom: 10,
            logs: 16..=26,
        },
        Family {
            name: "setup_today",
            columns: 1,
            log_v: 2,
            skip_bottom: 10,
            logs: 16..=26,
        },
        Family {
            name: "setup_d",
            columns: 2,
            log_v: 1,
            skip_bottom: 10,
            logs: 16..=26,
        },
    ];
    let budget = l2_working_set_budget(l2);
    let mut rows = Vec::new();
    let mut emit = |name: &str, n: u32, c: usize, v: u32, sb: u32| {
        let shape = dispatch(n, c, v, sb, l2);
        let key = format!("{name}\t{n}\t{c}\t{v}\t{sb}");
        let Ok(dispatched) = &shape else {
            rows.push((
                format!("{key}\tREJECT\t{:?}", shape.as_ref().unwrap_err()),
                shape,
            ));
            return;
        };
        assert_eq!(dispatched.l2_budget, budget);
        if dispatched.small {
            let column = size_of::<PR>() << n;
            let text = format!(
                "{key}\tSmall\t0\t{n}\t{}\t1\t0\t1\t1\t{column}\t{}\t0\t0\t0\t0\t1\t0\ttrue\ttrue\tPASS",
                dispatched.tile_bytes,
                CHUNK_16_MIB / column
            );
            rows.push((text, shape));
            return;
        }
        let plan = dispatched.prefix.as_ref().unwrap();
        let a = plan.stages();
        assert_eq!(a + dispatched.r, n);
        assert!(a >= sb && dispatched.r >= v && dispatched.tile_bytes <= MAX_TILE_BYTES);
        assert!(plan.chunk_bytes() <= MAX_CHUNK_BYTES || !dispatched.prefix_resident);
        let fixed = twiddle_bytes(33);
        assert_eq!(
            dispatched.prefix_working_set,
            2 * plan.chunk_bytes() + fixed
        );
        assert_eq!(
            dispatched.suffix_working_set,
            dispatched.tiles_per_batch * dispatched.tile_bytes + fixed
        );
        assert!((1..=2.min(dispatched.tiles_per_coset)).contains(&dispatched.tiles_per_batch));
        assert_eq!(
            dispatched.prefix_resident,
            dispatched.prefix_working_set <= budget
        );
        assert_eq!(
            dispatched.suffix_resident,
            dispatched.suffix_working_set <= budget
        );
        if !(dispatched.prefix_resident && dispatched.suffix_resident) {
            assert_eq!(dispatched.tiles_per_batch, 1);
        }
        let slots = if name.starts_with("intermediate") {
            plan.cols_per_chunk
        } else {
            plan.cols_per_chunk.min(c)
        };
        let per_column = plan.launches_per_column_group();
        let chunk = if plan.strips == 1 {
            (size_of::<PR>() << n) * plan.cols_per_chunk
        } else {
            plan.chunk_bytes()
        };
        let text = format!(
            "{key}\t{}\t{a}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{slots}\t{per_column}\t{}\t{}\t{}\t{}\t{chunk}\t{}\t{}\tPASS",
            groups_text(plan),
            dispatched.r,
            dispatched.tile_bytes,
            dispatched.tiles_per_coset,
            plan.strip_domain_bits,
            plan.strip_blocks,
            plan.strips,
            (size_of::<PR>() << n) >> plan.strip_domain_bits,
            per_column * c.div_ceil(slots),
            dispatched.prefix_working_set,
            dispatched.suffix_working_set,
            dispatched.tiles_per_batch,
            dispatched.prefix_resident,
            dispatched.suffix_resident,
        );
        assert_closure(plan, n <= 17);
        let groups: Vec<(u32, bool)> = plan.passes.iter().map(|p| (p.stages, p.narrow)).collect();
        let narrow = chunk_plan(n, &narrow_groups(&groups), plan.chunk_bytes()).unwrap();
        assert!(narrow.chunk_bytes() <= plan.chunk_bytes());
        assert_closure(&narrow, n <= 17);
        rows.push((text, shape));
    };
    for family in &families {
        for n in family.logs.clone() {
            emit(
                family.name,
                n,
                family.columns,
                family.log_v,
                family.skip_bottom,
            );
        }
    }
    for n in 13..=26 {
        for v in 1..=4 {
            emit("intermediate", n, 1, v, 5);
        }
    }
    for n in 8..=12 {
        for v in 1..=4 {
            emit("intermediate_small", n, 1, v, 5.min(n - v));
        }
    }
    for (n, c, v, sb) in [
        (24, 15, 1, 10),
        (7, 1, 1, 4),
        (16, 0, 1, 10),
        (16, 1000, 1, 10),
        (16, 7, 0, 10),
        (16, 7, 2, 15),
        (16, 7, 5, 10),
        (27, 1, 1, 5),
    ] {
        emit("invalid", n, c, v, sb);
    }
    rows
}

fn print_table(l2: usize, rows: &[(String, Result<Dispatch, DispatchError>)]) {
    println!(
        "# device L2 {} MiB, working-set budget {} MiB",
        l2 / MIB,
        l2_working_set_budget(l2) / MIB
    );
    println!("shape\tn\tC\tv\tsb\tprefix\ta\tr\ttile_B\ttiles_per_coset\tstrip_domain_bits\tstrip_blocks\tstrips\tper_strip_B\tcols_or_cosets_per_chunk\tprefix_launches_per_column\tprefix_launches_per_coset\tprefix_WS_L33_B\tsuffix_WS_L33_B\ttiles_per_batch\tchunk_B\tprefix_resident\tsuffix_resident\tstatus");
    for (row, _) in rows {
        println!("{row}");
    }
}

#[test]
fn cpu_pr_chunk_plan_closure() {
    let rows = chunk_plan_table(L2_RTX_PRO_6000);
    for (row, shape) in &rows {
        let invalid = row.starts_with("invalid") && !row.starts_with("invalid\t24\t15\t");
        assert_eq!(shape.is_err(), invalid, "{row}");
    }
    let today = dispatch(25, 7, 2, 10, L2_RTX_PRO_6000).unwrap();
    assert_eq!(
        (
            today.prefix_working_set,
            today.suffix_working_set,
            today.tiles_per_batch,
            today.prefix_resident && today.suffix_resident
        ),
        (38 * MIB, 62 * MIB, 2, true)
    );
    let shape_d = dispatch(24, 13, 1, 10, L2_RTX_PRO_6000).unwrap();
    assert_eq!(
        (
            shape_d.prefix_working_set,
            shape_d.suffix_working_set,
            shape_d.tiles_per_batch
        ),
        (38 * MIB, 58 * MIB, 2)
    );
    let wide = dispatch(24, 15, 1, 10, L2_RTX_PRO_6000).unwrap();
    assert_eq!(
        (wide.r, wide.tiles_per_batch, wide.suffix_working_set),
        (7, 1, 36 * MIB)
    );
    let n26 = dispatch(26, 7, 2, 10, L2_RTX_PRO_6000).unwrap();
    assert_eq!(
        (n26.prefix_resident, n26.prefix.unwrap().chunk_bytes()),
        (false, MAX_CHUNK_BYTES)
    );
    let n26_d = dispatch(26, 13, 1, 10, L2_RTX_PRO_6000).unwrap();
    // Full grid of [7n,7n,5n]: the narrow-7 first pass has 2^16 y-blocks, so it runs as two
    // grid-limit strips.
    assert_eq!(
        (n26_d.prefix_resident, n26_d.prefix.unwrap().strips),
        (false, 2)
    );
    print_table(L2_RTX_PRO_6000, &rows);
    // A100 40 MB, H100 50 MB, L40S / RTX 5090 96 MB.
    for l2 in [40 * MIB, 50 * MIB, L2_RTX_5090] {
        let device_rows = chunk_plan_table(l2);
        for (row, shape) in &device_rows {
            let invalid = row.starts_with("invalid") && !row.starts_with("invalid\t24\t15\t");
            assert_eq!(shape.is_err(), invalid, "{row} at {} MiB", l2 / MIB);
        }
        print_table(l2, &device_rows);
    }
    let today = dispatch(25, 7, 2, 10, L2_RTX_5090).unwrap();
    assert_eq!(
        (
            today.prefix_working_set,
            today.suffix_working_set,
            today.tiles_per_batch,
            today.r
        ),
        (38 * MIB, 34 * MIB, 1, 8)
    );
    let shape_d = dispatch(24, 13, 1, 10, L2_RTX_5090).unwrap();
    assert_eq!(
        (
            shape_d.prefix_working_set,
            shape_d.suffix_working_set,
            shape_d.tiles_per_batch,
            shape_d.r
        ),
        (38 * MIB, 32 * MIB, 1, 7)
    );

    // Synthetic devices, 16-192 MiB L2: every production shape dispatches on every L2, the
    // residency flags only turn on with more L2, and more L2 never shrinks a resident chunk
    // or batch.
    let shapes = [
        (25, 7, 2, 10),
        (24, 13, 1, 10),
        (25, 1, 2, 10),
        (24, 2, 1, 10),
        (23, 1, 4, 5),
        (19, 1, 4, 5),
        (15, 1, 4, 5),
        (11, 1, 4, 5),
    ];
    for &(n, c, v, sb) in &shapes {
        let mut previous: Option<Dispatch> = None;
        let mut first_resident = None;
        for l2_mib in [
            16, 24, 32, 40, 48, 50, 56, 64, 72, 80, 88, 96, 112, 128, 160, 192,
        ] {
            let current = dispatch(n, c, v, sb, l2_mib * MIB)
                .unwrap_or_else(|e| panic!("({n},{c},{v},{sb}) at {l2_mib} MiB: {e:?}"));
            let resident = current.prefix_resident && current.suffix_resident;
            if let Some(prior) = &previous {
                let prior_resident = prior.prefix_resident && prior.suffix_resident;
                assert!(
                    resident || !prior_resident,
                    "({n},{c},{v},{sb}) at {l2_mib} MiB"
                );
                if resident && prior_resident {
                    let chunk = |d: &Dispatch| d.prefix.as_ref().map_or(0, ChunkPlan::chunk_bytes);
                    assert!(chunk(&current) >= chunk(prior));
                    assert!(current.tiles_per_batch >= prior.tiles_per_batch);
                }
            }
            if resident && first_resident.is_none() {
                first_resident = Some(l2_mib);
            }
            previous = Some(current);
        }
        println!(
            "cpu_pr_chunk_plan_closure: ({n},{c},{v},{sb}) dispatches on 16-192 MiB, fully L2-resident from {:?} MiB",
            first_resident
        );
    }
}

fn reverse_bits(value: usize, bits: u32) -> usize {
    if bits == 0 {
        0
    } else {
        value.reverse_bits() >> (usize::BITS - bits)
    }
}

// The first `stages` stages of the network restricted to one low digit n2: the 2^stages values
// x[k * 2^r + n2] form an independent sub-network whose region twiddles are global.
fn cpu_prefix_digit(values: &mut [PR], stages: u32, root: Option<(PR, u32)>) {
    for t in 0..stages {
        let half = 1usize << (stages - t - 1);
        for region in 0..1usize << t {
            let twiddle = root.map(|(w, log_max_domain)| {
                w.pow_u128(reverse_bits(region, log_max_domain - 1) as u128)
            });
            for j in 0..half {
                let a = region * 2 * half + j;
                let b = a + half;
                match twiddle {
                    Some(twiddle) => {
                        let mut vb = values[b];
                        vb.mul_assign(&twiddle);
                        let mut sum = values[a];
                        sum.add_assign(&vb);
                        let mut diff = values[a];
                        diff.sub_assign(&vb);
                        values[a] = sum;
                        values[b] = diff;
                    }
                    None => {
                        let va = values[a];
                        values[b].sub_assign(&va);
                    }
                }
            }
        }
    }
}

fn assert_prefix_digits(
    input: &[PR],
    output: &[PR],
    log_n: u32,
    stages: u32,
    root: Option<(PR, u32)>,
    digits: &[usize],
) {
    let r = log_n - stages;
    for &n2 in digits {
        let mut values: Vec<PR> = (0..1usize << stages)
            .map(|k| input[(k << r) + n2])
            .collect();
        cpu_prefix_digit(&mut values, stages, root);
        for (block, expected) in values.iter().enumerate() {
            assert_eq!(
                output[(block << r) + n2].0,
                expected.0,
                "prefix block {block} digit {n2}"
            );
        }
    }
}

fn upload(values: &[PR]) -> DeviceAllocation<PR> {
    let mut device = DeviceAllocation::alloc(values.len()).unwrap();
    memory_copy(&mut device, values).unwrap();
    device
}

fn download(values: &DeviceSlice<PR>, stream: &CudaStream) -> Vec<PR> {
    let mut host = vec![PR::ZERO; values.len()];
    memory_copy_async(&mut host, values, stream).unwrap();
    stream.synchronize().unwrap();
    host
}

// The coarsest strip split whose grid fits grid.y <= 2^15 (one launch per pass when it does).
fn full_grid(plan: &ChunkPlan) -> ChunkPlan {
    let y_bits = plan.passes.iter().map(|p| p.y_bits(plan.log_n));
    let max = y_bits.clone().max().unwrap();
    let min = y_bits.min().unwrap();
    let strip_domain_bits = max.saturating_sub(15).min(min);
    ChunkPlan {
        cols_per_chunk: usize::MAX,
        strips: 1 << strip_domain_bits,
        strip_blocks: 1,
        strip_domain_bits,
        ..plan.clone()
    }
}

fn launch_final<P: TransformPolicy>(
    policy: &P,
    values: &mut DeviceSlice<PR>,
    log_n: u32,
    start: u32,
    cols: usize,
    stream: &CudaStream,
) {
    let stages = log_n - start;
    let function = policy.function(TransformPass::Final(stages));
    let bytes = size_of::<PR>() << stages;
    if stages >= 10 {
        set_max_dynamic_smem(&function, bytes).unwrap();
    }
    let rows = 1usize << log_n;
    let mut config = CudaLaunchConfig::basic(
        (1u32 << (log_n - stages), cols as u32),
        1u32 << (stages - 2),
        stream,
    );
    config.dynamic_smem_bytes = bytes;
    let target = MutPtrAndStride::new(values.as_mut_ptr(), rows);
    let source = PtrAndStride::new(target.ptr as *const PR, rows);
    function
        .launch(
            &config,
            &policy.arguments(source, target, log_n, start, ChunkMap::FULL),
        )
        .unwrap();
}

// Chunked prefix == full-grid prefix (index for index) == the CPU sub-network on sampled (or all)
// low digits; when the remaining stages have a final kernel, prefix + final == launch_transform.
fn prefix_case<P: TransformPolicy>(
    policy: &P,
    root: Option<(PR, u32)>,
    log_n: u32,
    groups: &[(u32, bool)],
    cols: usize,
    rng: &mut StdRng,
    stream: &CudaStream,
) -> ChunkPlan {
    let plan = chunk_plan(log_n, groups, CHUNK_16_MIB).unwrap();
    let rows = 1usize << log_n;
    let input: Vec<PR> = (0..rows * cols)
        .map(|_| PR::new(rng.random::<u128>() % PR::ORDER))
        .collect();
    let device_input = upload(&input);
    let mut chunked = DeviceAllocation::<PR>::alloc(rows * cols).unwrap();
    let mut reference = DeviceAllocation::<PR>::alloc(rows * cols).unwrap();
    let source = PtrAndStride::new(device_input.as_ptr(), rows);
    launch_prefix_chunked(
        policy,
        source,
        MutPtrAndStride::new(chunked.as_mut_ptr(), rows),
        cols,
        &plan,
        None,
        stream,
    )
    .unwrap();
    launch_prefix_chunked(
        policy,
        source,
        MutPtrAndStride::new(reference.as_mut_ptr(), rows),
        cols,
        &full_grid(&plan),
        None,
        stream,
    )
    .unwrap();
    let actual = download(&chunked, stream);
    assert!(
        actual == download(&reference, stream),
        "chunked prefix differs from the full grid at n = {log_n}"
    );
    assert!(download(&device_input, stream) == input);
    let stages = plan.stages();
    let r = log_n - stages;
    let digits: Vec<usize> = if log_n <= 19 {
        (0..1 << r).collect()
    } else {
        let mut d = vec![0, 1, (1 << r) - 1];
        d.extend((0..5).map(|_| rng.random_range(0..1usize << r)));
        d
    };
    for column in [0, cols - 1] {
        let span = column * rows..(column + 1) * rows;
        assert_prefix_digits(
            &input[span.clone()],
            &actual[span],
            log_n,
            stages,
            root,
            &digits,
        );
    }
    if [8, 10, 12].contains(&r) {
        launch_final(policy, &mut chunked, log_n, stages, cols, stream);
        let target = MutPtrAndStride::new(reference.as_mut_ptr(), rows);
        launch_transform(policy, source, target, log_n, cols, stream).unwrap();
        assert!(
            download(&chunked, stream) == download(&reference, stream),
            "prefix + final<{r}> differs from launch_transform at n = {log_n}"
        );
    }
    plan
}

#[test]
#[cfg(not(no_cuda))]
fn pr_prefix_chunked_cpu_parity() {
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    let mut rng = StdRng::seed_from_u64(0x9120_3101);
    let root = Some((domain_generator_for_size::<PR>(1u64 << 31), 31));
    let policy = DitPolicy(ctx.descriptor());
    for (log_n, columns, log_v, skip_bottom, cols) in [
        (25, 7, 2, 10, 1),
        (24, 13, 1, 10, 1),
        (23, 1, 4, 5, 2),
        (22, 7, 2, 10, 2),
        (21, 1, 4, 5, 2),
        (19, 1, 4, 5, 3),
        (17, 2, 1, 10, 3),
        (16, 13, 1, 10, 13),
        (15, 1, 4, 5, 3),
        (13, 1, 4, 5, 3),
    ] {
        let shape = dispatch(log_n, columns, log_v, skip_bottom, device_l2()).unwrap();
        let groups: Vec<(u32, bool)> = shape
            .prefix
            .as_ref()
            .unwrap()
            .passes
            .iter()
            .map(|p| (p.stages, p.narrow))
            .collect();
        for groups in [groups.clone(), narrow_groups(&groups)] {
            let plan = prefix_case(&policy, root, log_n, &groups, cols, &mut rng, &stream);
            println!("pr_prefix_chunked_cpu_parity: n {log_n} prefix {} r {} strips {} x {} block-strips (d {}), {} cols, 0 mismatches", groups_text(&plan), shape.r, plan.strips, plan.strip_blocks, plan.strip_domain_bits, cols);
        }
    }
    let ctx33 = DeviceContext::create(33).unwrap();
    let root33 = Some((domain_generator_for_size::<PR>(1u64 << 33), 33));
    prefix_case(
        &DitPolicy(ctx33.descriptor()),
        root33,
        24,
        &[(6, false), (6, false), (5, true)],
        1,
        &mut rng,
        &stream,
    );
    println!("pr_prefix_chunked_cpu_parity: L = 33, n 24 [6,6,5n], 0 mismatches");
}

#[test]
#[cfg(not(no_cuda))]
fn pr_prefix_chunked_mobius_cpu_parity() {
    let stream = CudaStream::create().unwrap();
    let mut rng = StdRng::seed_from_u64(0x9120_3102);
    for (log_n, groups, cols) in [
        (25, vec![(8, false), (7, false)], 1),
        (24, vec![(8, false), (8, false)], 1),
        (23, vec![(8, false), (7, false)], 2),
        (19, vec![(6, false), (5, true)], 3),
        (25, vec![(8, false), (7, true)], 1),
        (19, vec![(6, true), (5, true)], 3),
    ] {
        let plan = prefix_case(&MobiusPolicy, None, log_n, &groups, cols, &mut rng, &stream);
        println!(
            "pr_prefix_chunked_mobius_cpu_parity: n {log_n} prefix {} strips {} x {}, 0 mismatches",
            groups_text(&plan),
            plan.strips,
            plan.strip_blocks
        );
    }
}

#[test]
fn cpu_pr_prefix_digit_matches_transform_network() {
    let mut rng = StdRng::seed_from_u64(0x9120_3103);
    for log_max_domain in [31, 33] {
        let root = domain_generator_for_size::<PR>(1u64 << log_max_domain);
        for log_n in [3, 6, 9] {
            let input: Vec<PR> = (0..1usize << log_n)
                .map(|_| PR::new(rng.random::<u128>() % PR::ORDER))
                .collect();
            let mut full = input.clone();
            cpu_prefix_digit(&mut full, log_n, Some((root, log_max_domain)));
            let omega = domain_generator_for_size::<PR>(1u64 << log_n);
            for (p, value) in full.iter().enumerate() {
                let q = reverse_bits(p, log_n);
                let mut expected = PR::ZERO;
                for (i, x) in input.iter().enumerate() {
                    let mut term = omega.pow_u128(((q * i) % (1 << log_n)) as u128);
                    term.mul_assign(x);
                    expected.add_assign(&term);
                }
                assert_eq!(
                    value.0, expected.0,
                    "L {log_max_domain} n {log_n} position {p}"
                );
            }
        }
    }
}

#[test]
#[ignore]
#[cfg(not(no_cuda))]
fn pr_prefix_profile_probe() {
    use era_cudart::memory::memory_set_async;
    use gpu_core::primitives::nvtx::scoped_range;
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    let (log_n, cols) = (25u32, 7usize);
    let rows = 1usize << log_n;
    let shape = dispatch(log_n, cols, 2, 10, device_l2()).unwrap();
    let plan = shape.prefix.unwrap();
    let mut input = DeviceAllocation::<PR>::alloc(rows * cols).unwrap();
    let mut output = DeviceAllocation::<PR>::alloc(rows * cols).unwrap();
    unsafe {
        memory_set_async(input.transmute_mut(), 0, &stream).unwrap();
    }
    let policy = DitPolicy(ctx.descriptor());
    let today = chunk_plan(log_n, &[(8, false), (7, false)], CHUNK_16_MIB).unwrap();
    let narrow = chunk_plan(
        log_n,
        &narrow_groups(
            &plan
                .passes
                .iter()
                .map(|p| (p.stages, p.narrow))
                .collect::<Vec<_>>(),
        ),
        plan.chunk_bytes(),
    )
    .unwrap();
    let variants = [
        ("prefix.warmup", plan.clone()),
        ("prefix.probe", plan.clone()),
        ("prefix.narrow", narrow),
        ("prefix.full", full_grid(&plan)),
        ("prefix.today_8_7", full_grid(&today)),
    ];
    let start = era_cudart::event::CudaEvent::create().unwrap();
    let end = era_cudart::event::CudaEvent::create().unwrap();
    for (label, variant) in &variants {
        let _range = scoped_range(Some("ab"), label);
        for iteration in 0..3 {
            start.record(&stream).unwrap();
            launch_prefix_chunked(
                &policy,
                PtrAndStride::new(input.as_ptr(), rows),
                MutPtrAndStride::new(output.as_mut_ptr(), rows),
                cols,
                variant,
                Some(FirstPassScale {
                    descriptor: ctx.descriptor(),
                    scale: ScaleArgs {
                        coset: CosetSource::Constant(3),
                        log_domain: 31,
                    },
                }),
                &stream,
            )
            .unwrap();
            end.record(&stream).unwrap();
            end.synchronize().unwrap();
            let ms = era_cudart::event::elapsed_time(&start, &end).unwrap();
            println!(
                "pr_prefix_profile_probe: {label} iteration {iteration}: {ms:.3} ms for {cols} x 2^{log_n} ({} passes, {} strips)",
                variant.passes.len(),
                variant.strips
            );
            if *label == "prefix.probe" {
                break;
            }
        }
    }
}

fn reference_plan(log_n: u32) -> ChunkPlan {
    chunk_plan(log_n, &prefix_groups(log_n - 8).unwrap(), CHUNK_16_MIB).unwrap()
}

fn narrow_reference_plan(log_n: u32) -> ChunkPlan {
    let groups = narrow_groups(&prefix_groups(log_n - 8).unwrap());
    chunk_plan(log_n, &groups, CHUNK_16_MIB).unwrap()
}

#[test]
#[cfg(not(no_cuda))]
fn pr_lde_coset_slot_fused_scale_parity() {
    use super::{lde_coset, lde_coset_slot, lde_cosets_batched, lde_finish_reference};
    use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
    let stream = CudaStream::create().unwrap();
    let mut rng = StdRng::seed_from_u64(0x9120_3201);
    for (log_max_domain, log_domain) in [(31, 31), (33, 33), (33, 31)] {
        let ctx = DeviceContext::create(log_max_domain).unwrap();
        let nu = domain_generator_for_size::<PR>(1u64 << log_domain);
        for (log_n, cols) in [(13, 3), (15, 2), (23, 2), (25, 1)] {
            let rows = 1usize << log_n;
            let plans = [reference_plan(log_n), narrow_reference_plan(log_n)];
            let monomials: Vec<PR> = (0..rows * cols)
                .map(|_| PR::new(rng.random::<u128>() % PR::ORDER))
                .collect();
            let device_monomials = upload(&monomials);
            let last = (1u32 << (log_domain - log_n)) - 1;
            let mut reference = DeviceAllocation::<PR>::alloc(rows * cols).unwrap();
            let mut candidate = DeviceAllocation::<PR>::alloc(rows * cols).unwrap();
            let device_last = DeviceAllocation::<u32>::alloc(1).and_then(|mut d| {
                memory_copy(&mut d, &[last])?;
                Ok(d)
            });
            let device_last = device_last.unwrap();
            for (k, source) in [
                (0, CosetSource::Constant(0)),
                (1, CosetSource::Constant(1)),
                (last, CosetSource::Constant(last)),
                (last, CosetSource::Device(&device_last)),
            ] {
                let offset = upload(&[nu.pow_u128(k as u128)]);
                lde_coset(
                    &ctx,
                    &DeviceMatrix::new(&device_monomials, rows),
                    &mut DeviceMatrixMut::new(&mut reference, rows),
                    &offset,
                    &stream,
                )
                .unwrap();
                for plan in &plans {
                    let scale = ScaleArgs {
                        coset: source,
                        log_domain,
                    };
                    lde_coset_slot(
                        &ctx,
                        &device_monomials,
                        &mut candidate,
                        cols,
                        plan,
                        scale,
                        &stream,
                    )
                    .unwrap();
                    lde_finish_reference(&ctx, &mut candidate, cols, plan, &stream).unwrap();
                    assert!(
                        download(&candidate, &stream) == download(&reference, &stream),
                        "fused scale differs: L {log_max_domain} D {log_domain} n {log_n} k {k}"
                    );
                }
            }
        }
        let log_n = 13;
        let rows = 1usize << log_n;
        let plan = reference_plan(log_n);
        let column: Vec<PR> = (0..rows)
            .map(|_| PR::new(rng.random::<u128>() % PR::ORDER))
            .collect();
        let device_column = upload(&column);
        let end = 1u32 << (log_domain - log_n);
        for (k0, cosets) in [(0, 4usize), (end - 4, 4), (end - 131, 129)] {
            let mut reference = DeviceAllocation::<PR>::alloc(rows * cosets).unwrap();
            let mut candidate = DeviceAllocation::<PR>::alloc(rows * cosets).unwrap();
            lde_cosets_batched(
                &ctx,
                &device_column,
                log_domain,
                k0..k0 + cosets as u32,
                &mut reference,
                &stream,
            )
            .unwrap();
            let scale = ScaleArgs {
                coset: CosetSource::Batched { k0 },
                log_domain,
            };
            lde_coset_slot(
                &ctx,
                &device_column,
                &mut candidate,
                cosets,
                &plan,
                scale,
                &stream,
            )
            .unwrap();
            lde_finish_reference(&ctx, &mut candidate, cosets, &plan, &stream).unwrap();
            assert!(
                download(&candidate, &stream) == download(&reference, &stream),
                "batched fused scale differs: L {log_max_domain} D {log_domain} k0 {k0}"
            );
        }
        println!("pr_lde_coset_slot_fused_scale_parity: L {log_max_domain} D {log_domain}: n 13/15/23/25 cosets 0/1/last (constant + device) and batched (k0, cosets) (0, 4) (last-3, 4) (last-130, 129), 0 mismatches");
    }
}

fn device_l2() -> usize {
    gpu_core::primitives::context::DeviceProperties::new()
        .unwrap()
        .l2_cache_size_bytes
}

// Forces the dispatch of smaller devices on this GPU: every plan (resident, smaller strips or
// full grid) gives the same prefix as its coarsest split, and prefix + final == lde_coset.
#[test]
#[cfg(not(no_cuda))]
fn pr_lde_coset_slot_small_l2_parity() {
    use super::{has_reference_finish, lde_coset, lde_coset_slot, lde_finish_reference};
    use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    let mut rng = StdRng::seed_from_u64(0x9120_3401);
    let nu = domain_generator_for_size::<PR>(1u64 << 31);
    let k = 5u32;
    for (log_n, columns, log_v, skip_bottom, cols) in [
        (25, 7, 2, 10, 2),
        (24, 13, 1, 10, 2),
        (26, 7, 2, 10, 1),
        (26, 13, 1, 10, 1),
        (23, 1, 4, 5, 2),
        (19, 1, 4, 5, 3),
    ] {
        let rows = 1usize << log_n;
        let monomials: Vec<PR> = (0..rows * cols)
            .map(|_| PR::new(rng.random::<u128>() % PR::ORDER))
            .collect();
        let device_monomials = upload(&monomials);
        let mut candidate = DeviceAllocation::<PR>::alloc(rows * cols).unwrap();
        let mut reference = DeviceAllocation::<PR>::alloc(rows * cols).unwrap();
        let scale = ScaleArgs {
            coset: CosetSource::Constant(k),
            log_domain: 31,
        };
        for l2_mib in [16usize, 40, 50, 96, 128] {
            let shape = dispatch(log_n, columns, log_v, skip_bottom, l2_mib * MIB).unwrap();
            let plan = shape.prefix.as_ref().unwrap();
            lde_coset_slot(
                &ctx,
                &device_monomials,
                &mut candidate,
                cols,
                plan,
                scale,
                &stream,
            )
            .unwrap();
            lde_coset_slot(
                &ctx,
                &device_monomials,
                &mut reference,
                cols,
                &full_grid(plan),
                scale,
                &stream,
            )
            .unwrap();
            let prefix = download(&candidate, &stream);
            assert!(
                prefix == download(&reference, &stream),
                "({log_n},{columns},{log_v},{skip_bottom}) L2 {l2_mib} MiB: prefix differs from its full grid"
            );
            if has_reference_finish(plan) {
                lde_finish_reference(&ctx, &mut candidate, cols, plan, &stream).unwrap();
                let offset = upload(&[nu.pow_u128(k as u128)]);
                lde_coset(
                    &ctx,
                    &DeviceMatrix::new(&device_monomials, rows),
                    &mut DeviceMatrixMut::new(&mut reference, rows),
                    &offset,
                    &stream,
                )
                .unwrap();
                assert!(
                    download(&candidate, &stream) == download(&reference, &stream),
                    "({log_n},{columns},{log_v},{skip_bottom}) L2 {l2_mib} MiB: LDE differs"
                );
            }
            println!(
                "pr_lde_coset_slot_small_l2_parity: ({log_n},{columns},{log_v},{skip_bottom}) L2 {l2_mib} MiB: prefix {} chunk {} MiB resident prefix/suffix {}/{} tiles/batch {} finish {}, 0 mismatches",
                groups_text(plan),
                plan.chunk_bytes() / MIB,
                shape.prefix_resident,
                shape.suffix_resident,
                shape.tiles_per_batch,
                has_reference_finish(plan)
            );
        }
    }
}

#[test]
#[cfg(not(no_cuda))]
fn pr_hypercube_chunked_matches_plain() {
    use super::{hypercube_evals_to_monomials, hypercube_evals_to_monomials_chunked};
    use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
    let stream = CudaStream::create().unwrap();
    let mut rng = StdRng::seed_from_u64(0x9120_2301);
    for (log_n, cols) in [(12, 3), (16, 3), (21, 2), (23, 2), (24, 1), (25, 1)] {
        let rows = 1usize << log_n;
        let input: Vec<PR> = (0..rows * cols)
            .map(|_| PR::new(rng.random::<u128>() % PR::ORDER))
            .collect();
        let device_input = upload(&input);
        let mut reference = DeviceAllocation::<PR>::alloc(rows * cols).unwrap();
        let mut candidate = DeviceAllocation::<PR>::alloc(rows * cols).unwrap();
        hypercube_evals_to_monomials(
            &DeviceMatrix::new(&device_input, rows),
            &mut DeviceMatrixMut::new(&mut reference, rows),
            &stream,
        )
        .unwrap();
        let expected = download(&reference, &stream);
        for l2_mib in [16usize, 40, 128] {
            hypercube_evals_to_monomials_chunked(
                &DeviceMatrix::new(&device_input, rows),
                &mut DeviceMatrixMut::new(&mut candidate, rows),
                l2_mib * MIB,
                &stream,
            )
            .unwrap();
            assert!(
                download(&candidate, &stream) == expected,
                "chunked Mobius differs at n {log_n} with L2 {l2_mib} MiB"
            );
        }
        assert!(download(&device_input, &stream) == input);
        println!("pr_hypercube_chunked_matches_plain: n {log_n} x {cols} at L2 16/40/128 MiB, 0 mismatches");
    }
}

// Lazy prefix passes at the top of their range: every input p - 1 (largest canonical value), scaled
// by the last coset and unscaled, through single passes of 5-8 stages (wide and narrow) and the
// production three-pass prefix; prefix + final must equal lde_coset.
#[test]
#[cfg(not(no_cuda))]
fn pr_prefix_lazy_extreme_inputs() {
    use super::{lde_coset, lde_coset_slot, lde_finish_reference};
    use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    let nu = domain_generator_for_size::<PR>(1u64 << 31);
    let cols = 2;
    for (log_n, groups) in [
        (16, vec![(8, false)]),
        (15, vec![(7, false)]),
        (15, vec![(7, true)]),
        (14, vec![(6, false)]),
        (14, vec![(6, true)]),
        (13, vec![(5, false)]),
        (13, vec![(5, true)]),
        (24, vec![(8, false), (8, false)]),
        (25, vec![(6, true), (6, true), (5, true)]),
    ] {
        let rows = 1usize << log_n;
        let plan = chunk_plan(log_n, &groups, CHUNK_16_MIB).unwrap();
        let monomials = vec![PR::new(PR::ORDER - 1); rows * cols];
        let device_monomials = upload(&monomials);
        let mut candidate = DeviceAllocation::<PR>::alloc(rows * cols).unwrap();
        let mut reference = DeviceAllocation::<PR>::alloc(rows * cols).unwrap();
        for k in [0, (1u32 << (31 - log_n)) - 1] {
            let scale = ScaleArgs {
                coset: CosetSource::Constant(k),
                log_domain: 31,
            };
            lde_coset_slot(
                &ctx,
                &device_monomials,
                &mut candidate,
                cols,
                &plan,
                scale,
                &stream,
            )
            .unwrap();
            assert!(
                download(&candidate, &stream)
                    .iter()
                    .all(|v| v.0 < PR::ORDER),
                "noncanonical prefix store"
            );
            lde_finish_reference(&ctx, &mut candidate, cols, &plan, &stream).unwrap();
            lde_coset(
                &ctx,
                &DeviceMatrix::new(&device_monomials, rows),
                &mut DeviceMatrixMut::new(&mut reference, rows),
                &upload(&[nu.pow_u128(k as u128)]),
                &stream,
            )
            .unwrap();
            let actual = download(&candidate, &stream);
            assert!(
                actual.iter().all(|v| v.0 < PR::ORDER),
                "noncanonical output"
            );
            assert!(
                actual == download(&reference, &stream),
                "lazy prefix {} differs at n {log_n}, k {k}",
                groups_text(&plan)
            );
        }
        println!("pr_prefix_lazy_extreme_inputs: n {log_n} prefix {} with all inputs p - 1, k 0 and last, 0 mismatches", groups_text(&plan));
    }
}
