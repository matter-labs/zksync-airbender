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
    chunk_plan, dispatch, launch_prefix_chunked, prefix_groups, subroot_bytes, twiddle_bytes,
    ChunkPlan, CosetSource, FirstPassScale, PrefixPass, ScaleArgs, L2_CHUNK_BYTES,
    L2_WORKING_SET_BYTES, MAX_TILE_BYTES,
};
use super::DeviceContext;
use crate::upstream::{domain_generator_for_size, Field};

const MIB: usize = 1 << 20;

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

#[test]
fn cpu_pr_chunk_plan_closure() {
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
    let mut rows = Vec::new();
    let mut emit = |name: &str, n: u32, c: usize, v: u32, sb: u32| {
        let Some(shape) = dispatch(n, c, v, sb) else {
            rows.push(format!("{name}\t{n}\t{c}\t{v}\t{sb}\tREJECT"));
            return None;
        };
        if shape.small {
            let column = size_of::<PR>() << n;
            rows.push(format!(
                "{name}\t{n}\t{c}\t{v}\t{sb}\tSmall\t0\t{n}\t{}\t1\t0\t1\t1\t{column}\t{}\t0\t0\t0\t0\tPASS",
                shape.tile_bytes,
                L2_CHUNK_BYTES / column
            ));
            return Some(shape);
        }
        let plan = shape.prefix.as_ref().unwrap();
        let a = plan.stages();
        assert_eq!(a + shape.r, n);
        assert!(a >= sb && shape.r >= v && shape.tile_bytes <= MAX_TILE_BYTES);
        assert!(plan.chunk_bytes() <= L2_CHUNK_BYTES);
        let fixed = twiddle_bytes(33) + subroot_bytes(n, v, sb);
        assert_eq!(shape.prefix_working_set, 2 * plan.chunk_bytes() + fixed);
        assert_eq!(
            shape.suffix_working_set,
            shape.tiles_per_coset.min(2) * shape.tile_bytes + fixed
        );
        assert!(shape.prefix_working_set.max(shape.suffix_working_set) <= L2_WORKING_SET_BYTES);
        let slots = if name.starts_with("intermediate") {
            plan.cols_per_chunk
        } else {
            plan.cols_per_chunk.min(c)
        };
        let per_column = plan.launches_per_column_group();
        rows.push(format!(
            "{name}\t{n}\t{c}\t{v}\t{sb}\t{}\t{a}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{slots}\t{per_column}\t{}\t{}\t{}\tPASS",
            groups_text(plan),
            shape.r,
            shape.tile_bytes,
            shape.tiles_per_coset,
            plan.strip_domain_bits,
            plan.strip_blocks,
            plan.strips,
            (size_of::<PR>() << n) >> plan.strip_domain_bits,
            per_column * c.div_ceil(slots),
            shape.prefix_working_set,
            shape.suffix_working_set,
        ));
        assert_closure(plan, n <= 17);
        Some(shape)
    };
    for family in &families {
        for n in family.logs.clone() {
            let shape = emit(
                family.name,
                n,
                family.columns,
                family.log_v,
                family.skip_bottom,
            );
            assert_eq!(shape.is_none(), n == 26 || n == 25 && family.columns == 13);
        }
    }
    for n in 13..=26 {
        for v in 1..=4 {
            let shape = emit("intermediate", n, 1, v, 5);
            assert_eq!(shape.is_none(), n == 26);
        }
    }
    for n in 8..=12 {
        for v in 1..=4 {
            assert!(
                emit("intermediate_small", n, 1, v, 5.min(n - v))
                    .unwrap()
                    .small
            );
        }
    }
    let today = dispatch(25, 7, 2, 10).unwrap();
    assert_eq!(
        (today.prefix_working_set, today.suffix_working_set),
        (39 * MIB, 63 * MIB)
    );
    let shape_d = dispatch(24, 13, 1, 10).unwrap();
    assert_eq!(
        (shape_d.prefix_working_set, shape_d.suffix_working_set),
        (39 * MIB, 59 * MIB)
    );
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
        assert!(emit("invalid", n, c, v, sb).is_none());
    }
    let plan = chunk_plan(25, &[(6, false), (6, false), (5, true)], L2_CHUNK_BYTES).unwrap();
    assert_eq!(
        (
            plan.strips,
            plan.strip_blocks,
            plan.strip_domain_bits,
            plan.passes.len()
        ),
        (32, 1, 5, 3)
    );
    assert_eq!(plan.launches_per_column_group() * 7, 672);
    let plan = chunk_plan(24, &[(6, false), (6, false), (5, true)], L2_CHUNK_BYTES).unwrap();
    assert_eq!(plan.launches_per_column_group() * 13, 624);
    for (a, groups) in [
        (9, None),
        (10, Some("5,5n")),
        (11, Some("6,5n")),
        (12, Some("7,5n")),
        (13, Some("8,5n")),
        (14, Some("8,6")),
        (15, Some("8,7")),
        (16, Some("8,8")),
        (17, Some("6,6,5n")),
        (18, Some("7,6,5n")),
        (19, Some("7,7,5n")),
    ] {
        let text = prefix_groups(a).map(|g| {
            g.iter()
                .map(|&(s, narrow)| format!("{s}{}", if narrow { "n" } else { "" }))
                .collect::<Vec<_>>()
                .join(",")
        });
        assert_eq!(text.as_deref(), groups, "a = {a}");
    }
    println!("shape\tn\tC\tv\tsb\tprefix\ta\tr\ttile_B\ttiles_per_coset\tstrip_domain_bits\tstrip_blocks\tstrips\tper_strip_B\tcols_or_cosets_per_chunk\tprefix_launches_per_column\tprefix_launches_per_coset\tprefix_WS_L33_B\tsuffix_WS_L33_B\tstatus");
    for row in &rows {
        println!("{row}");
    }
    println!(
        "cpu_pr_chunk_plan_closure: {} rows, chunk {} MiB, working set cap {} MiB",
        rows.len(),
        L2_CHUNK_BYTES / MIB,
        L2_WORKING_SET_BYTES / MIB
    );
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

fn full_grid(plan: &ChunkPlan) -> ChunkPlan {
    ChunkPlan {
        cols_per_chunk: usize::MAX,
        strips: 1,
        strip_blocks: 1,
        strip_domain_bits: 0,
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
    let plan = chunk_plan(log_n, groups, L2_CHUNK_BYTES).unwrap();
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
        let shape = dispatch(log_n, columns, log_v, skip_bottom).unwrap();
        let groups: Vec<(u32, bool)> = shape
            .prefix
            .as_ref()
            .unwrap()
            .passes
            .iter()
            .map(|p| (p.stages, p.narrow))
            .collect();
        let plan = prefix_case(&policy, root, log_n, &groups, cols, &mut rng, &stream);
        println!("pr_prefix_chunked_cpu_parity: n {log_n} prefix {} r {} strips {} x {} block-strips (d {}), {} cols, 0 mismatches", groups_text(&plan), shape.r, plan.strips, plan.strip_blocks, plan.strip_domain_bits, cols);
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
    let shape = dispatch(log_n, cols, 2, 10).unwrap();
    let plan = shape.prefix.unwrap();
    let mut input = DeviceAllocation::<PR>::alloc(rows * cols).unwrap();
    let mut output = DeviceAllocation::<PR>::alloc(rows * cols).unwrap();
    unsafe {
        memory_set_async(input.transmute_mut(), 0, &stream).unwrap();
    }
    let policy = DitPolicy(ctx.descriptor());
    let today = chunk_plan(log_n, &[(8, false), (7, false)], L2_CHUNK_BYTES).unwrap();
    let variants = [
        ("prefix.warmup", plan.clone()),
        ("prefix.probe", plan.clone()),
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
    chunk_plan(log_n, &prefix_groups(log_n - 8).unwrap(), L2_CHUNK_BYTES).unwrap()
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
            let plan = reference_plan(log_n);
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
                let scale = ScaleArgs {
                    coset: source,
                    log_domain,
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
                lde_finish_reference(&ctx, &mut candidate, cols, &plan, &stream).unwrap();
                assert!(
                    download(&candidate, &stream) == download(&reference, &stream),
                    "fused scale differs: L {log_max_domain} D {log_domain} n {log_n} k {k}"
                );
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
