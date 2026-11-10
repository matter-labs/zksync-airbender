use std::collections::BTreeSet;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::{memory_copy, memory_copy_async, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::{MutPtrAndStride, PtrAndStride};
use gpu_core::primitives::field::PR;
use rand::{rngs::StdRng, Rng, SeedableRng};

use super::context as pr_twiddles;
use super::hypercube::MobiusPolicy;
use super::lde::{
    launch_transform, set_max_dynamic_smem, ChunkMap, TransformPass, TransformPolicy,
};
use super::prefix::{
    chunk_plan, dispatch, launch_prefix_chunked, narrow_groups, prefix_groups, ChunkPlan,
    CosetSource, PrefixPass, ScaleArgs,
};
use crate::upstream::{domain_generator_for_size, Field};

const MIB: usize = 1 << 20;
const CHUNK_16_MIB: usize = 16 << 20;

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

#[test]
fn cpu_pr_chunk_plan_closure() {
    for (n, c, v, sb) in [
        (24, 12, 1, 10),
        (24, 2, 1, 10),
        (23, 1, 4, 5),
        (19, 1, 4, 5),
        (15, 1, 4, 5),
        (18, 12, 1, 10),
        (18, 2, 1, 10),
        (19, 12, 1, 10),
        (19, 2, 1, 10),
        (20, 12, 1, 10),
    ] {
        for l2_mib in 0..=256 {
            let plan = dispatch(n, c, v, sb, l2_mib * MIB);
            assert!(matches!((plan.r, v), (7, 1) | (8, 1) | (8, 4)));
            let prefix = &plan.prefix;
            if [0, 1, 4, 16, 40, 50, 96, 128].contains(&l2_mib) {
                assert_closure(prefix, false);
            }
        }
    }
    // Diagnostic exhaustive address closure at reduced rows.
    let plan = chunk_plan(16, &[(8, false)], CHUNK_16_MIB).unwrap();
    assert_closure(&plan, true);
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
fn pr_prefix_chunked_mobius_cpu_parity() {
    let stream = CudaStream::create().unwrap();
    let mut rng = StdRng::seed_from_u64(0x9120_3102);
    // Diagnostic wide Mobius prefixes; narrow Mobius is not a wrap route.
    for (log_n, groups, cols) in [
        (16, vec![(8, false)], 12),
        (19, vec![(6, false), (5, false)], 2),
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

fn cpu_coset_prefix(monomials: &[PR], log_n: u32, log_domain: u32, k: u32, stages: u32) -> Vec<PR> {
    let rows = 1usize << log_n;
    let r = log_n - stages;
    let offset = domain_generator_for_size::<PR>(1u64 << log_domain).pow_u128(k as u128);
    let root = domain_generator_for_size::<PR>(1u64 << log_n);
    let mut result = monomials.to_vec();
    for column in result.chunks_exact_mut(rows) {
        let mut power = PR::ONE;
        for value in column.iter_mut() {
            value.mul_assign(&power);
            power.mul_assign(&offset);
        }
        for digit in 0..1usize << r {
            let mut values: Vec<PR> = (0..1usize << stages)
                .map(|block| column[(block << r) + digit])
                .collect();
            cpu_prefix_digit(&mut values, stages, Some((root, log_n)));
            for (block, value) in values.into_iter().enumerate() {
                column[(block << r) + digit] = value;
            }
        }
    }
    result
}

fn scaled_prefix_plan(log_n: u32) -> ChunkPlan {
    let groups = narrow_groups(&prefix_groups(log_n - 8).unwrap());
    chunk_plan(log_n, &groups, CHUNK_16_MIB).unwrap()
}

#[test]
#[cfg(not(no_cuda))]
fn pr_lde_coset_slot_fused_scale_parity() {
    use super::lde_coset_slot;
    let stream = CudaStream::create().unwrap();
    let mut twiddle_tables = DeviceAllocation::<PR>::alloc(pr_twiddles::TABLE_LEN).unwrap();
    let mut twiddle_factors = DeviceAllocation::<PR>::alloc(pr_twiddles::FACTOR_LEN).unwrap();
    let proof_twiddles =
        pr_twiddles::prepare_proof_twiddles(&mut twiddle_tables, &mut twiddle_factors, &stream)
            .unwrap();
    let mut rng = StdRng::seed_from_u64(0x9120_3201);
    // Diagnostic row counts, production column counts; exact CPU oracle.
    for (log_n, cols) in [(19, 12), (19, 2), (15, 1)] {
        let rows = 1usize << log_n;
        let plan = scaled_prefix_plan(log_n);
        let monomials: Vec<PR> = (0..rows * cols)
            .map(|_| PR::new(rng.random::<u128>() % PR::ORDER))
            .collect();
        let device_monomials = upload(&monomials);
        let mut candidate = DeviceAllocation::<PR>::alloc(monomials.len()).unwrap();
        let k = 3;
        let device_k = {
            let mut d = DeviceAllocation::<u32>::alloc(1).unwrap();
            memory_copy(&mut d, &[k]).unwrap();
            d
        };
        let gate = {
            let mut d = DeviceAllocation::<u32>::alloc(1).unwrap();
            memory_copy(&mut d, &[1]).unwrap();
            d
        };
        let expected = cpu_coset_prefix(&monomials, log_n, 31, k, plan.stages());
        for source in [
            CosetSource::Constant(k),
            CosetSource::Slot {
                coset: &device_k,
                active: &gate,
            },
        ] {
            lde_coset_slot(
                proof_twiddles,
                &device_monomials,
                &mut candidate,
                cols,
                &plan,
                ScaleArgs {
                    coset: source,
                    log_domain: 31,
                },
                &stream,
            )
            .unwrap();
            assert_eq!(download(&candidate, &stream), expected);
        }
    }
    let log_n = 15;
    let rows = 1usize << log_n;
    let plan = scaled_prefix_plan(log_n);
    let column: Vec<PR> = (0..rows)
        .map(|_| PR::new(rng.random::<u128>() % PR::ORDER))
        .collect();
    let device_column = upload(&column);
    let mut candidate = DeviceAllocation::<PR>::alloc(rows * 4).unwrap();
    lde_coset_slot(
        proof_twiddles,
        &device_column,
        &mut candidate,
        4,
        &plan,
        ScaleArgs {
            coset: CosetSource::Batched { k0: 3 },
            log_domain: 31,
        },
        &stream,
    )
    .unwrap();
    let expected: Vec<PR> = (3..7)
        .flat_map(|k| cpu_coset_prefix(&column, log_n, 31, k, plan.stages()))
        .collect();
    assert_eq!(download(&candidate, &stream), expected);
}

// Forces the dispatch of smaller devices on this GPU: every plan (resident, smaller strips or
// full grid) gives the same prefix as its coarsest split and the independent CPU network.
#[test]
#[cfg(not(no_cuda))]
fn pr_lde_coset_slot_small_l2_parity() {
    use super::lde_coset_slot;

    let stream = CudaStream::create().unwrap();
    let mut twiddle_tables = DeviceAllocation::<PR>::alloc(pr_twiddles::TABLE_LEN).unwrap();
    let mut twiddle_factors = DeviceAllocation::<PR>::alloc(pr_twiddles::FACTOR_LEN).unwrap();
    let proof_twiddles =
        pr_twiddles::prepare_proof_twiddles(&mut twiddle_tables, &mut twiddle_factors, &stream)
            .unwrap();
    let mut rng = StdRng::seed_from_u64(0x9120_3401);
    let k = 5u32;
    // Diagnostic rows with the production base/setup columns and WHIR fold.
    for (log_n, columns, log_v, skip_bottom, cols) in
        [(19, 12, 1, 10, 12), (19, 2, 1, 10, 2), (15, 1, 4, 5, 1)]
    {
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
        for l2_mib in [0usize, 1, 4, 16, 40, 50, 96, 128] {
            let shape = dispatch(log_n, columns, log_v, skip_bottom, l2_mib * MIB);
            let plan = &shape.prefix;
            lde_coset_slot(
                proof_twiddles,
                &device_monomials,
                &mut candidate,
                cols,
                plan,
                scale,
                &stream,
            )
            .unwrap();
            lde_coset_slot(
                proof_twiddles,
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
            assert_eq!(
                prefix,
                cpu_coset_prefix(&monomials, log_n, 31, k, plan.stages())
            );
            println!(
                "pr_lde_coset_slot_small_l2_parity: ({log_n},{columns},{log_v},{skip_bottom}) L2 {l2_mib} MiB: prefix {} chunk {} MiB resident prefix/suffix {}/{} tiles/batch {}, 0 mismatches",
                groups_text(plan),
                plan.chunk_bytes() / MIB,
                shape.prefix_resident,
                shape.suffix_resident,
                shape.tiles_per_batch
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
    // Diagnostic row count with the production base columns.
    for (log_n, cols) in [(19, 12)] {
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
