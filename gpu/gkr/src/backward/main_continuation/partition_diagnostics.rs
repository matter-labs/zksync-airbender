//! Feature-only offline partitions; all enqueue-time state is ordinary host memory.
//! CUDA events enclose the full fold/evaluation sequence and tensor reduction.
use super::*;
use crate::backward::window::tail::{WindowTailReduceArguments, WindowTailReduceFunction};
use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::memory::{memory_copy_async, memory_set_async};
use era_cudart::slice::DeviceSlice;
use gpu_core::primitives::context::DeviceAllocation;
use std::{
    cell::{Cell, RefCell},
    collections::BTreeSet,
    io::Write,
};

era_cudart::cuda_kernel!(PartitionDynamic, ab_gkr_main_cont_partition_dynamic(desc: MainContinuationWindowLaunchBinding, fold_count: u32));
era_cudart::cuda_kernel!(PartitionStatic, ab_gkr_main_cont_partition_static(desc: MainContinuationWindowLaunchBinding, fold_count: u32));
era_cudart::cuda_kernel!(PartitionPaired, ab_gkr_main_cont_partition_paired(desc: MainContinuationWindowLaunchBinding, fold_count: u32));
era_cudart::cuda_kernel!(PartitionCheck, ab_gkr_main_cont_partition_check(expected: *const E4, parts: *const E4, cells: u32, partitions: u32, status: *mut u32));
era_cudart::cuda_kernel!(Compare, ab_gkr_main_cont_fused_compare(expected: *const u32, actual: *const u32, limbs: u32, status: *mut u32, inject: u32));

struct Plan {
    layer: usize,
    round: usize,
    words: Vec<u16>,
    bytes: Vec<usize>,
    ranges: Vec<Vec<(usize, usize)>>,
}
struct Sample {
    plan_index: usize,
    iteration: usize,
    position: usize,
    candidate: bool,
    start: CudaEvent,
    end: CudaEvent,
}
struct State {
    plans: Vec<Plan>,
    coordinate: Option<(usize, usize)>,
    checked: Vec<bool>,
    pairs: usize,
    warmups: usize,
    proof_only: bool,
    status: DeviceAllocation<u32>,
    samples: Vec<Sample>,
    output: Option<String>,
    session: usize,
    identical: bool,
}
thread_local! { static STATE: RefCell<Option<State>> = const { RefCell::new(None) }; }

thread_local! {
    static PRODUCTION_OVERRIDE: Cell<Option<bool>> = const { Cell::new(None) };
    static PRODUCTION_COORDINATE: Cell<Option<(usize, usize)>> = const { Cell::new(None) };
    static PRODUCTION_CENSUS: RefCell<Vec<(usize, usize, usize, usize, u16)>> = const { RefCell::new(Vec::new()) };
}

pub fn set_production_override(enabled: bool) {
    PRODUCTION_OVERRIDE.with(|s| assert!(s.replace(Some(enabled)).is_none()));
    PRODUCTION_CENSUS.with_borrow(|s| assert!(s.is_empty()));
}

pub(super) fn production_enabled() -> bool {
    PRODUCTION_OVERRIDE.with(|s| s.get().unwrap_or(true))
}

pub(super) fn discard_production_coordinate() {
    PRODUCTION_COORDINATE.with(|s| s.set(None));
}

pub(super) fn record_production(k: usize, tiles: usize, words: u16) {
    if let Some((layer, round)) = PRODUCTION_COORDINATE.with(|s| s.take()) {
        PRODUCTION_CENSUS.with_borrow_mut(|s| s.push((layer, round, k, tiles, words)));
    }
}

pub fn finish_production_override() {
    let enabled = PRODUCTION_OVERRIDE
        .with(|s| s.take())
        .expect("active production comparison");
    assert!(PRODUCTION_COORDINATE.with(|s| s.get()).is_none());
    let census = PRODUCTION_CENSUS.with_borrow_mut(std::mem::take);
    assert!(!census.is_empty());
    for (layer, round, k, tiles, words) in &census {
        if !enabled {
            assert_eq!(*k, 1);
        }
        eprintln!("PRODUCTION_CONT layer={layer} round={round} k={k} tiles={tiles} words={words}");
    }
    eprintln!(
        "PRODUCTION_CONT_GATE enabled={enabled} coordinates={} partitioned={}",
        census.len(),
        census.iter().filter(|r| r.2 > 1).count()
    );
}

// Allocate aggregate status before prove(), preserving its balanced-allocation
// contract. Atomic OR keeps any failure sticky across all selected coordinates.
struct ProductionChecks {
    status: DeviceAllocation<u32>,
    checked: usize,
}
thread_local! {
    static PRODUCTION_CHECKS: RefCell<Option<ProductionChecks>> = const { RefCell::new(None) };
}

pub(super) fn validate_production(
    launch: &MainContinuationWindowLaunch<'_>,
    plan: &gpu_gkr_compiler::MainContinuationPartitionPlan,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<E4>> {
    let k = plan.parts.len();
    let cells = launch.row_tiles * 27;
    let pub_cells = launch.published.shape().columns * launch.published.shape().column_elems;
    let stream = context.get_exec_stream();
    let mut partials = context.alloc::<E4>(k * cells, AllocationPlacement::Top)?;
    let mut reference = context.alloc::<E4>(pub_cells + cells + 27, AllocationPlacement::Top)?;
    let status = PRODUCTION_CHECKS.with_borrow_mut(|s| {
        let s = s
            .as_mut()
            .expect("production validation initialized before prove");
        s.checked += 1;
        s.status.as_mut_ptr()
    });
    // SAFETY: all spans refer to live allocations, with sizes derived from their shapes.
    unsafe {
        baseline(launch, context)?;
        reduce(
            launch.binding.partials,
            launch.row_tiles,
            launch.reduced_tensor,
            context,
        )?;
        memory_copy_async(
            &mut reference[..pub_cells],
            DeviceSlice::from_raw_parts(launch.published.as_ptr(), pub_cells),
            stream,
        )?;
        memory_copy_async(
            &mut reference[pub_cells..pub_cells + cells],
            DeviceSlice::from_raw_parts(launch.binding.partials, cells),
            stream,
        )?;
        memory_copy_async(
            &mut reference[pub_cells + cells..],
            DeviceSlice::from_raw_parts(launch.reduced_tensor, 27),
            stream,
        )?;
        memory_set_async(
            DeviceSlice::from_raw_parts_mut(launch.published.as_ptr() as *mut u8, pub_cells * 16),
            0xa5,
            stream,
        )?;
        memory_set_async(
            DeviceSlice::from_raw_parts_mut(partials.as_mut_ptr().cast::<u8>(), k * cells * 16),
            0xa5,
            stream,
        )?;
        // Exactly the production descriptor construction and existing kernel entries.
        partition::enqueue(launch, plan, partials.as_mut_ptr(), context)?;
        reduce(
            partials.as_ptr(),
            k * launch.row_tiles,
            launch.reduced_tensor,
            context,
        )?;
        compare(
            reference.as_ptr(),
            launch.published.as_ptr(),
            pub_cells,
            status,
            0,
            context,
        )?;
        PartitionCheckFunction::default().launch(
            &CudaLaunchConfig::basic((cells as u32).div_ceil(256), 256, stream),
            &PartitionCheckArguments::new(
                reference.as_ptr().add(pub_cells),
                partials.as_ptr(),
                cells as u32,
                k as u32,
                status.add(1),
            ),
        )?;
        compare(
            reference.as_ptr().add(pub_cells + cells),
            launch.reduced_tensor,
            27,
            status.add(2),
            0,
            context,
        )?;
        compare(
            reference.as_ptr().add(pub_cells + cells),
            launch.reduced_tensor,
            27,
            status.add(3),
            1,
            context,
        )?;
    }
    Ok(partials)
}

fn finish_production_checks(context: &ProverContext) -> CudaResult<()> {
    let Some(checks) = PRODUCTION_CHECKS.with_borrow_mut(Option::take) else {
        return Ok(());
    };
    assert!(checks.checked > 0);
    let mut flags = [0u32; 4];
    memory_copy_async(
        &mut flags[..],
        &checks.status[..],
        context.get_exec_stream(),
    )?;
    context.get_exec_stream().synchronize()?;
    assert_eq!(
        flags,
        [0, 0, 0, 1],
        "production publication/partials/tensor/negative gates"
    );
    eprintln!("PRODUCTION_TENSOR_GATE checked={} publication_partials_tensor_poison_negative=passed candidate_feeds_proof=true", checks.checked);
    Ok(())
}

fn read_plan(file: &str, layer: usize, round: usize) -> Plan {
    let text = std::fs::read_to_string(file).unwrap();
    let mut lines = text.lines();
    assert_eq!(lines.next(), Some("MAIN_CONT_PARTITIONS_V1"));
    let words = lines
        .next()
        .unwrap()
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let bytes = lines
        .next()
        .unwrap()
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let ranges: Vec<Vec<(usize, usize)>> = lines
        .map(|line| {
            line.split_whitespace()
                .map(|r| {
                    let (a, b) = r.split_once(':').unwrap();
                    (a.parse().unwrap(), b.parse().unwrap())
                })
                .collect()
        })
        .collect();
    assert!([1, 2, 4, 8].contains(&ranges.len()));
    assert!(ranges.iter().all(|p| !p.is_empty()));
    Plan {
        layer,
        round,
        words,
        bytes,
        ranges,
    }
}
pub fn begin_from_env(context: &ProverContext) -> CudaResult<()> {
    if std::env::var_os("AB_CONT_PARTITION_PRODUCTION_VALIDATE").is_some() {
        let mut status = context.alloc::<u32>(4, AllocationPlacement::Top)?;
        // SAFETY: the byte span covers the four live status words.
        let bytes =
            unsafe { DeviceSlice::from_raw_parts_mut(status.as_mut_ptr().cast::<u8>(), 16) };
        memory_set_async(bytes, 0, context.get_exec_stream())?;
        PRODUCTION_CHECKS.with_borrow_mut(|s| {
            assert!(s.replace(ProductionChecks { status, checked: 0 }).is_none())
        });
    }
    let plans: Vec<_> = if let Ok(file) = std::env::var("AB_CONT_PARTITION_MANIFEST") {
        std::fs::read_to_string(file)
            .unwrap()
            .lines()
            .filter(|s| !s.is_empty())
            .map(|line| {
                let mut fields = line.split_whitespace();
                let layer = fields.next().unwrap().parse().unwrap();
                let round = fields.next().unwrap().parse().unwrap();
                let path = fields.next().unwrap();
                assert!(fields.next().is_none());
                read_plan(path, layer, round)
            })
            .collect()
    } else if let Ok(file) = std::env::var("AB_CONT_PARTITION_PLAN") {
        vec![read_plan(&file, 0, 3)]
    } else {
        return Ok(());
    };
    assert!(!plans.is_empty());
    assert!(std::env::var_os("AB_CONT_FUSION_VALIDATE").is_none());
    let mut unique = BTreeSet::new();
    for p in &plans {
        assert!(unique.insert((p.layer, p.round, p.ranges.len())));
    }
    let mut status = context.alloc::<u32>(4 * plans.len(), AllocationPlacement::Top)?;
    // SAFETY: byte span covers the complete live status allocation.
    let bytes = unsafe {
        DeviceSlice::from_raw_parts_mut(status.as_mut_ptr().cast::<u8>(), 16 * plans.len())
    };
    memory_set_async(bytes, 0, context.get_exec_stream())?;
    let state = State {
        checked: vec![false; plans.len()],
        plans,
        coordinate: None,
        status,
        samples: Vec::new(),
        output: std::env::var("AB_CONT_PARTITION_OUTPUT").ok(),
        session: std::env::var("AB_CONT_PARTITION_SESSION")
            .unwrap_or("0".into())
            .parse()
            .unwrap(),
        identical: std::env::var_os("AB_CONT_PARTITION_IDENTICAL").is_some(),
        pairs: std::env::var("AB_CONT_PARTITION_PAIRS")
            .unwrap_or("24".into())
            .parse()
            .unwrap(),
        warmups: std::env::var("AB_CONT_PARTITION_WARMUPS")
            .unwrap_or("5".into())
            .parse()
            .unwrap(),
        proof_only: std::env::var_os("AB_CONT_PARTITION_PROOF_ONLY").is_some(),
    };
    assert!(state.pairs > 0);
    assert!(!state.proof_only || state.output.is_none());
    STATE.with_borrow_mut(|s| assert!(s.replace(state).is_none()));
    Ok(())
}
pub(crate) fn set_coordinate(layer: usize, round: usize) {
    if PRODUCTION_OVERRIDE.with(|s| s.get().is_some()) {
        PRODUCTION_COORDINATE.with(|s| assert!(s.replace(Some((layer, round))).is_none()));
    }
    STATE.with_borrow_mut(|s| {
        if let Some(s) = s {
            assert!(s.coordinate.replace((layer, round)).is_none())
        }
    });
}

fn descriptors(
    launch: &MainContinuationWindowLaunch<'_>,
    plan: &Plan,
    partials: *mut E4,
) -> Vec<MainContinuationWindowLaunchBinding> {
    let base = &*launch.binding;
    assert_eq!(base.program[..base.program_words as usize], plan.words);
    assert_eq!(base.source_count as usize, plan.bytes.len());
    assert_eq!(launch.publish_kernel.0.mask & !0x1f, 0);
    // Parse the original atom boundaries independently of the retained assignment.
    let mut boundaries = BTreeSet::new();
    let mut i = 0;
    while i < plan.words.len() {
        let start = i;
        let cls = plan.words[i] >> 13;
        if cls == 2 {
            i += 3 * (1 + plan.words[i + 1] as usize)
        } else {
            assert!(cls <= 1);
            i += 3
        }
        assert!(i <= plan.words.len());
        boundaries.insert((start, i));
    }
    let mut assigned = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for (part, ranges) in plan.ranges.iter().enumerate() {
        let mut desc = *base;
        desc.program.fill(0);
        let mut words = Vec::new();
        let mut sources = BTreeSet::new();
        for &(start, end) in ranges {
            assert!(boundaries.contains(&(start, end)) && assigned.insert((start, end)));
            words.extend_from_slice(&plan.words[start..end]);
            let mut at = start;
            while at < end {
                let cls = plan.words[at] >> 13;
                if cls != 2 {
                    sources.insert(plan.words[at + 1]);
                    if cls == 1 {
                        sources.insert(plan.words[at + 2]);
                    }
                }
                at += 3;
            }
        }
        assert!(sources.iter().all(|s| *s < base.source_count));
        desc.program[..words.len()].copy_from_slice(&words);
        desc.program_words = words.len() as u16;
        if part > 0 {
            desc.c_init_coeff = BWD_COEFF_NONE;
        }
        // SAFETY: caller owns K disjoint row_tiles*27 banks until all consumers are scheduled.
        desc.partials = unsafe { partials.add(part * launch.row_tiles * 27) };
        let mut owned: Vec<_> = sources.difference(&seen).copied().collect();
        seen.extend(sources);
        owned.sort_by_key(|s| {
            (
                std::cmp::Reverse(if launch.canonical_input {
                    16
                } else {
                    plan.bytes[*s as usize].max(1)
                }),
                *s,
            )
        });
        let mut loads = [0usize; 9];
        let mut lists: [Vec<u16>; 9] = std::array::from_fn(|_| Vec::new());
        for s in owned {
            let warp = (0..9).min_by_key(|q| (loads[*q], *q)).unwrap();
            loads[warp] += if launch.canonical_input {
                16
            } else {
                plan.bytes[s as usize].max(1)
            };
            lists[warp].push(s);
        }
        desc.fold_list_offsets.fill(0);
        desc.fold_sources.fill(0);
        let mut offset = 0;
        for (q, list) in lists.iter().enumerate() {
            desc.fold_sources[offset..offset + list.len()].copy_from_slice(list);
            offset += list.len();
            desc.fold_list_offsets[q + 1] = offset as u16;
        }
        out.push(desc);
    }
    assert_eq!(assigned, boundaries);
    assert_eq!(seen.len(), base.source_count as usize);
    out
}

fn baseline(launch: &MainContinuationWindowLaunch<'_>, context: &ProverContext) -> CudaResult<()> {
    let sm = context.get_device_properties().sm_count;
    let words = launch.binding.program_words as usize;
    let paired = main_continuation_use_paired(sm, words, launch.row_tiles);
    let fused = paired
        || launch.row_tiles
            >= main_continuation_launch_min_tiles(sm, words, launch.canonical_input);
    let args = GkrBwdMainContinuationWindow3Arguments::new(*launch.binding);
    let stream = context.get_exec_stream();
    if fused {
        let kernel = if paired {
            MainContinuationWindowEvaluatorKernel(ab_gkr_main_cont_operand_1f_b2)
        } else {
            launch.fused_kernel
        };
        kernel.launch(
            &CudaLaunchConfig::basic(launch.row_tiles as u32, 288, stream),
            &args,
        )
    } else {
        launch.publish_kernel.launch(
            &CudaLaunchConfig::basic(
                launch.publication_grid_blocks,
                MAIN_CONTINUATION_WINDOW_PUBLICATION_THREADS,
                stream,
            ),
            &args,
        )?;
        launch.kernel.launch(
            &CudaLaunchConfig::basic(
                launch.grid_blocks,
                MAIN_CONTINUATION_WINDOW_BLOCK_THREADS,
                stream,
            ),
            &args,
        )
    }
}
fn candidate(
    descs: &[MainContinuationWindowLaunchBinding],
    static_x0: bool,
    paired: bool,
    context: &ProverContext,
) -> CudaResult<()> {
    for desc in descs {
        let config = CudaLaunchConfig::basic(desc.row_tiles, 288, context.get_exec_stream());
        let count = desc.fold_list_offsets[9] as u32;
        if paired {
            PartitionPairedFunction::default()
                .launch(&config, &PartitionPairedArguments::new(*desc, count))?;
        } else if static_x0 {
            PartitionStaticFunction::default()
                .launch(&config, &PartitionStaticArguments::new(*desc, count))?;
        } else {
            PartitionDynamicFunction::default()
                .launch(&config, &PartitionDynamicArguments::new(*desc, count))?;
        }
    }
    Ok(())
}
fn reduce(
    input: *const E4,
    tiles: usize,
    output: *mut E4,
    context: &ProverContext,
) -> CudaResult<()> {
    WindowTailReduceFunction::default().launch(
        &CudaLaunchConfig::basic(27, 256, context.get_exec_stream()),
        &WindowTailReduceArguments::new(input, u32::try_from(tiles).unwrap(), output),
    )
}
fn compare(
    expected: *const E4,
    actual: *const E4,
    cells: usize,
    status: *mut u32,
    inject: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let limbs = u32::try_from(cells * 4).unwrap();
    CompareFunction::default().launch(
        &CudaLaunchConfig::basic(limbs.div_ceil(256), 256, context.get_exec_stream()),
        &CompareArguments::new(expected.cast(), actual.cast(), limbs, status, inject),
    )
}

pub(super) fn schedule(
    launch: &MainContinuationWindowLaunch<'_>,
    context: &ProverContext,
) -> CudaResult<Option<DeviceAllocation<E4>>> {
    if launch.binding.publication_fold != 3 {
        return Ok(None);
    }
    STATE.with_borrow_mut(|state| {
        let Some(s) = state else { return Ok(None) };
        let (layer, round) = s.coordinate.take().expect("partition coordinate");
        let matching: Vec<_> = s
            .plans
            .iter()
            .enumerate()
            .filter(|(_, p)| (p.layer, p.round) == (layer, round))
            .map(|(i, _)| i)
            .collect();
        let mut last = None;
        for plan_index in matching {
            assert!(!s.checked[plan_index]);
            last = Some(run_plan(s, plan_index, layer, round, launch, context)?);
        }
        Ok(last)
    })
}
fn run_plan(
    s: &mut State,
    plan_index: usize,
    layer: usize,
    round: usize,
    launch: &MainContinuationWindowLaunch<'_>,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<E4>> {
    let k = s.plans[plan_index].ranges.len();
    let cells = launch.row_tiles * 27;
    let stream = context.get_exec_stream();
    let mut partials = context.alloc::<E4>(k * cells, AllocationPlacement::Top)?;
    let descs = descriptors(launch, &s.plans[plan_index], partials.as_mut_ptr());
    let paired = main_continuation_use_paired(
        context.get_device_properties().sm_count,
        launch.binding.program_words as usize,
        launch.row_tiles,
    );
    let static_x0 = !paired && use_fused_x01_specialization(launch.binding.program_words as usize);
    let pub_cells = launch.published.shape().columns * launch.published.shape().column_elems;
    eprintln!("PARTITION_POLICY_ENQUEUE plan={plan_index} layer={layer} round={round} k={k} mask={:02x} words={} sources={} tiles={} publication_cells={pub_cells} partial_cells={} static_x0={static_x0} paired={paired} identical={}",launch.publish_kernel.0.mask,launch.binding.program_words,launch.binding.source_count,launch.row_tiles,k*cells,s.identical);
    if s.proof_only {
        candidate(&descs, static_x0, paired, context)?;
        s.checked[plan_index] = true;
        return Ok(partials);
    }
    let mut reference = context.alloc::<E4>(pub_cells + cells + 27, AllocationPlacement::Top)?;
    // SAFETY: all pointer spans belong to live allocations owned by launch or this call.
    let published =
        unsafe { DeviceSlice::from_raw_parts_mut(launch.published.as_ptr() as *mut E4, pub_cells) };
    let base_partials = unsafe { DeviceSlice::from_raw_parts(launch.binding.partials, cells) };
    let tensor = unsafe { DeviceSlice::from_raw_parts(launch.reduced_tensor, 27) };
    baseline(launch, context)?;
    reduce(
        launch.binding.partials,
        launch.row_tiles,
        launch.reduced_tensor,
        context,
    )?;
    memory_copy_async(&mut reference[..pub_cells], published, stream)?;
    memory_copy_async(
        &mut reference[pub_cells..pub_cells + cells],
        base_partials,
        stream,
    )?;
    memory_copy_async(&mut reference[pub_cells + cells..], tensor, stream)?;
    // Poison every publication and partition output word before the first candidate.
    let published_words = unsafe {
        DeviceSlice::from_raw_parts_mut(published.as_mut_ptr().cast::<u8>(), pub_cells * 16)
    };
    let partial_words = unsafe {
        DeviceSlice::from_raw_parts_mut(partials.as_mut_ptr().cast::<u8>(), k * cells * 16)
    };
    memory_set_async(published_words, 0xa5, stream)?;
    memory_set_async(partial_words, 0xa5, stream)?;
    candidate(&descs, static_x0, paired, context)?;
    reduce(
        partials.as_ptr(),
        k * launch.row_tiles,
        launch.reduced_tensor,
        context,
    )?;
    // SAFETY: each plan owns four status words.
    let status = unsafe { s.status.as_mut_ptr().add(4 * plan_index) };
    compare(
        reference.as_ptr(),
        published.as_ptr(),
        pub_cells,
        status,
        0,
        context,
    )?;
    // SAFETY: reference is [publication | original partials | reduced tensor], status has four words.
    unsafe {
        PartitionCheckFunction::default().launch(
            &CudaLaunchConfig::basic((cells as u32).div_ceil(256), 256, stream),
            &PartitionCheckArguments::new(
                reference.as_ptr().add(pub_cells),
                partials.as_ptr(),
                cells as u32,
                k as u32,
                status.add(1),
            ),
        )?;
        compare(
            reference.as_ptr().add(pub_cells + cells),
            launch.reduced_tensor,
            27,
            status.add(2),
            0,
            context,
        )?;
        compare(
            reference.as_ptr().add(pub_cells + cells),
            launch.reduced_tensor,
            27,
            status.add(3),
            1,
            context,
        )?;
    }
    if s.output.is_some() {
        let enqueue = |arm: bool| -> CudaResult<()> {
            if arm && !s.identical {
                candidate(&descs, static_x0, paired, context)?;
                reduce(
                    partials.as_ptr(),
                    k * launch.row_tiles,
                    launch.reduced_tensor,
                    context,
                )
            } else {
                baseline(launch, context)?;
                reduce(
                    launch.binding.partials,
                    launch.row_tiles,
                    launch.reduced_tensor,
                    context,
                )
            }
        };
        for _ in 0..s.warmups {
            enqueue(false)?;
            enqueue(true)?;
        }
        for iteration in 0..s.pairs {
            let order = if (iteration + s.session) % 2 == 0 {
                [false, true]
            } else {
                [true, false]
            };
            for (position, arm) in order.into_iter().enumerate() {
                let start = CudaEvent::create()?;
                let end = CudaEvent::create()?;
                start.record(stream)?;
                enqueue(arm)?;
                end.record(stream)?;
                s.samples.push(Sample {
                    plan_index,
                    iteration,
                    position,
                    candidate: arm,
                    start,
                    end,
                });
            }
        }
    }
    // Candidate publication and all K partial banks feed the ordinary tail/transcript.
    candidate(&descs, static_x0, paired, context)?;
    s.checked[plan_index] = true;
    Ok(partials)
}
pub fn finish(context: &ProverContext) -> CudaResult<()> {
    finish_production_checks(context)?;
    let Some(s) = STATE.with_borrow_mut(Option::take) else {
        return Ok(());
    };
    assert!(
        s.checked.iter().all(|b| *b),
        "missing partition coordinates"
    );
    assert!(s.coordinate.is_none());
    if !s.proof_only {
        let mut status = vec![0u32; s.status.len()];
        memory_copy_async(&mut status[..], &s.status[..], context.get_exec_stream())?;
        context.get_exec_stream().synchronize()?;
        for (i, flags) in status.chunks_exact(4).enumerate() {
            assert_eq!(flags, [0, 0, 0, 1], "partition gate plan {i}");
        }
    }
    if let Some(path) = s.output {
        assert_eq!(s.samples.len(), 2 * s.pairs * s.plans.len());
        let mut file = std::fs::File::create(path).unwrap();
        writeln!(file, "session,plan,layer,round,k,iteration,position,arm,ms").unwrap();
        let mut census = vec![0; s.plans.len()];
        for sample in s.samples {
            census[sample.plan_index] += 1;
            let p = &s.plans[sample.plan_index];
            writeln!(
                file,
                "{},{},{},{},{},{},{},{},{:.9}",
                s.session,
                sample.plan_index,
                p.layer,
                p.round,
                p.ranges.len(),
                sample.iteration,
                sample.position,
                if sample.candidate {
                    "candidate"
                } else {
                    "baseline"
                },
                elapsed_time(&sample.start, &sample.end)?
            )
            .unwrap();
        }
        assert!(census.into_iter().all(|n| n == 2 * s.pairs));
    }
    eprintln!("PARTITION_POLICY_GATE checked={} proof_only={} publication_partials_tensor_poison_negative={} candidate_feeds_proof=true",s.plans.len(),s.proof_only,if s.proof_only {"skipped"} else {"passed"});
    Ok(())
}
