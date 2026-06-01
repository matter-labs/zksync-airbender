use super::super::super::{GpuBaseFieldSourceKind, GpuExtensionFieldPolyContinuingSourcePlan};
use super::super::kernels::GpuGKRMainLayerKernelKind;
use super::*;
use crate::allocator::tracker::AllocationPlacement;

use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::{BF, E4};
use crate::prover::test_utils::make_test_context;
use crate::prover::ProverContext;
use crate::upstream::Field;
use era_cudart::memory::memory_copy_async;
use serial_test::serial;

fn sample_ext(seed: u32) -> E4 {
    E4::from_array_of_base([
        BF::new(seed),
        BF::new(seed + 1),
        BF::new(seed + 2),
        BF::new(seed + 3),
    ])
}

fn alloc_and_copy<T: Copy>(context: &ProverContext, values: &[T]) -> DeviceAllocation<T> {
    let mut allocation = context
        .alloc(values.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut allocation, values, context.get_exec_stream()).unwrap();
    allocation
}

fn cont_source(cache_ptr: *mut E4) -> GpuExtensionFieldPolyContinuingSourcePlan<E4> {
    GpuExtensionFieldPolyContinuingSourcePlan {
        previous_layer_start: std::ptr::null(),
        this_layer_start: cache_ptr,
        this_layer_size: 0,
        next_layer_size: 0,
        first_access: false,
    }
}

fn build_round1_desc_from_plan(
    plan: &FlatContinuationBuildPlan<E4>,
    base_sources: &[Vec<GpuFlatBaseAfterOneSourceEntry>],
    ext_sources: &[Vec<GpuFlatContinuingSourceEntry>],
) -> Round1FusedSources {
    let mut desc = Round1FusedSources::default();
    let mut base_count = 0u32;
    let mut ext_count = 0u32;
    const UNASSIGNED: u16 = u16::MAX;
    let mut idx_remap = vec![UNASSIGNED; plan.term_desc.num_sources as usize];

    for assignment in &plan.source_assignments {
        let remap_slot = &mut idx_remap[assignment.source_table_idx as usize];
        if *remap_slot != UNASSIGNED {
            continue;
        }
        if assignment.is_ext {
            let src = &ext_sources[assignment.gate_idx][assignment.input_idx];
            let tagged_idx = ext_count as u16 | FLAT_CONT_EXT_SOURCE_BIT;
            *remap_slot = tagged_idx;
            desc.ext_sources[ext_count as usize] = *src;
            ext_count += 1;
        } else {
            let src = &base_sources[assignment.gate_idx][assignment.input_idx];
            let tagged_idx = base_count as u16;
            *remap_slot = tagged_idx;
            desc.base_sources[base_count as usize] = *src;
            base_count += 1;
        }
    }
    desc.num_base_sources = base_count;
    desc.num_ext_sources = ext_count;
    desc.idx_remap = idx_remap;
    desc
}

fn build_round2_desc_from_plan(
    plan: &FlatContinuationBuildPlan<E4>,
    base_sources: &[Vec<GpuFlatBaseAfterTwoSourceEntry>],
    ext_sources: &[Vec<GpuFlatContinuingSourceEntry>],
) -> Round2FusedSources {
    let mut desc = Round2FusedSources::default();
    let mut base_count = 0u32;
    let mut ext_count = 0u32;
    const UNASSIGNED: u16 = u16::MAX;
    let mut idx_remap = vec![UNASSIGNED; plan.term_desc.num_sources as usize];

    for assignment in &plan.source_assignments {
        let remap_slot = &mut idx_remap[assignment.source_table_idx as usize];
        if *remap_slot != UNASSIGNED {
            continue;
        }
        if assignment.is_ext {
            let src = &ext_sources[assignment.gate_idx][assignment.input_idx];
            let tagged_idx = ext_count as u16 | FLAT_CONT_EXT_SOURCE_BIT;
            *remap_slot = tagged_idx;
            desc.ext_sources[ext_count as usize] = *src;
            ext_count += 1;
        } else {
            let src = &base_sources[assignment.gate_idx][assignment.input_idx];
            let tagged_idx = base_count as u16;
            *remap_slot = tagged_idx;
            desc.base_sources[base_count as usize] = *src;
            base_count += 1;
        }
    }
    desc.num_base_sources = base_count;
    desc.num_ext_sources = ext_count;
    desc.idx_remap = idx_remap;
    desc
}

#[test]
fn flat_round1_source_remap_sanity() {
    let base_cache = [E4::ZERO; 1];
    let ext_cache = [E4::ZERO; 1];
    let base_inputs = [cont_source(base_cache.as_ptr() as *mut E4)];
    let ext_inputs = [cont_source(ext_cache.as_ptr() as *mut E4)];
    let gate = PreparedGateForFlatContinuationPlan {
        kind: GpuGKRMainLayerKernelKind::MaskIdentity,
        gate_idx: 0,
        base_inputs: &base_inputs,
        ext_inputs: &ext_inputs,
        batch_challenge_power_offset: 0,
        constraint_source: None,
    };
    let plan = build_flat_continuation_plan(&[gate]);
    let base_sources = vec![vec![GpuFlatBaseAfterOneSourceEntry {
        base_layer_half_size: 4,
        next_layer_size: 2,
        base_input_start: std::ptr::null(),
        this_layer_cache_start: base_cache.as_ptr() as *mut u8,
        first_access: true,
        source_kind: GpuBaseFieldSourceKind::Real,
    }]];
    let ext_sources = vec![vec![GpuFlatContinuingSourceEntry {
        previous_layer_start: std::ptr::null(),
        this_layer_cache_start: ext_cache.as_ptr() as *mut u8,
    }]];
    let desc = build_round1_desc_from_plan(&plan, &base_sources, &ext_sources);
    assert_eq!(desc.num_base_sources, 1);
    assert_eq!(desc.num_ext_sources, 1);
    // 2 continuation sources (one base, one ext) map to {0, FLAT_CONT_EXT_SOURCE_BIT}.
    let mut tags: Vec<u16> = desc.idx_remap.clone();
    tags.sort();
    assert_eq!(tags, vec![0u16, FLAT_CONT_EXT_SOURCE_BIT]);
}

#[test]
fn flat_round2_source_remap_sanity() {
    let base_cache = [E4::ZERO; 1];
    let ext_cache = [E4::ZERO; 1];
    let base_inputs = [cont_source(base_cache.as_ptr() as *mut E4)];
    let ext_inputs = [cont_source(ext_cache.as_ptr() as *mut E4)];
    let gate = PreparedGateForFlatContinuationPlan {
        kind: GpuGKRMainLayerKernelKind::MaskIdentity,
        gate_idx: 0,
        base_inputs: &base_inputs,
        ext_inputs: &ext_inputs,
        batch_challenge_power_offset: 0,
        constraint_source: None,
    };
    let plan = build_flat_continuation_plan(&[gate]);
    let base_sources = vec![vec![GpuFlatBaseAfterTwoSourceEntry {
        base_input_start: std::ptr::null(),
        this_layer_cache_start: base_cache.as_ptr() as *mut u8,
        base_layer_half_size: 4,
        base_quarter_size: 2,
        next_layer_size: 1,
        first_access: true,
        source_kind: GpuBaseFieldSourceKind::Real,
    }]];
    let ext_sources = vec![vec![GpuFlatContinuingSourceEntry {
        previous_layer_start: std::ptr::null(),
        this_layer_cache_start: ext_cache.as_ptr() as *mut u8,
    }]];
    let desc = build_round2_desc_from_plan(&plan, &base_sources, &ext_sources);
    assert_eq!(desc.num_base_sources, 1);
    assert_eq!(desc.num_ext_sources, 1);
    // 2 continuation sources (one base, one ext) map to {0, FLAT_CONT_EXT_SOURCE_BIT}.
    let mut tags: Vec<u16> = desc.idx_remap.clone();
    tags.sort();
    assert_eq!(tags, vec![0u16, FLAT_CONT_EXT_SOURCE_BIT]);
}

// End-to-end coverage of the round-0 kernel gate kinds runs through
// the compact-path stagewise/multi-schedule parity tests
// (`run_basic_unrolled_*`).

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn flat_continuation_remap_tags_sources() {
    let context = make_test_context(64, 8);

    let shared: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
    let base_inputs = vec![GpuExtensionFieldPolyContinuingSourcePlan {
        previous_layer_start: shared.as_ptr(),
        this_layer_start: shared.as_ptr().cast_mut(),
        this_layer_size: 0,
        next_layer_size: 0,
        first_access: true,
    }];
    let ext_inputs = vec![GpuExtensionFieldPolyContinuingSourcePlan {
        previous_layer_start: shared.as_ptr(),
        this_layer_start: shared.as_ptr().cast_mut(),
        this_layer_size: 0,
        next_layer_size: 0,
        first_access: true,
    }];

    let gate = PreparedGateForFlatContinuationPlan {
        kind: GpuGKRMainLayerKernelKind::MaskIdentity,
        gate_idx: 0,
        base_inputs: &base_inputs,
        ext_inputs: &ext_inputs,
        batch_challenge_power_offset: 0,
        constraint_source: None,
    };
    let plan = build_flat_continuation_plan(&[gate]);
    assert_eq!(plan.term_desc.num_sources, 2, "remap: base/ext dedup");

    let base_values: Vec<BF> = (0..8).map(|i| BF::new(5 + i)).collect();
    let ext_values: Vec<E4> = (0..8).map(|i| sample_ext(900 + i)).collect();
    let base_input_dev = alloc_and_copy(&context, &base_values);
    let ext_prev_dev = alloc_and_copy(&context, &ext_values);
    let base_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
    let ext_cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

    let round1_desc = build_round1_desc_from_plan(
        &plan,
        &[vec![GpuFlatBaseAfterOneSourceEntry {
            base_layer_half_size: 4,
            next_layer_size: 2,
            base_input_start: base_input_dev.as_ptr().cast(),
            this_layer_cache_start: base_cache.as_ptr().cast_mut().cast(),
            first_access: true,
            source_kind: GpuBaseFieldSourceKind::Real,
        }]],
        &[vec![GpuFlatContinuingSourceEntry {
            previous_layer_start: ext_prev_dev.as_ptr().cast(),
            this_layer_cache_start: ext_cache.as_ptr().cast_mut().cast(),
        }]],
    );
    assert_eq!(round1_desc.num_base_sources, 1);
    assert_eq!(round1_desc.num_ext_sources, 1);
    let mut round1_tags: Vec<u16> = round1_desc.idx_remap.clone();
    round1_tags.sort();
    assert_eq!(round1_tags, vec![0u16, FLAT_CONT_EXT_SOURCE_BIT]);

    let base_values2: Vec<BF> = (0..16).map(|i| BF::new(15 + i)).collect();
    let base_input_dev2 = alloc_and_copy(&context, &base_values2);
    let base_cache2: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
    let ext_cache2: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
    let round2_desc = build_round2_desc_from_plan(
        &plan,
        &[vec![GpuFlatBaseAfterTwoSourceEntry {
            base_input_start: base_input_dev2.as_ptr().cast(),
            this_layer_cache_start: base_cache2.as_ptr().cast_mut().cast(),
            base_layer_half_size: 8,
            base_quarter_size: 4,
            next_layer_size: 2,
            first_access: true,
            source_kind: GpuBaseFieldSourceKind::Real,
        }]],
        &[vec![GpuFlatContinuingSourceEntry {
            previous_layer_start: ext_prev_dev.as_ptr().cast(),
            this_layer_cache_start: ext_cache2.as_ptr().cast_mut().cast(),
        }]],
    );
    assert_eq!(round2_desc.num_base_sources, 1);
    assert_eq!(round2_desc.num_ext_sources, 1);
    let mut round2_tags: Vec<u16> = round2_desc.idx_remap.clone();
    round2_tags.sort();
    assert_eq!(round2_tags, vec![0u16, FLAT_CONT_EXT_SOURCE_BIT]);
}
