use super::super::super::GpuBaseFieldSourceKind;
use super::super::kernels::GpuGKRMainLayerKernelKind;
use super::*;
use crate::upstream::{Field, GKRAddress};
use gpu_core::primitives::field::E4;

fn build_round1_desc_from_plan(
    plan: &FlatContinuationBuildPlan,
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
    plan: &FlatContinuationBuildPlan,
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
    let gate: PreparedGateForFlatContinuationPlan<'_, E4> = PreparedGateForFlatContinuationPlan {
        kind: GpuGKRMainLayerKernelKind::MaskIdentity,
        gate_idx: 0,
        base_addresses: &[GKRAddress::BaseLayerWitness(0)],
        ext_addresses: &[GKRAddress::InnerLayer {
            layer: 0,
            offset: 0,
        }],
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
    let gate: PreparedGateForFlatContinuationPlan<'_, E4> = PreparedGateForFlatContinuationPlan {
        kind: GpuGKRMainLayerKernelKind::MaskIdentity,
        gate_idx: 0,
        base_addresses: &[GKRAddress::BaseLayerWitness(0)],
        ext_addresses: &[GKRAddress::InnerLayer {
            layer: 0,
            offset: 0,
        }],
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

#[test]
fn flat_continuation_deduplicates_logical_sources_across_cache_allocations() {
    let base_address = [GKRAddress::BaseLayerWitness(7)];
    let ext_address = [GKRAddress::InnerLayer {
        layer: 0,
        offset: 9,
    }];
    let gates: [PreparedGateForFlatContinuationPlan<'_, E4>; 2] = [
        PreparedGateForFlatContinuationPlan {
            kind: GpuGKRMainLayerKernelKind::MaskIdentity,
            gate_idx: 0,
            base_addresses: &base_address,
            ext_addresses: &ext_address,
            batch_challenge_power_offset: 0,
            constraint_source: None,
        },
        PreparedGateForFlatContinuationPlan {
            kind: GpuGKRMainLayerKernelKind::MaskIdentity,
            gate_idx: 1,
            base_addresses: &base_address,
            ext_addresses: &ext_address,
            batch_challenge_power_offset: 1,
            constraint_source: None,
        },
    ];

    let plan = build_flat_continuation_plan(&gates);
    assert_eq!(plan.term_desc.num_sources, 2);
}

// End-to-end coverage of the round-0 kernel gate kinds runs through
// the compact-path stagewise/multi-schedule parity tests
// (`run_basic_unrolled_*`).
