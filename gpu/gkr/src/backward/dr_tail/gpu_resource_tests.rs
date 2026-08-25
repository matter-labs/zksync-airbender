//! Locked GPU smoke test for DR-tail resource admission.
//!
//! The CPU tests in `resources.rs` cover the admission sequence against a
//! synthetic device. This one runs the same sequence against the real linked
//! kernel and the real device, and is the only place the CUDA queries are
//! exercised.

use super::{preflight_dr_tail_resources, DrTailEntrySelection};
use crate::backward::compile_corpus_layout;
use crate::test_utils::make_test_context;

const FINAL_TRACE_LOG: u32 = 4;

#[test]
fn dr_tail_gpu_resource_preflight() {
    // Smallest context proven by the existing GPU suite: admission only
    // queries function attributes and occupancy, but context creation itself
    // needs enough arena for the static allocator's small-pool carve.
    let _context = make_test_context(64, 16);
    let device_id = era_cudart::device::get_device().expect("a bound CUDA device");
    let (programs, _) = compile_corpus_layout("add_sub_lui_auipc_mop_layout_gkr.json");

    // Explicitly the production entry: this smoke covers the path production
    // takes, not a diagnostic neighbour.
    let plan = preflight_dr_tail_resources(
        &programs,
        FINAL_TRACE_LOG,
        device_id,
        DrTailEntrySelection::Portable,
    )
    .expect("the production DR tower must be admissible on this device");
    assert_eq!(plan.entry(), DrTailEntrySelection::Portable);

    let resources = plan.resources();
    assert_eq!(
        resources.local_bytes(),
        0,
        "the linked megakernel must not spill to local memory"
    );
    assert!(resources.registers() > 0);
    assert!(
        !plan.layers().is_empty(),
        "at least one DR layer is planned"
    );

    let largest = plan
        .layers()
        .iter()
        .map(|layer| layer.dynamic_smem_bytes())
        .max()
        .expect("non-empty plan");
    assert!(
        resources.effective_max_dynamic_smem_bytes() >= largest,
        "the opt-in ceiling must have been raised to cover the largest layer: \
         ceiling {} < required {largest}",
        resources.effective_max_dynamic_smem_bytes()
    );

    let measured = resources.occupancy_by_dynamic_bytes();
    assert!(!measured.is_empty());
    for (dynamic_bytes, blocks) in measured {
        assert!(
            *blocks > 0,
            "occupancy at {dynamic_bytes} dynamic bytes must admit a resident block"
        );
        assert!(*dynamic_bytes <= resources.effective_max_dynamic_smem_bytes());
    }

    let mut distinct: Vec<usize> = plan
        .layers()
        .iter()
        .map(|layer| layer.dynamic_smem_bytes())
        .collect();
    distinct.sort_unstable();
    distinct.dedup();
    assert_eq!(
        measured.len(),
        distinct.len(),
        "occupancy is measured once per distinct request size"
    );
}
