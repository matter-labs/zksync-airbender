use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::field::PR;
use gpu_hash::keccak256::{
    append_top_paths, build_partial_coset_trees_multi_coset, retained_layer_offset,
};
use gpu_prover_context::ProverContext;

use super::commit::IntermediateOracle;
use super::kernels;
use super::outputs::IntermediateProofDevice;

pub(crate) fn schedule_horner_leaves(
    monomials: &DeviceSlice<PR>,
    log_n: u32,
    log_v: u32,
    points: &DeviceSlice<PR>,
    leaves: &mut DeviceSlice<PR>,
    tower_log_k: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    kernels::horner_leaves(
        monomials,
        log_n,
        log_v,
        points,
        leaves,
        tower_log_k,
        context.get_exec_stream(),
    )
}

pub(crate) fn schedule_open_intermediate(
    oracle: &IntermediateOracle,
    queries: &DeviceSlice<u32>,
    query_domain_log2: u32,
    out: &mut IntermediateProofDevice,
    context: &ProverContext,
) -> CudaResult<()> {
    let shape = &oracle.shape;
    assert!(
        shape.log_domain >= query_domain_log2,
        "Proth120 WHIR: log_domain below query_domain_log2"
    );
    assert!(
        (8..=26).contains(&shape.log_n)
            && (1..=4).contains(&shape.log_v)
            && shape.log_leaves == shape.log_n - shape.log_v
            && shape.log_domain == shape.log_n + shape.log_lde
            && shape.log_domain <= 31
            && query_domain_log2 == shape.log_leaves + shape.log_lde,
        "Proth120 WHIR: opening oracle geometry invalid"
    );
    assert!(
        shape.skip_bottom <= shape.log_leaves.min(5),
        "Proth120 WHIR: skip_bottom exceeds min(5, h)"
    );
    assert!(
        shape.cap_log <= shape.log_lde
            && shape.path_len == (query_domain_log2 - shape.cap_log) as usize,
        "Proth120 WHIR: opening cap or path geometry invalid"
    );
    assert_eq!(
        shape.retained_per_coset,
        retained_layer_offset(shape.log_leaves, shape.skip_bottom, shape.log_leaves) + 1,
        "Proth120 WHIR: opening retained stride invalid"
    );
    assert!(
        oracle.monomials.len() == 1 << shape.log_n
            && oracle.retained.len() == (1usize << shape.log_lde) * shape.retained_per_coset
            && oracle.roots.len() == 1 << shape.log_lde
            && oracle.top_nodes.len() == (1usize << shape.log_lde) - (1 << shape.cap_log)
            && oracle.cap.len() == 1 << shape.cap_log,
        "Proth120 WHIR: opening oracle buffer lengths invalid"
    );
    assert!(
        out.cap.len() == 1 << shape.cap_log
            && out.leaves.len() == queries.len() << shape.log_v
            && out.paths.len() == queries.len() * shape.path_len as usize
            && out.tree_indexes.len() == queries.len(),
        "Proth120 WHIR: opening output lengths invalid"
    );
    let ntt = context.proth120_ntt_device_context();
    assert!(
        shape.log_domain <= ntt.log_max_domain(),
        "Proth120 WHIR: opening domain exceeds Proth120 context log_max_domain"
    );
    assert!(
        queries.len() <= u32::MAX as usize,
        "Proth120 WHIR: query count exceeds u32::MAX"
    );
    if queries.is_empty() {
        return Ok(());
    }
    let k = 1usize << shape.skip_bottom;
    let mut points = context.alloc(queries.len() * k, AllocationPlacement::BestFit)?;
    let mut leaves = context.alloc(
        queries.len() * k * (1 << shape.log_v),
        AllocationPlacement::BestFit,
    )?;
    let mut towers = context.alloc(queries.len() * (2 * k - 1), AllocationPlacement::BestFit)?;
    let stream = context.get_exec_stream();
    kernels::subtree_points(
        queries,
        query_domain_log2,
        shape.log_lde,
        shape.skip_bottom,
        ntt.descriptor(),
        shape.log_domain,
        &mut points,
        stream,
    )?;
    schedule_horner_leaves(
        &oracle.monomials,
        shape.log_n,
        shape.log_v,
        &points,
        &mut leaves,
        shape.skip_bottom,
        context,
    )?;
    build_partial_coset_trees_multi_coset(
        &leaves,
        shape.skip_bottom + shape.log_v,
        shape.log_v,
        1,
        0,
        queries.len() as u32,
        k << shape.log_v,
        2 * k - 1,
        &mut towers,
        stream,
    )?;
    kernels::extract_paths(
        &leaves,
        &towers,
        &oracle.retained,
        shape.retained_per_coset,
        shape.log_lde,
        shape.log_leaves,
        shape.skip_bottom,
        shape.log_v,
        queries,
        &mut out.leaves,
        &mut out.paths,
        shape.path_len as u32,
        stream,
    )?;
    append_top_paths(
        &oracle.roots,
        &oracle.top_nodes,
        shape.log_lde,
        shape.cap_log,
        shape.log_leaves,
        queries,
        &mut out.paths,
        &mut out.tree_indexes,
        stream,
    )
}
