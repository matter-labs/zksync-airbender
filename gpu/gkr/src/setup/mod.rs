use era_cudart::{memory::memory_copy_async, result::CudaResult, slice::DeviceSlice};
use gpu_core::primitives::static_host::{alloc_static_pinned_box_uninit, StaticPinnedBox};
use gpu_hash::blake2s::Digest;
use gpu_prover_context::ProverContext;

pub(crate) fn partial_tree_projection_start(
    name: &str,
    source_depth: u32,
    target_depth: u32,
    source_len: usize,
    target_len: usize,
) -> usize {
    assert!(
        target_depth >= source_depth,
        "{name}: target partial-tree depth must be >= source depth"
    );
    source_len
        .checked_sub(target_len)
        .unwrap_or_else(|| panic!("{name}: target partial tree must fit the source tree"))
}

pub(crate) const DECODER_FILL_INDEX: usize = 0;
pub(crate) const SETUP_PADDING_FILL_INDEX: usize = 1;
pub(crate) const LOOKUP_FILL_COUNT: usize = 2;

pub(crate) fn copy_partial_trees_to_pinned_host(
    backing: &DeviceSlice<Digest>,
    instances_count: usize,
    context: &ProverContext,
) -> CudaResult<Vec<StaticPinnedBox<Digest>>> {
    assert_eq!(backing.len() % instances_count, 0);
    let per_coset = backing.len() / instances_count;
    let mut result = Vec::with_capacity(instances_count);
    for coset_index in 0..instances_count {
        let segment = &backing[coset_index * per_coset..(coset_index + 1) * per_coset];
        let mut host_tree = alloc_static_pinned_box_uninit(per_coset)?;
        memory_copy_async(&mut host_tree[..], segment, context.get_exec_stream())?;
        result.push(host_tree);
    }
    Ok(result)
}
