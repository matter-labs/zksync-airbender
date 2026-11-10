use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::PR;
use gpu_core::primitives::nvtx::scoped_range;
use gpu_hash::keccak256::{
    build_top_tree, gather_tree_cap, retained_layer_offset, transcript_commit_u32, Digest,
};
use gpu_ntt::proth120::{dispatch, SuffixShape, TwiddleDescriptor};
use gpu_prover_context::ProverContext;
use gpu_trace::trace::sink::{
    coefficient_tiles_len, commit_coefficient_cosets, commit_residue_cosets, has_leaf_sink,
    has_residue_sink, residue_scratch_len, SinkMode,
};

use super::kernels;
use super::shape::OracleShape;

pub(crate) struct IntermediateOracle {
    pub(crate) shape: OracleShape,
    pub(crate) monomials: DeviceAllocation<PR>,
    pub(crate) retained: DeviceAllocation<Digest>,
    pub(crate) roots: DeviceAllocation<Digest>,
    pub(crate) top_nodes: DeviceAllocation<Digest>,
    pub(crate) cap: DeviceAllocation<Digest>,
}

fn validate_oracle_shape(shape: &OracleShape) {
    let log_max_domain = gpu_ntt::proth120::LOG_MAX_DOMAIN;
    assert!(
        shape.log_domain <= log_max_domain,
        "Proth120 WHIR: oracle log_domain exceeds the Proth120 NTT domain"
    );
    assert!(
        shape.tile_cosets_log2 <= shape.log_lde,
        "Proth120 WHIR: tile cosets exceed the oracle cosets"
    );
    assert_eq!(
        shape.retained_per_coset,
        retained_layer_offset(shape.log_leaves, shape.skip_bottom, shape.log_leaves) + 1,
        "Proth120 WHIR: retained_per_coset differs from retained_layer_offset(h, s, h) + 1"
    );
}

pub(crate) fn schedule_commit_intermediate(
    monomials: &DeviceSlice<PR>,
    shape: &OracleShape,
    cap_dst: &mut DeviceSlice<Digest>,
    seed: &mut DeviceSlice<u8>,
    twiddles: TwiddleDescriptor,
    context: &ProverContext,
) -> CudaResult<IntermediateOracle> {
    validate_oracle_shape(shape);
    assert_eq!(
        monomials.len(),
        1 << shape.log_n,
        "Proth120 WHIR: oracle monomials length differs from 2^log_n"
    );
    assert_eq!(
        cap_dst.len(),
        1 << shape.cap_log,
        "Proth120 WHIR: cap destination length differs from 2^cap_log"
    );
    let cosets = 1usize << shape.log_lde;
    let tile_cosets = 1usize << shape.tile_cosets_log2;
    let r = shape.retained_per_coset;
    let stream = context.get_exec_stream();
    let mut copy = context.alloc(monomials.len(), AllocationPlacement::Bottom)?;
    {
        let _r = scoped_range(Some("ab"), "whir.commit.copy_monomials");
        memory_copy_async(&mut copy, monomials, stream)?;
    }
    let mut retained = context.alloc(cosets * r, AllocationPlacement::Bottom)?;
    let mut roots = context.alloc(cosets, AllocationPlacement::Bottom)?;
    let mut top_nodes =
        context.alloc(cosets - (1 << shape.cap_log), AllocationPlacement::Bottom)?;
    let mut cap = context.alloc(1 << shape.cap_log, AllocationPlacement::Bottom)?;
    if has_residue_sink(shape.log_n, shape.log_v, shape.skip_bottom) {
        log::debug!(
            "whir commit 2^{} oracle, log_v {}, log_lde {}, skip_bottom {}: residue sink",
            shape.log_n,
            shape.log_v,
            shape.log_lde,
            shape.skip_bottom
        );
        let _r = scoped_range(Some("ab"), "whir.commit.suffix");
        let mut scratch = context.alloc(
            residue_scratch_len(shape.log_n, shape.log_v, shape.skip_bottom, tile_cosets),
            AllocationPlacement::Top,
        )?;
        for k0 in (0..cosets).step_by(tile_cosets) {
            commit_residue_cosets(
                twiddles,
                &copy,
                shape.log_n,
                shape.log_v,
                shape.skip_bottom,
                shape.log_domain,
                k0 as u32,
                tile_cosets,
                &mut scratch,
                &mut retained[k0 * r..(k0 + tile_cosets) * r],
                r,
                stream,
            )?;
        }
    } else {
        schedule_commit_retained(&copy, shape, &mut retained, twiddles, context)?;
    }
    let _r = scoped_range(Some("ab"), "whir.commit.top");
    kernels::place_roots(&retained, r, shape.log_lde, &mut roots, stream)?;
    build_top_tree(&roots, shape.cap_log, &mut top_nodes, stream)?;
    gather_tree_cap(&roots, &top_nodes, shape.cap_log, &mut cap, stream)?;
    memory_copy_async(cap_dst, &cap, stream)?;
    transcript_commit_u32(seed, unsafe { cap_dst.transmute() }, stream)?;
    Ok(IntermediateOracle {
        shape: *shape,
        monomials: copy,
        retained,
        roots,
        top_nodes,
        cap,
    })
}

// The retained trees of every coset of an oracle on the prefix + suffix path: the fused suffix micro
// and coefficient-tree sink when the shape has one, else the naturalized LDE, leaf conversion and
// partial trees.
fn schedule_commit_retained(
    copy: &DeviceSlice<PR>,
    shape: &OracleShape,
    retained: &mut DeviceSlice<Digest>,
    twiddles: TwiddleDescriptor,
    context: &ProverContext,
) -> CudaResult<()> {
    let cosets = 1usize << shape.log_lde;
    let tile_cosets = 1usize << shape.tile_cosets_log2;
    let r = shape.retained_per_coset;
    let stream = context.get_exec_stream();
    let mut tile = context.alloc(tile_cosets << shape.log_n, AllocationPlacement::Top)?;
    let plan = dispatch(
        shape.log_n,
        1,
        shape.log_v,
        shape.skip_bottom,
        context.get_device_properties().l2_cache_size_bytes,
    );
    let suffix = SuffixShape::new(&plan, shape.log_n, shape.log_v, shape.skip_bottom, 1);
    assert!(
        has_leaf_sink(
            &suffix,
            &SinkMode::CoefficientTree {
                log_domain: shape.log_domain,
                k0: 0
            }
        ),
        "Proth120 WHIR: retained commitment requires the fused sink"
    );

    let mut tiles = context.alloc(
        coefficient_tiles_len(&suffix, tile_cosets, plan.l2_budget),
        AllocationPlacement::Top,
    )?;
    for k0 in (0..cosets).step_by(tile_cosets) {
        commit_coefficient_cosets(
            twiddles,
            copy,
            &plan,
            &suffix,
            shape.log_domain,
            k0 as u32,
            tile_cosets,
            &mut tile,
            &mut tiles,
            &mut retained[k0 * r..(k0 + tile_cosets) * r],
            r,
            stream,
        )?;
    }
    drop(tiles);

    drop(tile);
    Ok(())
}
