use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use gpu_core::primitives::field::PR;
use gpu_core::primitives::nvtx::scoped_range;
use gpu_hash::keccak256::{
    build_partial_coset_trees_multi_coset, build_top_tree, gather_tree_cap, retained_layer_offset,
    transcript_commit_u32, Digest,
};
use gpu_ntt::proth120::{lde_coset, lde_cosets_batched};
use gpu_ops::powers::get_powers_by_val;
use gpu_prover_context::ProverContext;

use super::kernels;
use super::shape::OracleShape;
use crate::upstream::domain_generator_for_size;

pub(crate) struct IntermediateOracle {
    pub(crate) shape: OracleShape,
    pub(crate) monomials: DeviceAllocation<PR>,
    pub(crate) retained: DeviceAllocation<Digest>,
    pub(crate) roots: DeviceAllocation<Digest>,
    pub(crate) top_nodes: DeviceAllocation<Digest>,
    pub(crate) cap: DeviceAllocation<Digest>,
}

fn validate_oracle_shape(shape: &OracleShape, context: &ProverContext) {
    let log_max_domain = context.proth120_ntt_device_context().log_max_domain();
    assert!(
        shape.log_domain != 31 || log_max_domain == 31,
        "Proth120 WHIR: batched LDE requires a log_max_domain 31 context"
    );
    assert!(
        shape.log_domain <= log_max_domain,
        "Proth120 WHIR: oracle log_domain exceeds the Proth120 context log_max_domain"
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

pub(crate) fn schedule_coset_offsets(
    shape: &OracleShape,
    context: &ProverContext,
) -> CudaResult<Option<DeviceAllocation<PR>>> {
    if shape.log_domain == 31 {
        return Ok(None);
    }
    let mut offsets = context.alloc(1 << shape.log_lde, AllocationPlacement::BestFit)?;
    get_powers_by_val(
        domain_generator_for_size::<PR>(1u64 << shape.log_domain),
        0,
        &mut offsets,
        context.get_exec_stream(),
    )?;
    Ok(Some(offsets))
}

pub(crate) fn schedule_lde_convert_pass(
    monomials: &DeviceSlice<PR>,
    shape: &OracleShape,
    offsets: Option<&DeviceSlice<PR>>,
    k0: u32,
    tile: &mut DeviceSlice<PR>,
    context: &ProverContext,
) -> CudaResult<()> {
    let n = 1usize << shape.log_n;
    let cosets = tile.len() >> shape.log_n;
    let ntt = context.proth120_ntt_device_context();
    let stream = context.get_exec_stream();
    match offsets {
        None => lde_cosets_batched(ntt, monomials, k0..k0 + cosets as u32, tile, stream)?,
        Some(offsets) => {
            let input = DeviceMatrix::new(monomials, n);
            for local in 0..cosets {
                let k = k0 as usize + local;
                let mut output = DeviceMatrixMut::new(&mut tile[local * n..(local + 1) * n], n);
                lde_coset(ntt, &input, &mut output, &offsets[k..k + 1], stream)?;
            }
        }
    }
    kernels::convert_tile_leaves(
        tile,
        shape.log_n,
        shape.log_v,
        ntt.descriptor(),
        shape.log_domain,
        k0,
        cosets as u32,
        stream,
    )
}

pub(crate) fn schedule_commit_intermediate(
    monomials: &DeviceSlice<PR>,
    shape: &OracleShape,
    cap_dst: &mut DeviceSlice<Digest>,
    seed: &mut DeviceSlice<u8>,
    context: &ProverContext,
) -> CudaResult<IntermediateOracle> {
    validate_oracle_shape(shape, context);
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
    let offsets = schedule_coset_offsets(shape, context)?;
    let mut tile = context.alloc(tile_cosets << shape.log_n, AllocationPlacement::Top)?;
    for k0 in (0..cosets).step_by(tile_cosets) {
        {
            let _r = scoped_range(Some("ab"), "whir.commit.prefix");
            schedule_lde_convert_pass(
                &copy,
                shape,
                offsets.as_deref(),
                k0 as u32,
                &mut tile,
                context,
            )?;
        }
        let _r = scoped_range(Some("ab"), "whir.commit.suffix");
        build_partial_coset_trees_multi_coset(
            &tile,
            shape.log_n,
            shape.log_v,
            1,
            shape.skip_bottom,
            tile_cosets as u32,
            1 << shape.log_n,
            r,
            &mut retained[k0 * r..(k0 + tile_cosets) * r],
            stream,
        )?;
    }
    drop(tile);
    drop(offsets);
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
