use era_cudart::memory::{memory_copy, memory_copy_async, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use gpu_core::primitives::field::PR;
use gpu_hash::keccak256::{build_partial_coset_tree, build_retained_layers, Digest};
use gpu_ntt::proth120::{
    convert_coset_leaves, dispatch, launch_suffix_micro, lde_coset, lde_coset_slot, CosetSource,
    DeviceContext, ScaleArgs, SuffixShape,
};

use super::packed::retained_len;
use super::sink::{coefficient_batches, launch_sink, SinkMode};
use crate::upstream::{domain_generator_for_size, Field};

fn random_values(count: usize, seed: u64) -> Vec<PR> {
    let mut state = seed;
    (0..count)
        .map(|_| {
            let mut next = || {
                state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
                let mut z = state;
                z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                z ^ (z >> 31)
            };
            PR::new(((u128::from(next()) << 64) | u128::from(next())) % PR::ORDER)
        })
        .collect()
}

fn upload<T: Copy>(values: &[T]) -> DeviceAllocation<T> {
    let mut device = DeviceAllocation::<T>::alloc(values.len()).unwrap();
    memory_copy(&mut device, values).unwrap();
    device
}

fn download<T: Copy + Default>(values: &DeviceSlice<T>, stream: &CudaStream) -> Vec<T> {
    let mut host = vec![T::default(); values.len()];
    memory_copy_async(&mut host, values, stream).unwrap();
    stream.synchronize().unwrap();
    host
}

fn device_l2() -> usize {
    gpu_core::primitives::context::DeviceProperties::new()
        .unwrap()
        .l2_cache_size_bytes
}

// coefficient_batches covers every (coset, tile) of a call once, each batch within one batch.
#[test]
fn coefficient_batches_cover_each_tile_once() {
    for (cosets, tiles, batch_cosets, batch_tiles) in [
        (4, 1024, 1, 464),
        (8, 1024, 1, 464),
        (1, 1024, 1, 464),
        (3, 1024, 1, 512),
        (5, 7, 1, 3),
        (7, 100, 1, 33),
        (128, 64, 7, 64),
        (2048, 4, 116, 4),
        (1, 64, 1, 64),
    ] {
        let batches = coefficient_batches(cosets, tiles, batch_cosets, batch_tiles);
        let mut seen = vec![0u32; cosets * tiles];
        for &(first_coset, coset_count, first_tile, tile_count) in &batches {
            assert!(coset_count >= 1 && tile_count >= 1);
            assert!(coset_count * tile_count <= batch_cosets * batch_tiles);
            for coset in first_coset..first_coset + coset_count {
                for tile in first_tile..first_tile + tile_count {
                    seen[coset * tiles + tile] += 1;
                }
            }
        }
        assert!(
            seen.iter().all(|&count| count == 1),
            "({cosets}, {tiles}, {batch_cosets}, {batch_tiles})"
        );
    }
    assert_eq!(coefficient_batches(4, 1024, 1, 464)[8..], [(0, 4, 928, 96)]);
}

// Compare the batched residue sink with the independent LDE and partial-tree construction.
#[test]
#[cfg(not(no_cuda))]
fn sink_coefficient_tree_matches_reference() {
    let ctx = DeviceContext::create().unwrap();
    let stream = CudaStream::create().unwrap();
    for (log_n, log_v, log_lde, k0, cosets) in [
        (13, 4, 2, 1, 3),
        (15, 4, 6, 60, 4),
        (19, 4, 4, 13, 3),
        (23, 4, 3, 7, 1),
    ] {
        let skip_bottom = 5;
        let log_domain = log_n + log_lde;
        let rows = 1usize << log_n;
        let h = log_n - log_v;
        let monomials = upload(&random_values(
            rows,
            u64::from(log_n) << 8 | u64::from(log_v),
        ));
        let plan = dispatch(log_n, 1, log_v, skip_bottom, device_l2()).unwrap();
        let s = SuffixShape::new(&plan, log_n, log_v, skip_bottom, 1);
        let mut prefix = DeviceAllocation::<PR>::alloc(rows * cosets as usize).unwrap();
        lde_coset_slot(
            &ctx,
            &monomials,
            &mut prefix,
            cosets as usize,
            plan.prefix.as_ref().unwrap(),
            ScaleArgs {
                coset: CosetSource::Batched { k0 },
                log_domain,
            },
            &stream,
        )
        .unwrap();
        let tiles_per_coset = s.tiles_per_coset() as u32;
        let mut tiles = DeviceAllocation::<PR>::alloc(
            cosets as usize * s.tile_len() * tiles_per_coset as usize,
        )
        .unwrap();
        launch_suffix_micro(
            &ctx,
            &prefix,
            rows,
            &mut tiles,
            &s,
            0,
            tiles_per_coset,
            cosets,
            None,
            &stream,
        )
        .unwrap();
        let per_coset = retained_len(h, skip_bottom);
        let mut retained = DeviceAllocation::<Digest>::alloc(cosets as usize * per_coset).unwrap();
        launch_sink(
            &ctx,
            &tiles,
            &s,
            0,
            tiles_per_coset,
            cosets,
            SinkMode::CoefficientTree { log_domain, k0 },
            &mut retained,
            per_coset,
            &stream,
        )
        .unwrap();
        build_retained_layers(h, skip_bottom, cosets, per_coset, &mut retained, &stream).unwrap();
        let candidate = download(&retained, &stream);

        let nu = domain_generator_for_size::<PR>(1u64 << log_domain);
        let mut natural = DeviceAllocation::<PR>::alloc(rows).unwrap();
        let mut reference = DeviceAllocation::<Digest>::alloc(per_coset).unwrap();
        for coset in 0..cosets as usize {
            let offset = upload(&[nu.pow(k0 + coset as u32)]);
            lde_coset(
                &ctx,
                &DeviceMatrix::new(&monomials, rows),
                &mut DeviceMatrixMut::new(&mut natural, rows),
                &offset,
                &stream,
            )
            .unwrap();
            convert_coset_leaves(&ctx, &mut natural, log_v, &offset, &stream).unwrap();
            build_partial_coset_tree(
                &natural,
                log_n,
                log_v,
                1,
                skip_bottom,
                &mut reference,
                &stream,
            )
            .unwrap();
            let reference = download(&reference, &stream);
            let candidate = &candidate[coset * per_coset..(coset + 1) * per_coset];
            let mismatches = (0..per_coset)
                .filter(|&i| candidate[i] != reference[i])
                .count();
            assert_eq!(
                mismatches, 0,
                "({log_n},{log_v},D {log_domain}) coset {}: {mismatches} of {per_coset} retained digests differ",
                k0 as usize + coset
            );
        }
        println!(
            "sink_coefficient_tree_matches_reference: ({log_n},1,{log_v},{skip_bottom}) D {log_domain} cosets {k0}..{} r {} tiles {tiles_per_coset}: {per_coset} retained digests per coset, 0 mismatches",
            k0 + cosets,
            s.r
        );
    }
}

mod packed;
