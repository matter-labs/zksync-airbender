use era_cudart::memory::{memory_copy, memory_copy_async, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::field::PR;
use gpu_hash::keccak256::{build_partial_coset_tree, build_retained_layers, Digest};
use gpu_ntt::proth120::{
    dispatch, launch_suffix_micro, lde_coset_slot, CosetSource, DeviceContext, ScaleArgs,
    SuffixShape,
};

use super::packed::retained_len;
use super::sink::{coefficient_batches, launch_sink, SinkMode};

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
    // Diagnostic fused suffix8_4 with exact CPU LDE/leaf coefficients.
    for (log_n, log_v, log_lde, k0, cosets) in [(15, 4, 4, 3, 4)] {
        let skip_bottom = 5;
        let log_domain = log_n + log_lde;
        let rows = 1usize << log_n;
        let h = log_n - log_v;
        let monomials_host = random_values(rows, u64::from(log_n) << 8 | u64::from(log_v));
        let monomials = upload(&monomials_host);
        let plan = dispatch(log_n, 1, log_v, skip_bottom, device_l2());
        let s = SuffixShape::new(&plan, log_n, log_v, skip_bottom, 1);
        let mut prefix = DeviceAllocation::<PR>::alloc(rows * cosets as usize).unwrap();
        lde_coset_slot(
            &ctx,
            &monomials,
            &mut prefix,
            cosets as usize,
            &plan.prefix,
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

        let mut reference = DeviceAllocation::<Digest>::alloc(per_coset).unwrap();
        for coset in 0..cosets as usize {
            let expected = cpu_tile_pass(&monomials_host, log_lde, k0 as usize + coset, 1);
            let natural = upload(&expected);
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

fn cpu_tile_pass(monomials: &[PR], log_lde: u32, k0: usize, cosets: usize) -> Vec<PR> {
    use fft::Twiddles;
    use prover::allocation_pool::GenericAllocationPool;
    use prover::gkr::prover::backend::{
        Backend, ExtCoeffConversion, Proth120WorkStealingLazyBackend,
    };
    use std::alloc::Global;
    let worker = worker::Worker::new_with_num_threads(8);
    let n = monomials.len();
    let twiddles = Twiddles::<PR, Global>::new(n, &worker);
    let backend = Proth120WorkStealingLazyBackend;
    let pool = GenericAllocationPool::<PR, PR>::proxy();
    let (mut all, offsets) = backend.lde_ext_poly_from_monomial_form_continuous(
        monomials,
        &twiddles,
        1 << log_lde,
        &pool,
        &worker,
    );
    let conv =
        <Proth120WorkStealingLazyBackend as Backend<PR, PR>>::ext_coeff_conv(&backend, n, 16);
    for k in k0..k0 + cosets {
        conv.apply_serial(&mut all[k * n..(k + 1) * n], offsets[k]);
    }
    all[k0 * n..(k0 + cosets) * n].to_vec()
}
