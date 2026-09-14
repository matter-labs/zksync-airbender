//! Parity gates for the fused-boundary LDE path: the hybrid must produce
//! byte-identical coset outputs AND a byte-identical materialized monomial
//! scratch (the fused kernel's in-place side output) versus the unfused
//! hypercube-final + multi-coset-initial sequence.

use era_cudart::memory::{memory_copy_async, DeviceAllocation};

use super::super::{
    bitreversed_monomials_to_natural_evals_multi_coset, hypercube_evals_to_monomials,
    hypercube_to_bitreversed_multi_coset_evals_fused_log_n_20,
    hypercube_to_multi_coset_evals_fused, natural_monomials_to_bitreversed_evals_multi_coset,
};
use super::make_context;
use gpu_core::primitives::device_structures::DeviceMatrixChunk;
use gpu_core::primitives::field::BaseField;

type BF = BaseField;

fn check_case(log_n: usize, log_lde_factor: usize) {
    let ctx = make_context();
    let stream = ctx.get_exec_stream();
    let n = 1usize << log_n;
    let num_cosets = 1usize << log_lde_factor;

    let input = (0..n)
        .map(|idx| BF::new(29 + (idx as u32).wrapping_mul(2654435761)))
        .collect::<Vec<_>>();
    let mut d_in = DeviceAllocation::<BF>::alloc(n).unwrap();
    let mut d_scratch_old = DeviceAllocation::<BF>::alloc(n).unwrap();
    let mut d_scratch_new = DeviceAllocation::<BF>::alloc(n).unwrap();
    let mut d_out_old = DeviceAllocation::<BF>::alloc(num_cosets * n).unwrap();
    let mut d_out_new = DeviceAllocation::<BF>::alloc(num_cosets * n).unwrap();
    memory_copy_async(&mut d_in, &input[..], stream).unwrap();

    // Old sequence: standalone hypercube final into scratch, then the
    // multi-coset initial path over the monomials.
    hypercube_evals_to_monomials(
        &d_in[..],
        &mut d_scratch_old[..],
        log_n,
        true,
        stream,
        ctx.get_device_properties(),
    )
    .unwrap();
    let monomials = DeviceMatrixChunk::new(&d_scratch_old[..], n, 0, n);
    bitreversed_monomials_to_natural_evals_multi_coset(
        &monomials,
        &mut d_out_old[..],
        log_n,
        log_lde_factor,
        1,
        true,
        ctx.device_context(),
        None,
        stream,
        ctx.get_device_properties(),
    )
    .unwrap();

    // Hybrid path.
    let fused = hypercube_to_multi_coset_evals_fused(
        &d_in[..],
        &mut d_scratch_new[..],
        &mut d_out_new[..],
        log_n,
        log_lde_factor,
        1,
        stream,
        ctx.get_device_properties(),
    )
    .unwrap();
    assert!(fused, "hybrid path must be eligible at log_n {log_n}");

    let mut h_scratch_old = vec![BF::new(0); n];
    let mut h_scratch_new = vec![BF::new(0); n];
    let mut h_out_old = vec![BF::new(0); num_cosets * n];
    let mut h_out_new = vec![BF::new(0); num_cosets * n];
    memory_copy_async(&mut h_scratch_old[..], &d_scratch_old, stream).unwrap();
    memory_copy_async(&mut h_scratch_new[..], &d_scratch_new, stream).unwrap();
    memory_copy_async(&mut h_out_old[..], &d_out_old, stream).unwrap();
    memory_copy_async(&mut h_out_new[..], &d_out_new, stream).unwrap();
    stream.synchronize().unwrap();

    assert_ne!(h_out_old, vec![BF::new(0); num_cosets * n]);
    assert_eq!(
        h_scratch_old, h_scratch_new,
        "materialized monomials mismatch at log_n {log_n}, K {num_cosets}"
    );
    assert_eq!(
        h_out_old, h_out_new,
        "coset outputs mismatch at log_n {log_n}, K {num_cosets}"
    );
}

#[test]
fn test_lde_writeback_hybrid_matches_unfused() {
    for (log_n, log_lde_factor) in [(21, 1), (22, 1), (23, 1), (24, 1), (22, 2), (24, 0)] {
        check_case(log_n, log_lde_factor);
    }
}

#[test]
fn test_log_n_20_hypercube_final4_natural_initial8_fusion_matches_unfused() {
    let ctx = make_context();
    let stream = ctx.get_exec_stream();
    let log_n = 20usize;
    let log_lde_factor = 1usize;
    let n = 1usize << log_n;
    let num_cosets = 1usize << log_lde_factor;
    let input = (0..n)
        .map(|idx| BF::new(71 + (idx as u32).wrapping_mul(2246822519)))
        .collect::<Vec<_>>();
    let mut d_in = DeviceAllocation::<BF>::alloc(n).unwrap();
    let mut d_scratch_old = DeviceAllocation::<BF>::alloc(n).unwrap();
    let mut d_scratch_new = DeviceAllocation::<BF>::alloc(n).unwrap();
    let mut d_out_old = DeviceAllocation::<BF>::alloc(num_cosets * n).unwrap();
    let mut d_out_new = DeviceAllocation::<BF>::alloc(num_cosets * n).unwrap();
    memory_copy_async(&mut d_in, &input[..], stream).unwrap();

    hypercube_evals_to_monomials(
        &d_in[..],
        &mut d_scratch_old[..],
        log_n,
        false,
        stream,
        ctx.get_device_properties(),
    )
    .unwrap();
    let monomials = DeviceMatrixChunk::new(&d_scratch_old[..], n, 0, n);
    natural_monomials_to_bitreversed_evals_multi_coset(
        &monomials,
        &mut d_out_old[..],
        log_n,
        log_lde_factor,
        1,
        false,
        ctx.device_context(),
        None,
        stream,
        ctx.get_device_properties(),
    )
    .unwrap();

    hypercube_to_bitreversed_multi_coset_evals_fused_log_n_20(
        &d_in[..],
        &mut d_scratch_new[..],
        &mut d_out_new[..],
        log_lde_factor,
        1,
        stream,
        ctx.get_device_properties(),
    )
    .unwrap();

    let mut h_out_old = vec![BF::new(0); num_cosets * n];
    let mut h_out_new = vec![BF::new(0); num_cosets * n];
    memory_copy_async(&mut h_out_old[..], &d_out_old, stream).unwrap();
    memory_copy_async(&mut h_out_new[..], &d_out_new, stream).unwrap();
    stream.synchronize().unwrap();
    if let Some((row, (old, new))) = h_out_old
        .iter()
        .zip(h_out_new.iter())
        .enumerate()
        .find(|(_, (old, new))| old != new)
    {
        panic!("first fused-boundary mismatch at row {row}: old={old:?}, new={new:?}");
    }
}
