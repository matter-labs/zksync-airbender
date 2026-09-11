use std::alloc::Global;

use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use gpu_core::primitives::context::DeviceProperties;
use gpu_core::primitives::device_structures::DeviceMatrix;
use gpu_core::primitives::field::BF;

use super::super::{
    coset_to_monomials_in_place, hypercube_to_coset_in_place, monomials_to_coset_in_place,
    monomials_to_hypercube_in_place, natural_monomials_to_bitreversed_evals_multi_coset,
};
use super::make_context;

fn inverse_roundtrip(log_n: usize, log_f: usize, force_two_pass: bool) {
    let context = make_context();
    let stream = context.get_exec_stream();
    let live = context.get_device_properties();
    let properties = DeviceProperties {
        l2_cache_size_bytes: if force_two_pass { 16 << 20 } else { 128 << 20 },
        sm_count: live.sm_count,
        compute_capability_major: live.compute_capability_major,
        compute_capability_minor: live.compute_capability_minor,
        max_dynamic_smem_per_block_optin: live.max_dynamic_smem_per_block_optin,
    };
    let n = 1usize << log_n;
    let columns = 2;
    let len = n * columns;
    let raw: Vec<_> = (0..len)
        .map(|i| BF::new((i as u32).wrapping_mul(2654435761).wrapping_add(113)))
        .collect();
    let mut monomials = raw.clone();
    for column in monomials.chunks_mut(n) {
        super::multivariate_hypercube_evals_into_coeffs(column, log_n as u32);
    }
    let mut source = DeviceAllocation::<BF>::alloc(len).unwrap();
    let mut full = DeviceAllocation::<BF>::alloc(len << log_f).unwrap();
    let mut workspace = DeviceAllocation::<BF>::alloc(len).unwrap();
    memory_copy_async(&mut source, &monomials[..], stream).unwrap();
    natural_monomials_to_bitreversed_evals_multi_coset(
        &DeviceMatrix::new(&source, n),
        &mut full,
        log_n,
        log_f,
        columns,
        false,
        context.device_context(),
        None,
        stream,
        &properties,
    )
    .unwrap();
    let mut actual = vec![BF::new(0); len];
    let mut expected_coset = vec![BF::new(0); len];
    for coset in [0, (1usize << log_f) - 1] {
        memory_copy_async(&mut workspace, &raw[..], stream).unwrap();
        hypercube_to_coset_in_place(&mut workspace, log_n, log_f, coset, &properties, stream)
            .unwrap();
        memory_copy_async(&mut actual[..], &workspace, stream).unwrap();
        memory_copy_async(
            &mut expected_coset[..],
            &full[coset * len..(coset + 1) * len],
            stream,
        )
        .unwrap();
        stream.synchronize().unwrap();
        assert_eq!(
            actual.iter().zip(&expected_coset).position(|(a, b)| a != b),
            None,
            "fused raw-to-coset: log_n={log_n} log_f={log_f} coset={coset} two_pass={force_two_pass}"
        );
    }
    for coset in (0..1usize << log_f).rev() {
        // At log 20 the first inverse consumes independently computed CPU
        // coset values, so the roundtrip cannot hide a shared GPU transform bug.
        let cpu_coset = if log_n == 20 && coset == (1usize << log_f) - 1 {
            let worker = worker::Worker::new();
            let twiddles = fft::precompute_twiddles_for_fft::<BF, Global, false>(n, &worker);
            let mut result = Vec::with_capacity(len);
            for m in monomials.chunks(n) {
                let mut bitrev = m.to_vec();
                fft::bitreverse_enumeration_inplace(&mut bitrev);
                let mut c = super::helpers::host_forward_ntt_single_coset(
                    &bitrev,
                    log_n,
                    log_f,
                    coset,
                    &twiddles[..n / 2],
                );
                fft::bitreverse_enumeration_inplace(&mut c);
                result.extend(c);
            }
            Some(result)
        } else {
            None
        };
        if let Some(c) = &cpu_coset {
            memory_copy_async(&mut workspace, &c[..], stream).unwrap();
        } else {
            memory_copy_async(
                &mut workspace,
                &full[coset * len..(coset + 1) * len],
                stream,
            )
            .unwrap();
        }
        coset_to_monomials_in_place(&mut workspace, log_n, log_f, coset, &properties, stream)
            .unwrap();
        memory_copy_async(&mut actual[..], &workspace, stream).unwrap();
        stream.synchronize().unwrap();
        assert_eq!(
            actual.iter().zip(&monomials).position(|(a, b)| a != b),
            None,
            "coset inverse: log_n={log_n} log_f={log_f} coset={coset} two_pass={force_two_pass}"
        );
        let next_coset = (coset + 1) % (1usize << log_f);
        monomials_to_coset_in_place(
            &mut workspace,
            log_n,
            log_f,
            next_coset,
            &properties,
            stream,
        )
        .unwrap();
        memory_copy_async(&mut actual[..], &workspace, stream).unwrap();
        memory_copy_async(
            &mut expected_coset[..],
            &full[next_coset * len..(next_coset + 1) * len],
            stream,
        )
        .unwrap();
        stream.synchronize().unwrap();
        assert_eq!(
            actual.iter().zip(&expected_coset).position(|(a, b)| a != b),
            None,
            "in-place coset {coset} -> M -> coset {next_coset}: log_n={log_n} log_f={log_f} two_pass={force_two_pass}"
        );
        coset_to_monomials_in_place(
            &mut workspace,
            log_n,
            log_f,
            next_coset,
            &properties,
            stream,
        )
        .unwrap();
        monomials_to_hypercube_in_place(&mut workspace, log_n, &properties, stream).unwrap();
        memory_copy_async(&mut actual[..], &workspace, stream).unwrap();
        stream.synchronize().unwrap();
        assert_eq!(
            actual.iter().zip(&raw).position(|(a, b)| a != b),
            None,
            "restore raw evaluations: log_n={log_n} log_f={log_f} coset={next_coset} two_pass={force_two_pass}"
        );
    }
}

macro_rules! inverse_case {
    ($name:ident, $n:literal, $f:literal, $two:literal) => {
        #[test]
        fn $name() {
            inverse_roundtrip($n, $f, $two);
        }
    };
}
inverse_case!(in_place_inverse_n20_f8, 20, 3, false);
inverse_case!(in_place_inverse_n21_f4, 21, 2, false);
inverse_case!(in_place_inverse_n22_f2, 22, 1, false);
inverse_case!(in_place_inverse_n23_f4, 23, 2, false);
inverse_case!(in_place_inverse_n24_f8, 24, 3, false);
inverse_case!(in_place_inverse_n23_f4_two_pass, 23, 2, true);
inverse_case!(in_place_inverse_n24_f8_two_pass, 24, 3, true);
