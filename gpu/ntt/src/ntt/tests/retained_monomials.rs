use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use gpu_core::primitives::context::DeviceProperties;
use gpu_core::primitives::device_structures::DeviceMatrix;
use gpu_core::primitives::field::BF;

use super::super::{
    hypercube_to_retained_monomials_and_coset, hypercube_to_retained_monomials_and_coset_in_place,
    natural_monomials_to_bitreversed_evals_multi_coset, retained_monomials_to_coset,
};
use super::{make_context, multivariate_hypercube_evals_into_coeffs};

fn compare(actual: &[BF], expected: &[BF], label: &str) {
    assert_eq!(actual.len(), expected.len());
    if let Some((row, (a, b))) = actual
        .iter()
        .zip(expected)
        .enumerate()
        .find(|(_, (a, b))| a != b)
    {
        panic!("{label}: row={row} actual={a:?} expected={b:?}");
    }
}

fn run(log_n: usize, log_f: usize, force_two_pass: bool) {
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
    let f = 1usize << log_f;
    let columns = 2; // Exercises cross-column finest work and monomial prefetch.
    let len = columns * n;
    let raw = (0..len)
        .map(|i| BF::new((i as u32).wrapping_mul(2654435761).wrapping_add(71)))
        .collect::<Vec<_>>();
    let mut expected_monomials = raw.clone();
    for column in expected_monomials.chunks_mut(n) {
        multivariate_hypercube_evals_into_coeffs(column, log_n as u32);
    }
    let mut d_raw = DeviceAllocation::<BF>::alloc(len).unwrap();
    let mut d_m = DeviceAllocation::<BF>::alloc(len).unwrap();
    let mut d_coset = DeviceAllocation::<BF>::alloc(len).unwrap();
    let mut d_full = DeviceAllocation::<BF>::alloc(len * f).unwrap();
    memory_copy_async(&mut d_raw, &raw[..], stream).unwrap();
    memory_copy_async(&mut d_m, &expected_monomials[..], stream).unwrap();
    natural_monomials_to_bitreversed_evals_multi_coset(
        &DeviceMatrix::new(&d_m, n),
        &mut d_full,
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
    let mut expected_cosets = vec![BF::new(0); len * f];
    memory_copy_async(&mut expected_cosets[..], &d_full, stream).unwrap();
    stream.synchronize().unwrap();
    if log_n < 20 {
        let cpu =
            super::helpers::host_cosets_from_natural_monomials(&expected_monomials, log_n, log_f);
        for (coset, values) in cpu.into_iter().enumerate() {
            compare(
                &expected_cosets[coset * len..(coset + 1) * len],
                &values,
                &format!("full-LDE CPU reference m={log_n} ell={log_f} coset={coset}"),
            );
            expected_cosets[coset * len..(coset + 1) * len].copy_from_slice(&values);
        }
    }
    for in_place in [false, true] {
        // Nonzero recycled contents, overwritten by the first raw pass.
        memory_copy_async(&mut d_m, &raw[..], stream).unwrap();
        memory_copy_async(&mut d_coset, &raw[..], stream).unwrap();
        if in_place {
            hypercube_to_retained_monomials_and_coset_in_place(
                &mut d_m,
                &mut d_coset,
                log_n,
                log_f,
                1,
                &properties,
                stream,
            )
            .unwrap();
        } else {
            hypercube_to_retained_monomials_and_coset(
                &d_raw,
                &mut d_m,
                &mut d_coset,
                log_n,
                log_f,
                1,
                &properties,
                stream,
            )
            .unwrap();
        }
        let label = format!("n={log_n} f={log_f} two={force_two_pass} in_place={in_place}");
        let mut actual_m = vec![BF::new(0); len];
        let mut actual_c = vec![BF::new(0); len];
        let mut actual_raw = vec![BF::new(0); len];
        memory_copy_async(&mut actual_m[..], &d_m, stream).unwrap();
        memory_copy_async(&mut actual_c[..], &d_coset, stream).unwrap();
        memory_copy_async(&mut actual_raw[..], &d_raw, stream).unwrap();
        stream.synchronize().unwrap();
        compare(
            &actual_m,
            &expected_monomials,
            &format!("{label} monomials"),
        );
        compare(
            &actual_c,
            &expected_cosets[len..2 * len],
            &format!("{label} first coset"),
        );
        compare(&actual_raw, &raw, &format!("{label} preserved raw"));
        for coset in (0..f).rev() {
            retained_monomials_to_coset(
                &d_m,
                &mut d_coset,
                log_n,
                log_f,
                coset,
                &properties,
                stream,
            )
            .unwrap();
            memory_copy_async(&mut actual_c[..], &d_coset, stream).unwrap();
            stream.synchronize().unwrap();
            compare(
                &actual_c,
                &expected_cosets[coset * len..(coset + 1) * len],
                &format!("{label} coset={coset}"),
            );
        }
        memory_copy_async(&mut actual_m[..], &d_m, stream).unwrap();
        stream.synchronize().unwrap();
        compare(
            &actual_m,
            &expected_monomials,
            &format!("{label} retained after regeneration"),
        );
    }
}

macro_rules! case {
    ($name:ident, $n:literal, $f:literal, $two:literal) => {
        #[test]
        fn $name() {
            run($n, $f, $two);
        }
    };
}
case!(retained_n20_f8, 20, 3, false);
case!(retained_n21_f2, 21, 1, false);
case!(retained_n24_f2, 24, 1, false);
case!(retained_n24_f8, 24, 3, false);
case!(retained_n24_f8_two_pass, 24, 3, true);

case!(retained_n22_f2, 22, 1, false);
case!(retained_n23_f2, 23, 1, false);
case!(retained_n23_f8_two_pass, 23, 3, true);

case!(retained_n13_f2, 13, 1, false);
case!(retained_n13_f4, 13, 2, false);
case!(retained_n14_f2, 14, 1, false);
case!(retained_n14_f4, 14, 2, false);
case!(retained_n15_f2, 15, 1, false);
case!(retained_n15_f4, 15, 2, false);
case!(retained_n16_f2, 16, 1, false);
case!(retained_n16_f4, 16, 2, false);
case!(retained_n17_f2, 17, 1, false);
case!(retained_n17_f4, 17, 2, false);
case!(retained_n18_f2, 18, 1, false);
case!(retained_n18_f4, 18, 2, false);
case!(retained_n19_f2, 19, 1, false);
case!(retained_n19_f4, 19, 2, false);
