use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use gpu_core::primitives::context::DeviceProperties;
use gpu_core::primitives::field::BF;

use super::super::{
    hypercube_evals_to_monomials, hypercube_to_bitreversed_multi_coset_evals_fused_log_n_20,
    hypercube_to_multi_coset_bitrev_evals_fused, hypercube_to_retained_monomials_and_coset,
    hypercube_to_retained_monomials_and_coset_in_place,
    natural_monomials_to_bitreversed_evals_multi_coset, retained_monomials_to_coset,
    RetainedLdeOptions,
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
    let mut scratch = DeviceAllocation::<BF>::alloc(n).unwrap();
    memory_copy_async(&mut d_raw, &raw[..], stream).unwrap();
    // Existing full-LDE schedule, with the same two/three-pass dispatch.
    for column in 0..columns {
        let offset = column * n;
        let input = &d_raw[offset..offset + n];
        if log_n == 20 {
            hypercube_to_bitreversed_multi_coset_evals_fused_log_n_20(
                input,
                &mut scratch,
                &mut d_full[offset..],
                log_f,
                columns,
                stream,
                &properties,
            )
            .unwrap();
        } else if !force_two_pass {
            let next = (column + 1 < columns).then(|| unsafe { d_raw.as_ptr().add(offset + n) });
            assert!(hypercube_to_multi_coset_bitrev_evals_fused(
                input,
                &mut d_full[offset..],
                log_n,
                log_f,
                columns,
                column != 0,
                next,
                stream,
                &properties
            )
            .unwrap());
        } else {
            hypercube_evals_to_monomials(input, &mut scratch, log_n, false, stream, &properties)
                .unwrap();
            natural_monomials_to_bitreversed_evals_multi_coset(
                &scratch[..],
                &mut d_full[offset..],
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
        }
    }
    let mut expected_cosets = vec![BF::new(0); len * f];
    memory_copy_async(&mut expected_cosets[..], &d_full, stream).unwrap();
    stream.synchronize().unwrap();
    for in_place in [false, true] {
        for (streamed, prefetch) in [(false, false), (false, true), (true, false), (true, true)] {
            let options = RetainedLdeOptions {
                stream_first_coset_stores: streamed,
                prefetch_next_monomial_column: prefetch,
            };
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
                    options,
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
                    options,
                    &properties,
                    stream,
                )
                .unwrap();
            }
            let label = format!(
                "n={log_n} f={log_f} two={force_two_pass} in_place={in_place} streamed={streamed} prefetch={prefetch}"
            );
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
                    options,
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
}

macro_rules! case {
    ($name:ident, $n:literal, $f:literal, $two:literal) => {
        #[test]
        fn $name() {
            run($n, $f, $two);
        }
    };
}
case!(retained_n20_f2, 20, 1, false);
case!(retained_n20_f4, 20, 2, false);
case!(retained_n20_f8, 20, 3, false);
case!(retained_n21_f2, 21, 1, false);
case!(retained_n21_f4, 21, 2, false);
case!(retained_n21_f8, 21, 3, false);
case!(retained_n24_f2, 24, 1, false);
case!(retained_n24_f4, 24, 2, false);
case!(retained_n24_f8, 24, 3, false);
case!(retained_n24_f2_two_pass, 24, 1, true);
case!(retained_n24_f4_two_pass, 24, 2, true);
case!(retained_n24_f8_two_pass, 24, 3, true);

case!(retained_n22_f2, 22, 1, false);
case!(retained_n22_f8, 22, 3, false);
case!(retained_n23_f2, 23, 1, false);
case!(retained_n23_f8, 23, 3, false);
case!(retained_n23_f2_two_pass, 23, 1, true);
