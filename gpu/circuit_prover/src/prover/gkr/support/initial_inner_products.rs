use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use crate::primitives::field::E4;

cuda_kernel!(
    InitialInnerProductE4,
    ab_initial_inner_product_e4_kernel(
        polys_base: *const E4,
        eq_values: *const E4,
        poly_len: u32,
        claims_out: *mut E4
    )
);

/// One-launch fused initial inner product: for each block index `i`, compute
/// `claims_out[i] = sum_j polys[i][j] * eq_values[j]` over `poly_len` E4
/// elements, where the polys are stored contiguously at `polys_base` with
/// stride `poly_len`: poly `i` is `polys_base[i*poly_len .. (i+1)*poly_len]`.
/// The caller is responsible for arranging the polys in slot order (the
/// post-forward construction in `proof.rs` does this implicitly — see the
/// identity-permutation invariant asserted there).
pub(crate) fn initial_inner_product_e4(
    polys_base: *const E4,
    num_polys: usize,
    eq_values: &DeviceSlice<E4>,
    poly_len: u32,
    claims_out: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(claims_out.len(), num_polys);
    assert!(num_polys > 0);
    assert!(num_polys <= u32::MAX as usize);
    assert!(poly_len > 0);
    assert_eq!(eq_values.len(), poly_len as usize);
    let config = CudaLaunchConfig::basic(num_polys as u32, 256u32, stream);
    let args = InitialInnerProductE4Arguments::new(
        polys_base,
        eq_values.as_ptr(),
        poly_len,
        claims_out.as_mut_ptr(),
    );
    InitialInnerProductE4Function::default().launch(&config, &args)
}

#[cfg(test)]
mod tests {
    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use era_cudart::stream::CudaStream;
    use rand::Rng;
    use serial_test::serial;

    use crate::primitives::field::{BaseField, E4};
    use field::{Field, PrimeField};

    fn host_inner_product(poly: &[E4], eq: &[E4]) -> E4 {
        assert_eq!(poly.len(), eq.len());
        let mut sum = E4::ZERO;
        for (p, e) in poly.iter().zip(eq.iter()) {
            let mut t = *p;
            t.mul_assign(e);
            sum.add_assign(&t);
        }
        sum
    }

    fn random_e4<R: Rng>(rng: &mut R) -> E4 {
        E4::from_array_of_base([
            BaseField::from_u64_with_reduction(rng.random()),
            BaseField::from_u64_with_reduction(rng.random()),
            BaseField::from_u64_with_reduction(rng.random()),
            BaseField::from_u64_with_reduction(rng.random()),
        ])
    }

    #[test]
    #[serial]
    fn initial_inner_product_e4_parity() {
        let stream = CudaStream::default();
        let mut rng = rand::rng();
        for &(num_polys, poly_len_log) in &[(1usize, 4u32), (2, 6), (4, 8), (8, 12), (8, 16)] {
            let poly_len = 1usize << poly_len_log;
            let polys: Vec<Vec<E4>> = (0..num_polys)
                .map(|_| (0..poly_len).map(|_| random_e4(&mut rng)).collect())
                .collect();
            let eq: Vec<E4> = (0..poly_len).map(|_| random_e4(&mut rng)).collect();
            let expected: Vec<E4> = polys.iter().map(|p| host_inner_product(p, &eq)).collect();
            // Pack all polys contiguously: poly i lives at
            // `flat[i*poly_len .. (i+1)*poly_len]`.
            let flat: Vec<E4> = polys.iter().flat_map(|p| p.iter().copied()).collect();
            let mut d_flat: DeviceAllocation<E4> =
                DeviceAllocation::alloc(num_polys * poly_len).unwrap();
            memory_copy_async(&mut d_flat, &flat[..], &stream).unwrap();
            let mut d_eq: DeviceAllocation<E4> = DeviceAllocation::alloc(poly_len).unwrap();
            memory_copy_async(&mut d_eq, &eq[..], &stream).unwrap();
            let mut d_claims: DeviceAllocation<E4> = DeviceAllocation::alloc(num_polys).unwrap();
            super::initial_inner_product_e4(
                d_flat.as_ptr(),
                num_polys,
                &d_eq,
                poly_len as u32,
                &mut d_claims,
                &stream,
            )
            .unwrap();
            let mut actual = vec![E4::ZERO; num_polys];
            memory_copy_async(&mut actual[..], &d_claims, &stream).unwrap();
            stream.synchronize().unwrap();
            for (i, (a, e)) in actual.iter().zip(expected.iter()).enumerate() {
                assert_eq!(
                    a, e,
                    "claim mismatch for poly {i} (num_polys={num_polys}, poly_len=2^{poly_len_log})"
                );
            }
        }
    }
}
