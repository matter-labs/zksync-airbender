//! Launchers for the symbolic in-domain step split around a PoW-gated folding
//! draw (`in_domain.cu`): correct the reductions and commit the round
//! polynomial, then fold the terms with the challenge drawn in between.

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::utils::get_grid_block_dims_for_threads_count;
use gpu_hash::blake2s::STATE_SIZE;

/// Must equal `WHIR_IN_DOMAIN_BLOCK_THREADS` in `in_domain.cu`: the one-CTA
/// correction reduces exactly this many partials.
const CORRECT_BLOCK_THREADS: u32 = 256;
const FOLD_BLOCK_THREADS: u32 = 128;

cuda_kernel_signature_arguments_and_function!(
    WhirInDomainCorrectAndCommit,
    leaves: *const E4,
    leaf_stride: u32,
    leaf_width: u32,
    weights: *const E4,
    points: *const BF,
    reductions: *mut E4,
    seed_io: *mut u32,
    coeffs_out: *mut E4,
    count: u32,
);

cuda_kernel_declaration!(
    ab_whir_in_domain_correct_and_commit_kernel(
        leaves: *const E4,
        leaf_stride: u32,
        leaf_width: u32,
        weights: *const E4,
        points: *const BF,
        reductions: *mut E4,
        seed_io: *mut u32,
        coeffs_out: *mut E4,
        count: u32,
    )
);

cuda_kernel_signature_arguments_and_function!(
    WhirInDomainFoldTerms,
    leaves: *mut E4,
    leaf_stride: u32,
    leaf_width: u32,
    weights: *mut E4,
    points: *mut BF,
    exponents: *mut u32,
    challenge: *const E4,
    count: u32,
);

cuda_kernel_declaration!(
    ab_whir_in_domain_fold_terms_kernel(
        leaves: *mut E4,
        leaf_stride: u32,
        leaf_width: u32,
        weights: *mut E4,
        points: *mut BF,
        exponents: *mut u32,
        challenge: *const E4,
        count: u32,
    )
);

fn term_count(weights_len: usize, points_len: usize) -> u32 {
    assert_eq!(points_len, weights_len);
    let count = u32::try_from(weights_len).expect("term count must fit u32");
    assert!(count > 0, "split symbolic step needs terms");
    count
}

fn check_leaf_geometry(leaves_len: usize, leaf_stride: u32, leaf_width: u32, count: u32) {
    assert!(leaf_width >= 2 && leaf_width.is_multiple_of(2));
    assert!(leaf_width <= leaf_stride);
    assert_eq!(leaves_len, count as usize * leaf_stride as usize);
}

/// Adds the terms' `[h(0), h(1), 4 h(1/2)]` to `reductions`, then writes the
/// round polynomial to `coefficients` and commits it into `seed`. Draws no
/// challenge and leaves the terms unfolded.
pub(crate) fn correct_and_commit(
    leaves: &DeviceSlice<E4>,
    leaf_stride: u32,
    leaf_width: u32,
    weights: &DeviceSlice<E4>,
    points: &DeviceSlice<BF>,
    reductions: &mut DeviceSlice<E4>,
    seed: &mut DeviceSlice<u32>,
    coefficients: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = term_count(weights.len(), points.len());
    check_leaf_geometry(leaves.len(), leaf_stride, leaf_width, count);
    assert!(reductions.len() >= 3);
    assert_eq!(seed.len(), STATE_SIZE);
    assert_eq!(coefficients.len(), 3);
    let config = CudaLaunchConfig::basic(1, CORRECT_BLOCK_THREADS, stream);
    let args = WhirInDomainCorrectAndCommitArguments::new(
        leaves.as_ptr(),
        leaf_stride,
        leaf_width,
        weights.as_ptr(),
        points.as_ptr(),
        reductions.as_mut_ptr(),
        seed.as_mut_ptr(),
        coefficients.as_mut_ptr(),
        count,
    );
    WhirInDomainCorrectAndCommitFunction(ab_whir_in_domain_correct_and_commit_kernel)
        .launch(&config, &args)
}

/// Folds every term's leaf pairs, weight, point and angle by the
/// device-resident `challenge`.
pub(crate) fn fold_terms(
    leaves: &mut DeviceSlice<E4>,
    leaf_stride: u32,
    leaf_width: u32,
    weights: &mut DeviceSlice<E4>,
    points: &mut DeviceSlice<BF>,
    exponents: &mut DeviceSlice<u32>,
    challenge: &DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = term_count(weights.len(), points.len());
    assert_eq!(exponents.len(), count as usize);
    check_leaf_geometry(leaves.len(), leaf_stride, leaf_width, count);
    assert_eq!(challenge.len(), 1);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(FOLD_BLOCK_THREADS, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = WhirInDomainFoldTermsArguments::new(
        leaves.as_mut_ptr(),
        leaf_stride,
        leaf_width,
        weights.as_mut_ptr(),
        points.as_mut_ptr(),
        exponents.as_mut_ptr(),
        challenge.as_ptr(),
        count,
    );
    WhirInDomainFoldTermsFunction(ab_whir_in_domain_fold_terms_kernel).launch(&config, &args)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::make_test_context;
    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use field::{Field, FieldExtension, PrimeField, Rand};
    use prover::transcript::{Blake2sTranscript, Seed};
    use rand::{rng, Rng};

    const LOG_V: usize = 5;
    const LEAF_WIDTH: usize = 1 << LOG_V;
    const LEAF_STRIDE: usize = 2 * LEAF_WIDTH;

    fn upload<T: Copy>(src: &[T], stream: &CudaStream) -> DeviceAllocation<T> {
        let mut dst = DeviceAllocation::alloc(src.len()).unwrap();
        memory_copy_async(&mut dst, src, stream).unwrap();
        dst
    }

    fn download<T: Copy + Default>(src: &DeviceSlice<T>, stream: &CudaStream) -> Vec<T> {
        let mut host = vec![T::default(); src.len()];
        memory_copy_async(&mut host[..], src, stream).unwrap();
        stream.synchronize().unwrap();
        host
    }

    fn random_point() -> BF {
        loop {
            let point = BF::from_u32_with_reduction(rng().random());
            if !point.is_zero() {
                return point;
            }
        }
    }

    struct Terms {
        leaves: Vec<E4>,
        weights: Vec<E4>,
        points: Vec<BF>,
        exponents: Vec<u32>,
    }

    impl Terms {
        fn random(count: usize) -> Self {
            Self {
                leaves: (0..count * LEAF_STRIDE)
                    .map(|_| E4::random_element(&mut rng()))
                    .collect(),
                weights: (0..count).map(|_| E4::random_element(&mut rng())).collect(),
                points: (0..count).map(|_| random_point()).collect(),
                exponents: (0..count).map(|_| rng().random()).collect(),
            }
        }

        /// Host mirror of `fold_term` for every term at `width`.
        fn fold(&mut self, width: usize, alpha: E4) {
            for t in 0..self.weights.len() {
                let leaf = &mut self.leaves[t * LEAF_STRIDE..t * LEAF_STRIDE + width];
                for j in 0..width / 2 {
                    let mut folded = leaf[2 * j + 1];
                    folded.mul_assign(&alpha);
                    folded.add_assign(&leaf[2 * j]);
                    leaf[j] = folded;
                }
                let rho = self.points[t];
                let mut two_rho_minus_one = rho;
                two_rho_minus_one.double();
                two_rho_minus_one.sub_assign(&BF::ONE);
                let mut one_minus_rho = BF::ONE;
                one_minus_rho.sub_assign(&rho);
                let mut eq_factor = alpha;
                eq_factor.mul_assign_by_base(&two_rho_minus_one);
                eq_factor.add_assign(&E4::from_base(one_minus_rho));
                self.weights[t].mul_assign(&eq_factor);
                self.points[t].square();
                self.exponents[t] = self.exponents[t].wrapping_shl(1);
            }
        }
    }

    struct DeviceStep {
        leaves: DeviceAllocation<E4>,
        weights: DeviceAllocation<E4>,
        points: DeviceAllocation<BF>,
        exponents: DeviceAllocation<u32>,
        reductions: DeviceAllocation<E4>,
        seed: DeviceAllocation<u32>,
        coefficients: DeviceAllocation<E4>,
        challenge: DeviceAllocation<E4>,
    }

    impl DeviceStep {
        fn upload(terms: &Terms, seed: &[u32], stream: &CudaStream) -> Self {
            Self {
                leaves: upload(&terms.leaves, stream),
                weights: upload(&terms.weights, stream),
                points: upload(&terms.points, stream),
                exponents: upload(&terms.exponents, stream),
                reductions: DeviceAllocation::alloc(4).unwrap(),
                seed: upload(seed, stream),
                coefficients: DeviceAllocation::alloc(3).unwrap(),
                challenge: DeviceAllocation::alloc(1).unwrap(),
            }
        }

        fn correct_and_commit(&mut self, width: usize, stream: &CudaStream) {
            correct_and_commit(
                &self.leaves,
                LEAF_STRIDE as u32,
                width as u32,
                &self.weights,
                &self.points,
                &mut self.reductions,
                &mut self.seed,
                &mut self.coefficients,
                stream,
            )
            .unwrap();
        }

        fn fold_terms(&mut self, width: usize, stream: &CudaStream) {
            fold_terms(
                &mut self.leaves,
                LEAF_STRIDE as u32,
                width as u32,
                &mut self.weights,
                &mut self.points,
                &mut self.exponents,
                &self.challenge,
                stream,
            )
            .unwrap();
        }

        fn assert_terms(&self, host: &Terms, width: usize, label: &str, stream: &CudaStream) {
            let leaves = download(&self.leaves, stream);
            for t in 0..host.weights.len() {
                let range = t * LEAF_STRIDE..t * LEAF_STRIDE + width;
                assert_eq!(
                    leaves[range.clone()],
                    host.leaves[range],
                    "{label}: term {t}"
                );
            }
            assert_eq!(download(&self.weights, stream), host.weights, "{label}");
            assert_eq!(download(&self.points, stream), host.points, "{label}");
            assert_eq!(download(&self.exponents, stream), host.exponents, "{label}");
        }
    }

    #[test]
    fn split_steps_match_fused_kernel() {
        let stream = CudaStream::default();
        for count in [1usize, 137, 300] {
            let terms = Terms::random(count);
            let seed: Vec<u32> = (0..STATE_SIZE).map(|_| rng().random()).collect();
            let mut fused = DeviceStep::upload(&terms, &seed, &stream);
            let mut split = DeviceStep::upload(&terms, &seed, &stream);
            for step in 0..LOG_V {
                let width = LEAF_WIDTH >> step;
                let reductions: Vec<E4> = (0..4).map(|_| E4::random_element(&mut rng())).collect();
                memory_copy_async(&mut fused.reductions, &reductions[..], &stream).unwrap();
                memory_copy_async(&mut split.reductions, &reductions[..], &stream).unwrap();
                crate::in_domain::correct_update_and_fold(
                    &mut fused.leaves,
                    LEAF_STRIDE as u32,
                    width as u32,
                    &mut fused.weights,
                    &mut fused.points,
                    &mut fused.exponents,
                    &mut fused.reductions,
                    &mut fused.seed,
                    &mut fused.coefficients,
                    &mut fused.challenge,
                    &stream,
                )
                .unwrap();
                split.correct_and_commit(width, &stream);
                // The plain draw is the fused kernel's: fold with the same
                // challenge.
                memory_copy_async(&mut split.challenge, &fused.challenge, &stream).unwrap();
                split.fold_terms(width, &stream);
                let label = format!("count {count} step {step}");
                for (a, b) in [
                    (&fused.reductions, &split.reductions),
                    (&fused.coefficients, &split.coefficients),
                ] {
                    assert_eq!(download(a, &stream), download(b, &stream), "{label}");
                }
                assert_eq!(
                    download(&fused.seed, &stream),
                    download(&split.seed, &stream),
                    "{label}"
                );
                let host = Terms {
                    leaves: download(&fused.leaves, &stream),
                    weights: download(&fused.weights, &stream),
                    points: download(&fused.points, &stream),
                    exponents: download(&fused.exponents, &stream),
                };
                split.assert_terms(&host, width / 2, &label, &stream);
            }
        }
    }

    #[test]
    fn split_step_with_pow_draw_matches_host_transcript_and_fold() {
        let context = make_test_context(64, 16);
        let stream = context.get_exec_stream();
        let count = 137;
        let mut host = Terms::random(count);
        let seed: Vec<u32> = (0..STATE_SIZE).map(|_| rng().random()).collect();
        let mut device = DeviceStep::upload(&host, &seed, stream);
        let mut nonce: DeviceAllocation<u64> = DeviceAllocation::alloc(1).unwrap();
        for (step, pow_bits) in [1u32, 8, 16, 22, 23].into_iter().enumerate() {
            let width = LEAF_WIDTH >> step;
            let reductions: Vec<E4> = (0..4).map(|_| E4::random_element(&mut rng())).collect();
            memory_copy_async(&mut device.reductions, &reductions[..], stream).unwrap();
            device.correct_and_commit(width, stream);
            let committed = Seed(download(&device.seed, stream).try_into().unwrap());
            crate::pow::schedule_draw_e4_challenges_with_pow(
                &mut device.seed,
                &mut device.challenge,
                pow_bits,
                &mut nonce[0],
                &context,
            )
            .unwrap();
            device.fold_terms(width, stream);

            // Host transcript: `verify_pow` (panics on an invalid nonce), then
            // the PoW-aware draw skips the header word.
            let device_nonce = download(&nonce, stream)[0];
            let mut expected_seed = committed;
            <Blake2sTranscript>::verify_pow(&mut expected_seed, device_nonce, pow_bits);
            let mut words = [0u32; STATE_SIZE];
            <Blake2sTranscript>::draw_randomness(&mut expected_seed, &mut words);
            let alpha = E4::from_array_of_base(std::array::from_fn(|i| {
                BF::from_raw_repr_with_reduction(words[1 + i])
            }));
            #[cfg(feature = "deterministic_pow")]
            {
                use prover::gkr::prover::transcript_utils::draw_random_field_els_with_pow;
                let mut host_seed = committed;
                let (expected_nonce, expected) =
                    draw_random_field_els_with_pow::<BF, E4, Blake2sTranscript>(
                        &mut host_seed,
                        1,
                        pow_bits,
                        &worker::Worker::new(),
                    );
                assert_eq!(host_seed.0, expected_seed.0, "step {step}: host seed paths");
                assert_eq!(
                    device_nonce, expected_nonce,
                    "step {step}: deterministic nonce"
                );
                assert_eq!(expected[0], alpha, "step {step}: host draw paths");
            }
            assert_eq!(download(&device.challenge, stream)[0], alpha, "step {step}");
            assert_eq!(
                download(&device.seed, stream),
                expected_seed.0,
                "step {step}"
            );

            host.fold(width, alpha);
            device.assert_terms(&host, width / 2, &format!("step {step}"), stream);
        }
    }
}
