use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::utils::get_grid_block_dims_for_threads_count;
use gpu_hash::blake2s::STATE_SIZE;
use gpu_ntt::ntt_twiddles::WhirLeafTransformParams;

const IN_DOMAIN_BLOCK_THREADS: u32 = 256;
const IN_DOMAIN_LEAF_THREADS: u32 = 256;

cuda_kernel_signature_arguments_and_function!(
    WhirInDomainAddTerms,
    indexes: *const u32,
    challenges: *const E4,
    query_domain_log2: u32,
    generator: BF,
    weights: *mut E4,
    points: *mut BF,
    exponents: *mut u32,
    count: u32,
);

cuda_kernel_declaration!(
    ab_whir_in_domain_add_terms_kernel(
        indexes: *const u32,
        challenges: *const E4,
        query_domain_log2: u32,
        generator: BF,
        weights: *mut E4,
        points: *mut BF,
        exponents: *mut u32,
        count: u32,
    )
);

cuda_kernel_signature_arguments_and_function!(
    WhirInDomainPrepareIndexes,
    exponents: *const u32,
    domain_log2: u32,
    log_v: u32,
    indexes: *mut u32,
    count: u32,
);

cuda_kernel_declaration!(
    ab_whir_in_domain_prepare_indexes_kernel(
        exponents: *const u32,
        domain_log2: u32,
        log_v: u32,
        indexes: *mut u32,
        count: u32,
    )
);

fn term_count(weights_len: usize, points_len: usize, exponents_len: usize) -> u32 {
    assert_eq!(points_len, weights_len);
    assert_eq!(exponents_len, weights_len);
    u32::try_from(weights_len).expect("term count must fit u32")
}

fn check_leaf_geometry(leaves_len: usize, leaf_stride: u32, leaf_width: u32, count: u32) {
    assert!(leaf_width >= 2 && leaf_width.is_multiple_of(2));
    assert!(leaf_width <= leaf_stride);
    assert_eq!(leaves_len, count as usize * leaf_stride as usize);
}

/// Appends `count` terms: weight = challenge, point = generator^index, exponent =
/// `index << (32 - query_domain_log2)`. Destinations are already sliced to the new terms.
pub(crate) fn add_terms(
    indexes: &DeviceSlice<u32>,
    challenges: &DeviceSlice<E4>,
    query_domain_log2: u32,
    generator: BF,
    weights: &mut DeviceSlice<E4>,
    points: &mut DeviceSlice<BF>,
    exponents: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = term_count(weights.len(), points.len(), exponents.len());
    assert_eq!(indexes.len(), count as usize);
    assert_eq!(challenges.len(), count as usize);
    assert!(query_domain_log2 <= 32);
    if count == 0 {
        return Ok(());
    }
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(IN_DOMAIN_BLOCK_THREADS, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = WhirInDomainAddTermsArguments::new(
        indexes.as_ptr(),
        challenges.as_ptr(),
        query_domain_log2,
        generator,
        weights.as_mut_ptr(),
        points.as_mut_ptr(),
        exponents.as_mut_ptr(),
        count,
    );
    WhirInDomainAddTermsFunction(ab_whir_in_domain_add_terms_kernel).launch(&config, &args)
}

/// Writes each term's protocol leaf index in the current oracle: the low
/// `domain_log2 - log_v` bits of `exponent >> (32 - domain_log2)`.
pub(crate) fn prepare_indexes(
    exponents: &DeviceSlice<u32>,
    domain_log2: u32,
    log_v: u32,
    indexes: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(indexes.len(), exponents.len());
    assert!(domain_log2 <= 32);
    assert!(log_v <= domain_log2);
    let count = u32::try_from(exponents.len()).expect("term count must fit u32");
    if count == 0 {
        return Ok(());
    }
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(IN_DOMAIN_BLOCK_THREADS, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = WhirInDomainPrepareIndexesArguments::new(
        exponents.as_ptr(),
        domain_log2,
        log_v,
        indexes.as_mut_ptr(),
        count,
    );
    WhirInDomainPrepareIndexesFunction(ab_whir_in_domain_prepare_indexes_kernel)
        .launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    WhirInDomainLeavesFromMonomials,
    coeffs: *const BF,
    transform_params: WhirLeafTransformParams,
    log_n: u32,
    log_c: u32,
    log_v: u32,
    tree_indexes: *const u32,
    leaves: *mut E4,
    count: u32,
);

cuda_kernel_declaration!(
    ab_whir_in_domain_leaves_from_monomials_kernel(
        coeffs: *const BF,
        transform_params: WhirLeafTransformParams,
        log_n: u32,
        log_c: u32,
        log_v: u32,
        tree_indexes: *const u32,
        leaves: *mut E4,
        count: u32,
    )
);

/// Writes each term's natural-order coefficient leaf `[P_0(x^V) .. P_{V-1}(x^V)]`
/// straight from a recomputed oracle's bit-reversed limb columns (`4 << log_n`
/// BF), addressed by tree index like the residue query kernels.
pub(crate) fn leaves_from_monomials(
    coeffs: &DeviceSlice<BF>,
    params: WhirLeafTransformParams,
    log_n: u32,
    log_c: u32,
    log_v: u32,
    tree_indexes: &DeviceSlice<u32>,
    leaves: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        log_v <= 5,
        "leaf width must fit one 256-thread block interleave"
    );
    assert!(log_n >= log_v);
    let log_m = log_n - log_v;
    assert!(
        log_m <= 8,
        "slot polynomials must fit the block-family sizes"
    );
    assert!(log_c >= 1);
    assert!(log_m + log_c <= params.omega_log_order);
    assert_eq!(coeffs.len(), 4usize << log_n);
    assert_eq!(leaves.len(), tree_indexes.len() << log_v);
    let count = u32::try_from(tree_indexes.len()).expect("term count must fit u32");
    if count == 0 {
        return Ok(());
    }
    let config = CudaLaunchConfig::basic(count, IN_DOMAIN_LEAF_THREADS, stream);
    let args = WhirInDomainLeavesFromMonomialsArguments::new(
        coeffs.as_ptr(),
        params,
        log_n,
        log_c,
        log_v,
        tree_indexes.as_ptr(),
        leaves.as_mut_ptr(),
        count,
    );
    WhirInDomainLeavesFromMonomialsFunction(ab_whir_in_domain_leaves_from_monomials_kernel)
        .launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    WhirInDomainCorrectUpdateAndFold,
    leaves: *mut E4,
    leaf_stride: u32,
    leaf_width: u32,
    weights: *mut E4,
    points: *mut BF,
    exponents: *mut u32,
    reductions: *mut E4,
    seed_io: *mut u32,
    coeffs_out: *mut E4,
    challenge_out: *mut E4,
    count: u32,
);

cuda_kernel_declaration!(
    ab_whir_in_domain_correct_update_and_fold_kernel(
        leaves: *mut E4,
        leaf_stride: u32,
        leaf_width: u32,
        weights: *mut E4,
        points: *mut BF,
        exponents: *mut u32,
        reductions: *mut E4,
        seed_io: *mut u32,
        coeffs_out: *mut E4,
        challenge_out: *mut E4,
        count: u32,
    )
);

/// Correct the sumcheck reductions, update the transcript, and fold the
/// symbolic terms with the derived challenge in one launch.
pub(crate) fn correct_update_and_fold(
    leaves: &mut DeviceSlice<E4>,
    leaf_stride: u32,
    leaf_width: u32,
    weights: &mut DeviceSlice<E4>,
    points: &mut DeviceSlice<BF>,
    exponents: &mut DeviceSlice<u32>,
    reductions: &mut DeviceSlice<E4>,
    seed: &mut DeviceSlice<u32>,
    coefficients: &mut DeviceSlice<E4>,
    challenge: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = term_count(weights.len(), points.len(), exponents.len());
    assert!(
        count > 0,
        "fused symbolic step needs terms; empty steps use whir_fold_round_update alone"
    );
    check_leaf_geometry(leaves.len(), leaf_stride, leaf_width, count);
    assert!(reductions.len() >= 3);
    assert_eq!(seed.len(), STATE_SIZE);
    assert_eq!(coefficients.len(), 3);
    assert_eq!(challenge.len(), 1);
    let config = CudaLaunchConfig::basic(1, IN_DOMAIN_BLOCK_THREADS, stream);
    let args = WhirInDomainCorrectUpdateAndFoldArguments::new(
        leaves.as_mut_ptr(),
        leaf_stride,
        leaf_width,
        weights.as_mut_ptr(),
        points.as_mut_ptr(),
        exponents.as_mut_ptr(),
        reductions.as_mut_ptr(),
        seed.as_mut_ptr(),
        coefficients.as_mut_ptr(),
        challenge.as_mut_ptr(),
        count,
    );
    WhirInDomainCorrectUpdateAndFoldFunction(ab_whir_in_domain_correct_update_and_fold_kernel)
        .launch(&config, &args)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::make_test_context;
    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use fft::domain_generator_for_size;
    use field::{Field, FieldExtension, Rand};
    use gpu_hash::blake2s::{Digest, STATE_SIZE};
    use gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS;
    use rand::{rng, Rng};

    fn download<T: Copy>(src: &DeviceSlice<T>, fill: T, stream: &CudaStream) -> Vec<T> {
        let mut host = vec![fill; src.len()];
        memory_copy_async(&mut host[..], src, stream).unwrap();
        stream.synchronize().unwrap();
        host
    }

    fn host_angle(index: u32, query_domain_log2: u32) -> u32 {
        if query_domain_log2 == 0 {
            0
        } else {
            index << (32 - query_domain_log2)
        }
    }

    fn host_prepare_index(angle: u32, domain_log2: u32, log_v: u32) -> u32 {
        let e = if domain_log2 == 0 {
            0
        } else {
            angle >> (32 - domain_log2)
        };
        let leaves_log2 = domain_log2 - log_v;
        if leaves_log2 >= 32 {
            e
        } else {
            e & ((1u32 << leaves_log2) - 1)
        }
    }

    struct HostTerms {
        weights: Vec<E4>,
        points: Vec<BF>,
        exponents: Vec<u32>,
    }

    struct DeviceTerms {
        weights: DeviceAllocation<E4>,
        points: DeviceAllocation<BF>,
        exponents: DeviceAllocation<u32>,
    }

    /// Appends one batch per `(query_domain_log2, count)` through `add_terms`
    /// into consecutive slices and returns the host-side expectation.
    fn add_batches(
        batches: &[(u32, usize)],
        device: &mut DeviceTerms,
        stream: &CudaStream,
    ) -> HostTerms {
        let mut host = HostTerms {
            weights: Vec::new(),
            points: Vec::new(),
            exponents: Vec::new(),
        };
        let mut offset = 0;
        for &(query_domain_log2, count) in batches {
            let generator = domain_generator_for_size::<BF>(1u64 << query_domain_log2);
            let indexes = (0..count)
                .map(|_| rng().random_range(0..(1u64 << query_domain_log2)) as u32)
                .collect::<Vec<_>>();
            let challenges = (0..count)
                .map(|_| E4::random_element(&mut rng()))
                .collect::<Vec<_>>();
            let mut d_indexes = DeviceAllocation::alloc(count).unwrap();
            let mut d_challenges = DeviceAllocation::alloc(count).unwrap();
            memory_copy_async(&mut d_indexes, &indexes[..], stream).unwrap();
            memory_copy_async(&mut d_challenges, &challenges[..], stream).unwrap();
            let end = offset + count;
            add_terms(
                &d_indexes[..],
                &d_challenges[..],
                query_domain_log2,
                generator,
                &mut device.weights[offset..end],
                &mut device.points[offset..end],
                &mut device.exponents[offset..end],
                stream,
            )
            .unwrap();
            stream.synchronize().unwrap();
            for (index, challenge) in indexes.iter().zip(challenges.iter()) {
                host.weights.push(*challenge);
                host.points.push(generator.pow(*index));
                host.exponents.push(host_angle(*index, query_domain_log2));
            }
            offset = end;
        }
        host
    }

    fn assert_terms_match(device: &DeviceTerms, host: &HostTerms, stream: &CudaStream) {
        assert_eq!(
            download(&device.weights[..], E4::ZERO, stream),
            host.weights
        );
        assert_eq!(download(&device.points[..], BF::ZERO, stream), host.points);
        assert_eq!(
            download(&device.exponents[..], 0u32, stream),
            host.exponents
        );
    }

    /// Hypercube evaluations of natural-order monomial coefficients (LSB = variable 0).
    fn hypercube_evals(coeffs: &[E4]) -> Vec<E4> {
        let mut evals = coeffs.to_vec();
        let mut bit = 1;
        while bit < evals.len() {
            for b in 0..evals.len() {
                if b & bit != 0 {
                    let low = evals[b ^ bit];
                    evals[b].add_assign(&low);
                }
            }
            bit <<= 1;
        }
        evals
    }

    /// Dense `sum_t w_t * eq(b, (rho_t, rho_t^2, rho_t^4, ...))` over the hypercube.
    fn dense_eq(host: &HostTerms, log_n: usize) -> Vec<E4> {
        let mut eq = vec![E4::ZERO; 1 << log_n];
        for (w, rho) in host.weights.iter().zip(host.points.iter()) {
            let mut table = vec![*w];
            let mut z = *rho;
            for _ in 0..log_n {
                let mut next = Vec::with_capacity(table.len() * 2);
                let mut one_minus_z = BF::ONE;
                one_minus_z.sub_assign(&z);
                for value in table.iter() {
                    let mut low = *value;
                    low.mul_assign_by_base(&one_minus_z);
                    next.push(low);
                }
                for value in table.iter() {
                    let mut high = *value;
                    high.mul_assign_by_base(&z);
                    next.push(high);
                }
                // variable j is bit j: the new bit is the highest so far
                table = next;
                z.square();
            }
            for (acc, value) in eq.iter_mut().zip(table.iter()) {
                acc.add_assign(value);
            }
        }
        eq
    }

    fn three_point_sums(evals: &[E4], eq: &[E4]) -> [E4; 3] {
        let mut sums = [E4::ZERO; 3];
        for i in 0..evals.len() / 2 {
            let mut p0 = evals[2 * i];
            p0.mul_assign(&eq[2 * i]);
            sums[0].add_assign(&p0);
            let mut p1 = evals[2 * i + 1];
            p1.mul_assign(&eq[2 * i + 1]);
            sums[1].add_assign(&p1);
            let mut ev = evals[2 * i];
            ev.add_assign(&evals[2 * i + 1]);
            let mut eqs = eq[2 * i];
            eqs.add_assign(&eq[2 * i + 1]);
            ev.mul_assign(&eqs);
            sums[2].add_assign(&ev);
        }
        sums
    }

    fn coefficient_leaf(coeffs: &[E4], rho: BF, leaf_width: usize) -> Vec<E4> {
        let y = rho.pow(leaf_width as u32);
        (0..leaf_width)
            .map(|s| {
                let mut acc = E4::ZERO;
                for u in (0..coeffs.len() / leaf_width).rev() {
                    acc.mul_assign_by_base(&y);
                    acc.add_assign(&coeffs[s + leaf_width * u]);
                }
                acc
            })
            .collect()
    }

    fn fold_pairs(values: &[E4], alpha: &E4) -> Vec<E4> {
        (0..values.len() / 2)
            .map(|j| {
                let mut v = values[2 * j + 1];
                v.mul_assign(alpha);
                v.add_assign(&values[2 * j]);
                v
            })
            .collect()
    }

    #[test]
    fn add_and_prepare_follow_cpu_conventions_including_domain_zero() {
        let stream = CudaStream::default();
        let batches = [(0u32, 3usize), (5, 40), (27, 300)];
        let total = batches.iter().map(|b| b.1).sum::<usize>();
        let mut device = DeviceTerms {
            weights: DeviceAllocation::alloc(total).unwrap(),
            points: DeviceAllocation::alloc(total).unwrap(),
            exponents: DeviceAllocation::alloc(total).unwrap(),
        };
        let host = add_batches(&batches, &mut device, &stream);
        assert_terms_match(&device, &host, &stream);
        assert!(host.points[..3].iter().all(|p| *p == BF::ONE));

        let mut d_indexes = DeviceAllocation::alloc(total).unwrap();
        for (domain_log2, log_v) in [(0u32, 0u32), (5, 5), (27, 5), (27, 0), (3, 1)] {
            prepare_indexes(
                &device.exponents[..],
                domain_log2,
                log_v,
                &mut d_indexes[..],
                &stream,
            )
            .unwrap();
            let expected = host
                .exponents
                .iter()
                .map(|angle| host_prepare_index(*angle, domain_log2, log_v))
                .collect::<Vec<_>>();
            assert_eq!(download(&d_indexes[..], 0u32, &stream), expected);
        }
    }

    /// 300 terms from two query domains exercise the grid-stride correction
    /// and fold loops; `leaf_stride > leaf_width` exercises striding.
    #[test]
    fn fused_steps_match_dense_reference_with_grid_stride() {
        const LOG_N: usize = 8;
        const LOG_V: usize = 5;
        let leaf_width = 1usize << LOG_V;
        let leaf_stride = 2 * leaf_width;
        let stream = CudaStream::default();
        for count in [1usize, 137, 300] {
            let batches = [(12u32, count - count / 3), (7, count / 3)];
            let total = batches.iter().map(|b| b.1).sum::<usize>();
            let mut device = DeviceTerms {
                weights: DeviceAllocation::alloc(total).unwrap(),
                points: DeviceAllocation::alloc(total).unwrap(),
                exponents: DeviceAllocation::alloc(total).unwrap(),
            };
            let mut host = add_batches(&batches, &mut device, &stream);
            assert_terms_match(&device, &host, &stream);

            let mut coeffs = (0..1usize << LOG_N)
                .map(|_| E4::random_element(&mut rng()))
                .collect::<Vec<_>>();
            let mut host_leaves = vec![E4::ZERO; total * leaf_stride];
            for (t, rho) in host.points.iter().enumerate() {
                let leaf = coefficient_leaf(&coeffs, *rho, leaf_width);
                host_leaves[t * leaf_stride..t * leaf_stride + leaf_width].copy_from_slice(&leaf);
            }
            let mut d_leaves = DeviceAllocation::alloc(host_leaves.len()).unwrap();
            memory_copy_async(&mut d_leaves, &host_leaves[..], &stream).unwrap();
            let mut d_reductions: DeviceAllocation<E4> = DeviceAllocation::alloc(4).unwrap();
            let mut d_alpha: DeviceAllocation<E4> = DeviceAllocation::alloc(1).unwrap();

            let initial_seed: Vec<u32> = (0..STATE_SIZE).map(|_| rng().random()).collect();
            let mut d_seed = DeviceAllocation::alloc(STATE_SIZE).unwrap();
            memory_copy_async(&mut d_seed, &initial_seed[..], &stream).unwrap();
            let mut d_coefficients = DeviceAllocation::alloc(3).unwrap();
            for step in 0..LOG_V {
                let width = leaf_width >> step;
                let evals = hypercube_evals(&coeffs);
                let eq = dense_eq(&host, LOG_N - step);
                let expected = three_point_sums(&evals, &eq);
                let initial = (0..4)
                    .map(|_| E4::random_element(&mut rng()))
                    .collect::<Vec<_>>();
                memory_copy_async(&mut d_reductions, &initial[..], &stream).unwrap();
                correct_update_and_fold(
                    &mut d_leaves[..],
                    leaf_stride as u32,
                    width as u32,
                    &mut device.weights[..],
                    &mut device.points[..],
                    &mut device.exponents[..],
                    &mut d_reductions[..],
                    &mut d_seed[..],
                    &mut d_coefficients[..],
                    &mut d_alpha[..],
                    &stream,
                )
                .unwrap();
                let actual = download(&d_reductions[..], E4::ZERO, &stream);
                for i in 0..3 {
                    let mut want = initial[i];
                    want.add_assign(&expected[i]);
                    assert_eq!(actual[i], want, "step {step} reduction {i}");
                }
                assert_eq!(actual[3], initial[3]);

                let alpha = download(&d_alpha[..], E4::ZERO, &stream)[0];
                assert_ne!(
                    download(&d_seed[..], 0u32, &stream),
                    initial_seed,
                    "seed must advance"
                );
                coeffs = fold_pairs(&coeffs, &alpha);
                for t in 0..total {
                    let rho = host.points[t];
                    let mut two_rho_minus_one = rho;
                    two_rho_minus_one.double();
                    two_rho_minus_one.sub_assign(&BF::ONE);
                    let mut one_minus_rho = BF::ONE;
                    one_minus_rho.sub_assign(&rho);
                    let mut eq_factor = alpha;
                    eq_factor.mul_assign_by_base(&two_rho_minus_one);
                    eq_factor.add_assign(&E4::from_base(one_minus_rho));
                    host.weights[t].mul_assign(&eq_factor);
                    host.points[t].square();
                    host.exponents[t] = host.exponents[t].wrapping_shl(1);
                    let base = t * leaf_stride;
                    let folded = fold_pairs(&host_leaves[base..base + width], &alpha);
                    host_leaves[base..base + width / 2].copy_from_slice(&folded);
                }
                assert_terms_match(&device, &host, &stream);
                let actual_leaves = download(&d_leaves[..], E4::ZERO, &stream);
                for t in 0..total {
                    let base = t * leaf_stride;
                    assert_eq!(
                        &actual_leaves[base..base + width / 2],
                        &host_leaves[base..base + width / 2],
                        "step {step} term {t}"
                    );
                }
            }
        }
    }

    fn bitrev(value: u32, bits: u32) -> u32 {
        if bits == 0 {
            0
        } else {
            value.reverse_bits() >> (32 - bits)
        }
    }

    /// Four limb columns of `n`, each bit-reversed over `log_n`: the layout of
    /// `OracleValues::Recomputed`.
    fn bitreversed_limb_columns(coeffs: &[E4], log_n: u32) -> Vec<BF> {
        let n = coeffs.len();
        let mut columns = crate::e4_coeffs_to_vectorized(coeffs);
        for column in columns.chunks_mut(n) {
            for i in 0..n {
                let j = bitrev(i as u32, log_n) as usize;
                if i < j {
                    column.swap(i, j);
                }
            }
        }
        columns
    }

    /// `P_s(x^V)` for every slot of the leaf at tree index `q`.
    fn host_leaf(coeffs: &[E4], log_m: u32, log_c: u32, log_v: u32, q: u32) -> Vec<E4> {
        let m = 1usize << log_m;
        let v = 1usize << log_v;
        let coset = bitrev(q >> log_m, log_c);
        let row = q & (m as u32 - 1);
        let generator = domain_generator_for_size::<BF>(1u64 << (log_m + log_c));
        let y = generator.pow(coset + (row << log_c));
        (0..v)
            .map(|s| {
                let mut acc = E4::ZERO;
                for u in (0..m).rev() {
                    acc.mul_assign_by_base(&y);
                    acc.add_assign(&coeffs[s + v * u]);
                }
                acc
            })
            .collect()
    }

    fn flatten_limbs(values: &[E4]) -> Vec<BF> {
        values
            .iter()
            .flat_map(|e| [e.c0.c0, e.c0.c1, e.c1.c0, e.c1.c1])
            .collect()
    }

    /// All ten fused (recomputed) shapes, including M = 2 (R > M) and M = 256
    /// (chain length 32): kernel leaves equal an independent host Horner and
    /// the fused query path's leaves, bit for bit.
    #[test]
    fn leaves_from_monomials_match_host_and_fused_query() {
        let context = make_test_context(64, 16);
        let stream = context.get_exec_stream();
        for (log_n, log_c, log_v) in [
            (13u32, 14u32, 5u32),
            (12, 14, 5),
            (11, 15, 5),
            (10, 15, 5),
            (9, 15, 4),
            (8, 19, 4),
            (7, 19, 4),
            (6, 19, 5),
            (5, 19, 4),
            (4, 19, 3),
        ] {
            let log_m = log_n - log_v;
            let log_total_leaves = log_m + log_c;
            let coeffs = (0..1usize << log_n)
                .map(|_| E4::random_element(&mut rng()))
                .collect::<Vec<_>>();
            let columns = bitreversed_limb_columns(&coeffs, log_n);
            let mut d_coeffs = DeviceAllocation::alloc(columns.len()).unwrap();
            memory_copy_async(&mut d_coeffs, &columns[..], stream).unwrap();
            let params = context.ntt_device_context().whir_leaf_transform_params();
            let d_tree: DeviceAllocation<Digest> = DeviceAllocation::alloc(
                2usize << (log_total_leaves - PARTIAL_TREE_REDUCTION_LAYERS),
            )
            .unwrap();
            for count in [1usize, 137, 300] {
                let indexes = (0..count)
                    .map(|_| rng().random_range(0..1u64 << log_total_leaves) as u32)
                    .collect::<Vec<_>>();
                let mut d_indexes = DeviceAllocation::alloc(count).unwrap();
                memory_copy_async(&mut d_indexes, &indexes[..], stream).unwrap();
                let mut d_leaves: DeviceAllocation<E4> =
                    DeviceAllocation::alloc(count << log_v).unwrap();
                leaves_from_monomials(
                    &d_coeffs[..],
                    params,
                    log_n,
                    log_c,
                    log_v,
                    &d_indexes[..],
                    &mut d_leaves[..],
                    stream,
                )
                .unwrap();
                let actual = download(&d_leaves[..], E4::ZERO, stream);
                let expected = indexes
                    .iter()
                    .flat_map(|q| host_leaf(&coeffs, log_m, log_c, log_v, *q))
                    .collect::<Vec<_>>();
                assert_eq!(
                    actual, expected,
                    "host reference ({log_n},{log_c},{log_v}) x{count}"
                );

                let mut d_query_leaves: DeviceAllocation<BF> =
                    DeviceAllocation::alloc(count << (log_v + 2)).unwrap();
                let mut d_paths: DeviceAllocation<u32> = DeviceAllocation::alloc(
                    count * PARTIAL_TREE_REDUCTION_LAYERS as usize * STATE_SIZE,
                )
                .unwrap();
                crate::fused_commit::query(
                    &d_coeffs[..],
                    &d_tree[..],
                    &d_indexes[..],
                    &mut d_query_leaves[..],
                    &mut d_paths[..],
                    log_n,
                    log_c,
                    log_v,
                    log_total_leaves - PARTIAL_TREE_REDUCTION_LAYERS,
                    params,
                    stream,
                )
                .unwrap();
                let query_leaves = download(&d_query_leaves[..], BF::ZERO, stream);
                assert_eq!(
                    flatten_limbs(&actual),
                    query_leaves,
                    "fused query parity ({log_n},{log_c},{log_v}) x{count}"
                );
            }
        }
    }
}
