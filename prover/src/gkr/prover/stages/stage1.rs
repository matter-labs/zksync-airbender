use super::*;
use crate::gkr::whir::{hypercube_to_monomial, ColumnMajorBaseOracleForLDE};
use fft::Twiddles;
use fft::{
    bitreverse_enumeration_inplace, distribute_powers_serial, domain_generator_for_size,
    materialize_powers_serial_starting_with_one, GoodAllocator,
};
use field::{Field, FieldExtension, PrimeField, TwoAdicField};
use std::sync::Arc;

#[derive(Clone, Debug)]
pub struct ColumnMajorCosetBoundTracePart<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
> {
    pub column: Arc<Box<[E]>>,
    pub offset: F,
}

pub fn compute_column_major_lde_from_main_domain<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    A: GoodAllocator,
>(
    source_domain: Arc<Box<[E]>>,
    twiddles: &Twiddles<F, A>,
    // lde_precomputations: &LdePrecomputations<A>,
    lde_factor: usize,
) -> Vec<ColumnMajorCosetBoundTracePart<F, E>> {
    let mut result = Vec::with_capacity(lde_factor);
    result.push(ColumnMajorCosetBoundTracePart {
        column: Arc::clone(&source_domain),
        offset: F::ONE,
    });
    let other_domains =
        compute_column_major_lde_from_main_domain_inner(&source_domain[..], twiddles, lde_factor);
    result.extend(other_domains.into_iter().map(|(column, offset)| {
        ColumnMajorCosetBoundTracePart {
            column: Arc::new(column),
            offset,
        }
    }));

    result
}

pub(crate) fn compute_column_major_lde_from_main_domain_inner<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    A: GoodAllocator,
>(
    source_domain: &[E],
    twiddles: &Twiddles<F, A>,
    // lde_precomputations: &LdePrecomputations<A>,
    lde_factor: usize,
) -> Vec<(Box<[E]>, F)> {
    assert!(lde_factor.is_power_of_two());

    assert!(lde_factor > 1, "No reason to call this function");

    let trace_len_log2 = source_domain.len().trailing_zeros();

    let mut ifft: Box<[E]> = source_domain.to_vec().into_boxed_slice();
    fft::naive::cache_friendly_ntt_natural_to_bitreversed(
        &mut ifft[..],
        trace_len_log2,
        &twiddles.inverse_twiddles[..],
    );

    let mut ifft = Some(ifft);

    let next_root = domain_generator_for_size::<F>(((1 << trace_len_log2) * lde_factor) as u64);
    let root_powers =
        materialize_powers_serial_starting_with_one::<F, Global>(next_root, lde_factor);
    assert_eq!(root_powers[0], F::ONE);

    let mut result = Vec::with_capacity(lde_factor - 1);

    let roots = &root_powers[1..];
    let size_inv = F::from_u32_unchecked(1 << trace_len_log2)
        .inverse()
        .unwrap();

    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();
    for i in 0..(lde_factor - 1) {
        let mut source = if i == (lde_factor - 2) {
            ifft.take().unwrap()
        } else {
            ifft.as_ref().unwrap().clone()
        };
        // TODO: very stupid and slow...
        bitreverse_enumeration_inplace(&mut source[..]);
        // normalize by 1/N
        let offset = roots[i];
        distribute_powers_serial(&mut source[..], size_inv, offset);
        bitreverse_enumeration_inplace(&mut source[..]);
        fft::naive::serial_ct_ntt_bitreversed_to_natural(
            &mut source[..],
            trace_len_log2,
            &twiddles.forward_twiddles,
        );
        result.push((source, offset));
    }
    #[cfg(feature = "timing_logs")]
    dbg!(now.elapsed());

    assert!(ifft.is_none());
    assert_eq!(result.len(), lde_factor - 1);

    result
}

pub(crate) fn compute_column_major_lde_from_main_domain_and_output_monomial_form<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    A: GoodAllocator,
>(
    source_domain: &[E],
    twiddles: &Twiddles<F, A>,
    // lde_precomputations: &LdePrecomputations<A>,
    lde_factor: usize,
) -> (Vec<(Box<[E]>, F)>, Vec<E>) {
    assert!(lde_factor.is_power_of_two());

    assert!(lde_factor > 1, "No reason to call this function");

    let trace_len_log2 = source_domain.len().trailing_zeros();

    let mut ifft: Vec<E> = source_domain.to_vec();
    let size_inv = F::from_u32_unchecked(1 << trace_len_log2)
        .inverse()
        .unwrap();
    fft::naive::cache_friendly_ntt_natural_to_bitreversed(
        &mut ifft[..],
        trace_len_log2,
        &twiddles.inverse_twiddles[..],
    );
    for el in ifft.iter_mut() {
        el.mul_assign_by_base(&size_inv);
    }
    bitreverse_enumeration_inplace(&mut ifft[..]);

    let next_root = domain_generator_for_size::<F>(((1 << trace_len_log2) * lde_factor) as u64);
    let root_powers =
        materialize_powers_serial_starting_with_one::<F, Global>(next_root, lde_factor);
    assert_eq!(root_powers[0], F::ONE);

    let mut result = Vec::with_capacity(lde_factor - 1);

    {
        let offset = root_powers[0];
        let mut source = ifft.clone();
        // TODO: very stupid and slow...
        distribute_powers_serial(&mut source[..], F::ONE, offset);
        bitreverse_enumeration_inplace(&mut source[..]);
        fft::naive::serial_ct_ntt_bitreversed_to_natural(
            &mut source[..],
            trace_len_log2,
            &twiddles.forward_twiddles,
        );
        assert_eq!(source, source_domain);
    }

    let roots = &root_powers[1..];

    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();
    for i in 0..(lde_factor - 1) {
        let mut source = ifft.clone();
        // TODO: very stupid and slow...
        let offset = roots[i];
        distribute_powers_serial(&mut source[..], F::ONE, offset);
        bitreverse_enumeration_inplace(&mut source[..]);
        fft::naive::serial_ct_ntt_bitreversed_to_natural(
            &mut source[..],
            trace_len_log2,
            &twiddles.forward_twiddles,
        );
        result.push((source.into_boxed_slice(), offset));
    }
    #[cfg(feature = "timing_logs")]
    dbg!(now.elapsed());

    assert_eq!(result.len(), lde_factor - 1);

    (result, ifft)
}

pub(crate) fn compute_column_major_lde_from_monomial_form<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    A: GoodAllocator,
>(
    monomial_form_normal_order: &[E],
    twiddles: &Twiddles<F, A>,
    lde_factor: usize,
    worker: Option<&Worker>,
) -> Vec<(Box<[E]>, F)> {
    assert!(lde_factor.is_power_of_two());

    assert!(lde_factor > 1, "No reason to call this function");

    let trace_len_log2 = monomial_form_normal_order.len().trailing_zeros();

    let next_root = domain_generator_for_size::<F>(((1 << trace_len_log2) * lde_factor) as u64);
    let root_powers =
        materialize_powers_serial_starting_with_one::<F, Global>(next_root, lde_factor);
    assert_eq!(root_powers[0], F::ONE);

    assert!(twiddles.forward_twiddles.len() >= (1 << (trace_len_log2 - 1)));

    let selected_twiddles = &twiddles.forward_twiddles[..(1 << (trace_len_log2 - 1))];

    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();

    let compute_coset = |i: usize| -> (Box<[E]>, F) {
        let mut evals = monomial_form_normal_order.to_vec();
        let offset = root_powers[i];
        if i != 0 {
            distribute_powers_serial(&mut evals[..], F::ONE, offset);
        }
        bitreverse_enumeration_inplace(&mut evals[..]);
        fft::naive::serial_ct_ntt_bitreversed_to_natural(
            &mut evals[..],
            trace_len_log2,
            selected_twiddles,
        );
        (evals.into_boxed_slice(), offset)
    };

    let result = if let Some(worker) = worker {
        let mut result: Vec<(Box<[E]>, F)> = Vec::with_capacity(lde_factor);
        unsafe { result.set_len(lde_factor) };
        let base_ptr = result.as_mut_ptr();
        worker.scope(lde_factor, |scope, geometry| {
            (0..geometry.len())
                .map(|chunk_idx| {
                    let start = geometry.get_chunk_start_pos(chunk_idx);
                    let size = geometry.get_chunk_size(chunk_idx);
                    let dst = unsafe { base_ptr.add(start) } as usize;
                    (start, size, dst, chunk_idx == geometry.len() - 1)
                })
                .for_each(|(chunk_start, chunk_size, dst, is_last)| {
                    Worker::smart_spawn(scope, is_last, move |_| {
                        let mut dst = dst as *mut (Box<[E]>, F);
                        for i in chunk_start..(chunk_start + chunk_size) {
                            unsafe { dst.write(compute_coset(i)) };
                            dst = unsafe { dst.add(1) };
                        }
                    });
                });
        });
        result
    } else {
        (0..lde_factor).map(compute_coset).collect()
    };

    #[cfg(feature = "timing_logs")]
    dbg!(now.elapsed());

    assert_eq!(result.len(), lde_factor);

    result
}

pub(crate) fn compute_column_major_monomial_form_from_main_domain<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    A: GoodAllocator,
>(
    source_domain: &[E],
    twiddles: &Twiddles<F, A>,
) -> Vec<E> {
    let trace_len_log2 = source_domain.len().trailing_zeros();

    let mut ifft: Vec<E> = source_domain.to_vec();
    let size_inv = F::from_u32_unchecked(1 << trace_len_log2)
        .inverse()
        .unwrap();
    fft::naive::cache_friendly_ntt_natural_to_bitreversed(
        &mut ifft[..],
        trace_len_log2,
        &twiddles.inverse_twiddles[..],
    );
    for el in ifft.iter_mut() {
        el.mul_assign_by_base(&size_inv);
    }
    bitreverse_enumeration_inplace(&mut ifft[..]);

    ifft
}

pub(crate) fn compute_column_major_monomial_form_from_main_domain_owned<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    A: GoodAllocator,
>(
    source_domain: Vec<E>,
    twiddles: &Twiddles<F, A>,
) -> Vec<E> {
    let trace_len_log2 = source_domain.len().trailing_zeros();

    let mut ifft = source_domain;
    let size_inv = F::from_u32_unchecked(1 << trace_len_log2)
        .inverse()
        .unwrap();
    fft::naive::cache_friendly_ntt_natural_to_bitreversed(
        &mut ifft[..],
        trace_len_log2,
        &twiddles.inverse_twiddles[..],
    );
    for el in ifft.iter_mut() {
        el.mul_assign_by_base(&size_inv);
    }
    bitreverse_enumeration_inplace(&mut ifft[..]);

    ifft
}

fn lde_multiple_polys_parallel_from_hypercubes<F: PrimeField + TwoAdicField>(
    evals: &[&[F]],
    twiddles: &Twiddles<F, Global>,
    lde_factor: usize,
    worker: &Worker,
) -> Vec<Vec<ColumnMajorCosetBoundTracePart<F, F>>> {
    let mut cosets = Vec::with_capacity(lde_factor);
    for _ in 0..lde_factor {
        cosets.push(Vec::with_capacity(evals.len()));
    }

    unsafe {
        worker.scope(evals.len(), |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let range = chunk_start..(chunk_start + chunk_size);
                let ptr = SendPtr(cosets.as_mut_ptr());

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let ptr = ptr;
                    for i in range {
                        let mut input = evals[i].to_vec();
                        let size_log2 = input.len().trailing_zeros();

                        bitreverse_enumeration_inplace(&mut input);
                        hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs(
                            &mut input, size_log2,
                        );

                        // RS
                        let cosets = compute_column_major_lde_from_monomial_form(
                            &input, twiddles, lde_factor, None,
                        );
                        for (coset_idx, (coset, offset)) in cosets.into_iter().enumerate() {
                            let trace_part = ColumnMajorCosetBoundTracePart {
                                column: Arc::new(coset),
                                offset,
                            };
                            ptr.0.add(coset_idx).as_mut_unchecked().spare_capacity_mut()[i]
                                .write(trace_part);
                        }
                    }
                });
            }
        });

        for coset in cosets.iter_mut() {
            coset.set_len(evals.len());
        }
    };

    cosets
}

pub fn commit_trace_part<F: PrimeField + TwoAdicField, T: ColumnMajorMerkleTreeConstructor<F>>(
    input_on_hypercube: &[&[F]],
    twiddles: &Twiddles<F, Global>,
    lde_factor: usize,
    whir_first_fold_step_log2: usize,
    tree_cap_size: usize,
    trace_len_log2: usize,
    worker: &Worker,
) -> ColumnMajorBaseOracleForLDE<F, T>
where
    [(); F::DEGREE]: Sized,
{
    let values_per_leaf = 1 << whir_first_fold_step_log2;
    use crate::gkr::whir::ColumnMajorBaseOracleForCoset;
    let evals = lde_multiple_polys_parallel_from_hypercubes(
        input_on_hypercube,
        twiddles,
        lde_factor,
        worker,
    );
    let mut cosets = Vec::with_capacity(lde_factor);
    for coset in evals.into_iter() {
        assert!(coset.len() > 0);
        for el in coset.iter() {
            assert!(el.column.len() > 0);
        }
        let offset = coset[0].offset;
        let trace_part = ColumnMajorBaseOracleForCoset {
            original_values_normal_order: coset,
            offset,
            trace_len_log2,
        };
        cosets.push(trace_part);
    }
    let source: Vec<_> = cosets
        .iter()
        .map(|el| {
            let columns: Vec<_> = el
                .original_values_normal_order
                .iter()
                .map(|el| &el.column[..])
                .collect();

            columns
        })
        .collect();
    let source_ref: Vec<_> = source.iter().map(|el| &el[..]).collect();

    let tree = T::construct_from_cosets::<F, Global>(
        &source_ref[..],
        values_per_leaf,
        tree_cap_size,
        true,
        true,
        false,
        worker,
    );

    ColumnMajorBaseOracleForLDE {
        cosets,
        tree,
        values_per_leaf,
        trace_len_log2,
    }
}

pub fn stage1<F: PrimeField + TwoAdicField, T: ColumnMajorMerkleTreeConstructor<F>>(
    witness_eval_data: &GKRFullWitnessTrace<F, Global, Global>,
    twiddles: &Twiddles<F, Global>,
    lde_factor: usize,
    whir_first_fold_step_log2: usize,
    tree_cap_size: usize,
    trace_len_log2: usize,
    worker: &Worker,
) -> (
    ColumnMajorBaseOracleForLDE<F, T>,
    ColumnMajorBaseOracleForLDE<F, T>,
)
where
    [(); F::DEGREE]: Sized,
{
    let mem_inputs: Vec<_> = witness_eval_data
        .column_major_memory_trace
        .iter()
        .map(|el| &el[..])
        .collect();
    let mem = commit_trace_part(
        &mem_inputs,
        twiddles,
        lde_factor,
        whir_first_fold_step_log2,
        tree_cap_size,
        trace_len_log2,
        worker,
    );

    let wit_inputs: Vec<_> = witness_eval_data
        .column_major_witness_trace
        .iter()
        .map(|el| &el[..])
        .collect();
    let wit = commit_trace_part(
        &wit_inputs,
        twiddles,
        lde_factor,
        whir_first_fold_step_log2,
        tree_cap_size,
        trace_len_log2,
        worker,
    );

    (mem, wit)
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::baby_bear::base::BabyBearField;
    use field::baby_bear::ext4::BabyBearExt4;
    use rand::RngCore;

    type F = BabyBearField;
    type E = BabyBearExt4;

    fn random_monomial_form(size: usize) -> Vec<E> {
        let mut rng = rand::rng();
        (0..size)
            .map(|_| {
                let coeffs = [(); 4].map(|_| F::from_u32_with_reduction(rng.next_u32()));
                <E as FieldExtension<F>>::from_coeffs(coeffs)
            })
            .collect()
    }

    fn run_serial_vs_parallel(poly_size_log2: usize, lde_factor: usize) {
        let worker = Worker::new_with_num_threads(4);
        let poly_size = 1 << poly_size_log2;
        let twiddles = fft::Twiddles::<F, Global>::new(poly_size, &worker);
        let coeffs = random_monomial_form(poly_size);

        let serial = compute_column_major_lde_from_monomial_form::<F, E, Global>(
            &coeffs, &twiddles, lde_factor, None,
        );
        let parallel = compute_column_major_lde_from_monomial_form::<F, E, Global>(
            &coeffs,
            &twiddles,
            lde_factor,
            Some(&worker),
        );

        assert_eq!(serial.len(), parallel.len());
        for (i, (s, p)) in serial.iter().zip(parallel.iter()).enumerate() {
            assert_eq!(s.1, p.1, "offset mismatch at coset {i}");
            assert_eq!(s.0[..], p.0[..], "evals mismatch at coset {i}");
        }
    }

    #[test]
    fn test_lde_serial_vs_parallel_lde2() {
        run_serial_vs_parallel(10, 2);
        run_serial_vs_parallel(14, 2);
        run_serial_vs_parallel(18, 2);
    }

    #[test]
    fn test_lde_serial_vs_parallel_lde4() {
        run_serial_vs_parallel(10, 4);
        run_serial_vs_parallel(14, 4);
    }

    #[test]
    fn test_lde_serial_vs_parallel_lde8() {
        run_serial_vs_parallel(10, 8);
        run_serial_vs_parallel(14, 8);
    }
}
