use super::*;
use ::field::*;
use worker::{IterableWithGeometry, Worker};

pub fn distribute_powers_serial<F: Field, E: FieldExtension<F>>(
    input: &mut [E],
    element_initial: F,
    element_step: F,
) {
    let mut shift = element_initial;
    let mut idx = 0;

    while idx < input.len() {
        input[idx].mul_assign_by_base(&shift);
        shift.mul_assign(&element_step);
        idx += 1;
    }
}

pub fn distribute_powers_parallel<F: Field, E: FieldExtension<F>>(
    input: &mut [E],
    element_initial: F,
    element_step: F,
    worker: &Worker,
) {
    const PAR_THRESHOLD: usize = 1024;
    if input.len() < PAR_THRESHOLD {
        distribute_powers_serial(input, element_initial, element_step);
        return;
    }
    worker.scope(input.len(), |scope, geometry| {
        let num_chunks = geometry.len();
        let ordinary_step = element_step.pow(geometry.ordinary_chunk_size as u32);
        let mut current = element_initial;
        let mut chunk_starts: Vec<F> = Vec::with_capacity(num_chunks);
        for _ in 0..num_chunks {
            chunk_starts.push(current);
            current.mul_assign(&ordinary_step);
        }

        input
            .chunks_for_geometry_mut(geometry)
            .enumerate()
            .for_each(|(idx, chunk)| {
                let chunk_start = chunk_starts[idx];
                Worker::smart_spawn(scope, idx == num_chunks - 1, move |_| {
                    distribute_powers_serial(chunk, chunk_start, element_step);
                });
            });
    });
}

fn materialize_powers_serial_impl<F: Field, A: GoodAllocator>(
    base: F,
    size: usize,
    start_with_one: bool,
) -> Vec<F, A> {
    if size == 0 {
        return Vec::new_in(A::default());
    }
    let mut storage = Vec::with_capacity_in(size, A::default());
    let mut current = if start_with_one { F::ONE } else { base };
    storage.push(current);
    for _ in 1..size {
        current.mul_assign(&base);
        storage.push(current);
    }

    storage
}

// starts the array with F::ONE
pub fn materialize_powers_serial_starting_with_one<F: Field, A: GoodAllocator>(
    base: F,
    size: usize,
) -> Vec<F, A> {
    materialize_powers_serial_impl(base, size, true)
}

// starts the array with base
pub fn materialize_powers_serial_starting_with_elem<F: Field, A: GoodAllocator>(
    base: F,
    size: usize,
) -> Vec<F, A> {
    materialize_powers_serial_impl(base, size, false)
}

pub fn domain_generator_for_size<F: TwoAdicField>(size: u64) -> F {
    debug_assert!(size.is_power_of_two());
    debug_assert!(size.trailing_zeros() as usize <= F::TWO_ADICITY);

    let mut omega = F::two_adic_generator();
    let mut t = omega;
    t.exp_power_of_2(F::TWO_ADICITY);
    assert_eq!(t, F::ONE);
    let mut t = omega;
    for _ in 0..(F::TWO_ADICITY - 1) {
        assert_ne!(t, F::ONE);
        t.square();
    }

    for _ in size.trailing_zeros()..(F::TWO_ADICITY as u32) {
        omega.square();
        if size != 1 {
            assert_ne!(omega, F::ONE);
        }
    }

    assert_eq!(omega.pow(size as u32), F::ONE);

    omega
}

pub fn materialize_powers_parallel<F: Field, A: GoodAllocator>(
    first_element: F,
    step: F,
    size: usize,
    worker: &Worker,
) -> Vec<F, A> {
    if size == 0 {
        return Vec::new_in(A::default());
    }
    assert!(
        size.is_power_of_two(),
        "due to requirement on size and alignment we only allow powers of two sizes, but got {}",
        size
    );
    let mut storage = Vec::with_capacity_in(size, A::default());
    worker.scope(size, |scope, geometry| {
        for (chunk_idx, chunk) in storage.spare_capacity_mut()[..size]
            .chunks_for_geometry_mut(geometry)
            .enumerate()
        {
            scope.spawn(move |_| {
                let mut current = step.pow(geometry.get_chunk_start_pos(chunk_idx) as u32);
                current.mul_assign(&first_element);
                for el in chunk.iter_mut() {
                    el.write(current);
                    current.mul_assign(&step);
                }
            });
        }
    });

    unsafe { storage.set_len(size) }

    storage
}

pub fn materialize_powers_parallel_starting_with_one<F: Field, A: GoodAllocator>(
    base: F,
    size: usize,
    worker: &Worker,
) -> Vec<F, A> {
    if size == 0 {
        return Vec::new_in(A::default());
    }
    assert!(
        size.is_power_of_two(),
        "due to requirement on size and alignment we only allow powers of two sizes, but got {}",
        size
    );
    let mut storage = Vec::with_capacity_in(size, A::default());
    worker.scope(size, |scope, geometry| {
        for (chunk_idx, chunk) in storage.spare_capacity_mut()[..size]
            .chunks_for_geometry_mut(geometry)
            .enumerate()
        {
            scope.spawn(move |_| {
                let mut current = base.pow(geometry.get_chunk_start_pos(chunk_idx) as u32);
                for el in chunk.iter_mut() {
                    el.write(current);
                    current.mul_assign(&base);
                }
            });
        }
    });

    unsafe { storage.set_len(size) }

    storage
}

pub fn batch_inverse_inplace<F: Field>(input: &mut [F], tmp_buffer: &mut [F]) {
    if input.is_empty() {
        return;
    }

    // we do Montgomery batch inversion trick, and reuse a buffer
    tmp_buffer[0] = F::ONE;
    let mut accumulator = input[0];
    for (el, out) in input.iter().zip(tmp_buffer.iter_mut()).skip(1) {
        *out = accumulator;
        accumulator.mul_assign(el);
    }

    // for a set of a, b, c, d we have
    // - input = [1, a, ab, abc],
    // - accumulator = abcd
    let mut grand_inverse = accumulator
        .inverse()
        .expect("batch inverse must be called on sets without zeroes");

    // grand_inverse = a^-1 b^-1 c^-1 d^-1
    for (tmp, original) in tmp_buffer.iter().rev().zip(input.iter_mut().rev()) {
        let mut tmp = *tmp; // abc
        tmp.mul_assign(&grand_inverse); // d^-1
        grand_inverse.mul_assign(original); // e.g. it's now a^-1 b^-1 c^-1

        *original = tmp;
    }
}

pub fn batch_inverse_with_buffer<F: Field>(input: &mut [F], tmp_buffer: &mut Vec<F>) {
    assert!(tmp_buffer.is_empty());
    if input.is_empty() {
        return;
    }

    // we do Montgomery batch inversion trick, and reuse a buffer
    tmp_buffer.push(F::ONE);
    let mut accumulator = input[0];
    for el in input[1..].iter() {
        tmp_buffer.push(accumulator);
        accumulator.mul_assign(el);
    }

    debug_assert_eq!(tmp_buffer.len(), input.len());

    // for a set of a, b, c, d we have
    // - input = [1, a, ab, abc],
    // - accumulator = abcd
    let mut grand_inverse = accumulator
        .inverse()
        .expect("batch inverse must be called on sets without zeroes");

    // grand_inverse = a^-1 b^-1 c^-1 d^-1
    for (tmp, original) in tmp_buffer.iter().rev().zip(input.iter_mut().rev()) {
        let mut tmp = *tmp; // abc
        tmp.mul_assign(&grand_inverse); // d^-1
        grand_inverse.mul_assign(original); // e.g. it's now a^-1 b^-1 c^-1

        *original = tmp;
    }

    tmp_buffer.clear();
}

pub fn batch_inverse_for_several_slices_inplace<F: Field>(
    mut input_slices: Vec<&mut [F]>,
    tmp_buffer: &mut [F],
) {
    assert_eq!(
        input_slices.iter().map(|slice| slice.len()).sum::<usize>(),
        tmp_buffer.len()
    );

    // we do Montgomery batch inversion trick, and reuse a buffer
    tmp_buffer[0] = F::ONE;
    let mut accumulator = input_slices[0][0];
    for (el, out) in (input_slices.iter().flat_map(|slice| slice.iter()))
        .zip(tmp_buffer.iter_mut())
        .skip(1)
    {
        *out = accumulator;
        accumulator.mul_assign(el);
    }

    // for a set of a, b, c, d we have
    // - input = [1, a, ab, abc],
    // - accumulator = abcd
    let mut grand_inverse = accumulator
        .inverse()
        .expect("batch inverse must be called on sets without zeroes");

    // grand_inverse = a^-1 b^-1 c^-1 d^-1
    for (tmp, original) in tmp_buffer.iter().rev().zip(
        input_slices
            .iter_mut()
            .rev()
            .flat_map(|slice| slice.iter_mut().rev()),
    ) {
        let mut tmp = *tmp; // abc
        tmp.mul_assign(&grand_inverse); // d^-1
        grand_inverse.mul_assign(original); // e.g. it's now a^-1 b^-1 c^-1

        *original = tmp;
    }
}

pub fn batch_inverse_inplace_parallel<F: Field>(
    input: &mut [F],
    tmp_buf: &mut [F],
    worker: &Worker,
) {
    worker.scope(input.len(), |scope, geometry| {
        for (dst_chunk, tmp_chunk) in input
            .chunks_for_geometry_mut(geometry)
            .zip(tmp_buf.chunks_for_geometry_mut(geometry))
        {
            scope.spawn(move |_| {
                batch_inverse_inplace(dst_chunk, tmp_chunk);
            });
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
    use rand::{rngs::ThreadRng, RngCore};
    use worker::Worker;

    type F = BabyBearField;
    type E = BabyBearExt4;

    fn random_in_ext(rng: &mut ThreadRng) -> E
    where
        [(); <E as FieldExtension<F>>::DEGREE]: Sized,
    {
        let coefs = [(); <E as FieldExtension<F>>::DEGREE]
            .map(|_| F::from_u32_with_reduction(rng.next_u32()));
        <E as FieldExtension<F>>::from_coeffs(coefs)
    }

    fn run_test(size: usize, initial: F, step: F) {
        let mut rng = rand::rng();
        let input: Vec<E> = (0..size).map(|_| random_in_ext(&mut rng)).collect();

        let worker = Worker::new_with_num_threads(4);

        let mut serial = input.clone();
        distribute_powers_serial(&mut serial, initial, step);

        let mut parallel = input.clone();
        distribute_powers_parallel(&mut parallel, initial, step, &worker);

        assert_eq!(serial, parallel, "mismatch for size={size}");
    }

    #[test]
    fn test_distribute_powers() {
        let step = F::from_nonreduced_u32(13);
        run_test(2048, F::ONE, step);

        let step = F::from_nonreduced_u32(7);
        let initial = F::from_nonreduced_u32(3);
        run_test(16, initial, step);
        run_test(256, initial, step);
        run_test(1023, initial, step);

        let step = F::from_nonreduced_u32(7);
        let initial = F::from_nonreduced_u32(3);
        run_test(1024, initial, step);
        run_test(4096, initial, step);
        run_test(1 << 16, initial, step);
    }
}

// RoundFunction knows nothing about rate and capacity, it only operates on the state as a wholw
pub trait AlgebraicRoundFunction<F: PrimeField, const STATE_WIDTH: usize>:
    Clone + Send + Sync
{
    fn round_function(&self, state: &mut [F; STATE_WIDTH]);
    fn initial_state(&self) -> [F; STATE_WIDTH];
    fn specialize_for_depth(&self, depth: u32, state: &mut [F; STATE_WIDTH]);
}
