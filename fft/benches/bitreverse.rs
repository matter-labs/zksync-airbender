use criterion::*;

use field::Mersenne31Field;
use field::PrimeField;

use fft::bitreverse_enumeration_inplace;
use fft::parallel_bitreverse_enumeration_inplace;

use worker::Worker;

fn get_random_slice(len: usize) -> Vec<Mersenne31Field> {
    use rand::Rng;
    let mut rng = rand::rng();

    (0..len)
        .map(|_| Mersenne31Field::from_u64(rng.random_range(0..(1 << 31) - 1)).unwrap())
        .collect()
}

fn bitreverse(crit: &mut Criterion) {
    let mut data = get_random_slice(1 << 20);
    let worker_2 = Worker::new_with_num_threads(2);
    let worker_4 = Worker::new_with_num_threads(4);

    crit.bench_function("Bitreverse", |b| {
        b.iter(|| bitreverse_enumeration_inplace(&mut data));
    });

    crit.bench_function("Parallel bitreverse 2 threads", |b| {
        b.iter(|| parallel_bitreverse_enumeration_inplace(&mut data, &worker_2));
    });

    crit.bench_function("Parallel bitreverse 4 threads", |b| {
        b.iter(|| parallel_bitreverse_enumeration_inplace(&mut data, &worker_4));
    });
}

criterion_group!(benches, bitreverse,);
criterion_main!(benches);
