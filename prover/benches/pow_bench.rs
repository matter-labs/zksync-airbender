use criterion::{criterion_group, criterion_main, Criterion};

use prover::prover_stages::Transcript;
use transcript::Seed;
use worker::Worker;

fn get_random_seed() -> Seed {
    use rand::Rng;
    let mut rng = rand::rng();

    let inner = [0; 8].map(|_| rng.random());

    Seed(inner)
}

fn pow_benchmark(c: &mut Criterion) {
    let seed = get_random_seed();
    let worker = Worker::new_with_num_threads(1);

    for pow_bits in [1, 4, 7, 17, 28].iter() {
        c.bench_function(&format!("PoW for {} bits", pow_bits), |b| {
            b.iter(|| Transcript::search_pow(&seed, *pow_bits, &worker))
        });
    }
}

criterion_group!(benches, pow_benchmark);
criterion_main!(benches);
