// Microbenchmark: unreduced accumulation vs Montgomery-per-iteration.
//
// Two loop shapes, each over N random inputs:
//   Base scalar:  acc += a_i * b_i  (both base field)
//   Base × Ext4:  acc += a_i * c_i  (a base, c Ext4)
//

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use field::baby_bear::unreduced::{BabyBearExt4RawProductSum, BabyBearRawProductSum};
use field::field::{Field, FieldExtension};
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

fn random_base(rng: &mut impl Rng) -> BabyBearField {
    BabyBearField::new(rng.random_range(0..BabyBearField::ORDER))
}

fn random_ext4(rng: &mut impl Rng) -> BabyBearExt4 {
    <BabyBearExt4 as FieldExtension<BabyBearField>>::from_coeffs([
        random_base(rng),
        random_base(rng),
        random_base(rng),
        random_base(rng),
    ])
}

fn bench_base_dot_product(c: &mut Criterion) {
    let mut group = c.benchmark_group("base_dot_product");
    for &log_n in &[10usize, 16, 20] {
        let n = 1usize << log_n;
        let mut r = SmallRng::seed_from_u64(0xC0FFEE_u64 ^ (log_n as u64));
        let pairs: Vec<(BabyBearField, BabyBearField)> = (0..n)
            .map(|_| (random_base(&mut r), random_base(&mut r)))
            .collect();

        group.bench_with_input(
            BenchmarkId::new("baseline_mul_mod", log_n),
            &pairs,
            |b, pairs| {
                b.iter(|| {
                    let mut acc = BabyBearField::ZERO;
                    for (a, b) in pairs {
                        let mut t = *a;
                        t.mul_assign(b);
                        acc.add_assign(&t);
                    }
                    black_box(acc)
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("unreduced_raw_product_sum", log_n),
            &pairs,
            |b, pairs| {
                b.iter(|| {
                    let mut acc = BabyBearRawProductSum::ZERO;
                    for (a, b) in pairs {
                        acc.add_assign_product(*a, *b);
                    }
                    black_box(acc.finalize())
                })
            },
        );
    }
    group.finish();
}

fn bench_base_times_ext4(c: &mut Criterion) {
    let mut group = c.benchmark_group("base_times_ext4");
    for &log_n in &[10usize, 16, 20] {
        let n = 1usize << log_n;
        let mut r = SmallRng::seed_from_u64(0xC0FFEE_u64 ^ (log_n as u64));
        let terms: Vec<(BabyBearField, BabyBearExt4)> = (0..n)
            .map(|_| (random_base(&mut r), random_ext4(&mut r)))
            .collect();

        group.bench_with_input(
            BenchmarkId::new("baseline_mul_by_base", log_n),
            &terms,
            |b, terms| {
                b.iter(|| {
                    let mut acc = BabyBearExt4::ZERO;
                    for (a, c) in terms {
                        let mut t = *c;
                        t.mul_assign_by_base(a);
                        acc.add_assign(&t);
                    }
                    black_box(acc)
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("unreduced_ext4_raw_product_sum", log_n),
            &terms,
            |b, terms| {
                b.iter(|| {
                    let mut acc = BabyBearExt4RawProductSum::ZERO;
                    for (a, c) in terms {
                        acc.add_assign_base_times_ext(*a, *c);
                    }
                    black_box(acc.finalize())
                })
            },
        );
    }
    group.finish();
}

criterion_group!(benches, bench_base_dot_product, bench_base_times_ext4);
criterion_main!(benches);
