#[cfg(target_arch = "aarch64")]
use blake2s_u32::vectorized_impls::arm_neon;
use blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS;
use criterion::*;

fn naive(crit: &mut Criterion) {
    let data = vec![u32::MAX; 1 << 20];
    let mut hasher = blake2s_u32::Blake2sState::new();

    crit.bench_function("Naive impl reduced rounds", |b| {
        b.iter(|| {
            hasher.reset();
            for chunk in data.as_chunks::<BLAKE2S_BLOCK_SIZE_U32_WORDS>().0 {
                hasher.absorb::<true>(&chunk);
            }
        });
    });

    crit.bench_function("Naive impl full rounds", |b| {
        b.iter(|| {
            hasher.reset();
            for chunk in data.as_chunks::<BLAKE2S_BLOCK_SIZE_U32_WORDS>().0 {
                hasher.absorb::<false>(&chunk);
            }
        });
    });
}

#[cfg(target_arch = "aarch64")]
fn neon(crit: &mut Criterion) {
    let data = vec![u32::MAX; 1 << 20];
    let mut hasher = arm_neon::Blake2sState::new();

    crit.bench_function("Neon impl reduced rounds", |b| {
        b.iter(|| {
            hasher.reset();
            for chunk in data.as_chunks::<BLAKE2S_BLOCK_SIZE_U32_WORDS>().0 {
                hasher.absorb::<true>(&chunk);
            }
        });
    });

    crit.bench_function("Neon impl full rounds", |b| {
        b.iter(|| {
            hasher.reset();
            for chunk in data.as_chunks::<BLAKE2S_BLOCK_SIZE_U32_WORDS>().0 {
                hasher.absorb::<false>(&chunk);
            }
        });
    });
}

#[cfg(target_arch = "aarch64")]
criterion_group!(benches, naive, neon,);
#[cfg(not(target_arch = "aarch64"))]
criterion_group!(benches, naive,);

criterion_main!(benches);
