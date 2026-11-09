mod bank;
mod continuation;
mod dr;
mod layered;
mod r0;

use field::{Field, PrimeField};
use gpu_core::primitives::field::PR;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use super::{make_context, read_back, upload};
use crate::proth120::backward::abi::pr_sum32_probe;

fn random_canonical(rng: &mut StdRng) -> PR {
    loop {
        let raw = rng.random::<u128>() >> 5;
        if raw < PR::CHARACTERISTICS_U128 {
            return PR::from_raw_u128(raw);
        }
    }
}

#[test]
#[cfg(not(no_cuda))]
fn pr_sum32_bounds() {
    let context = make_context();
    let mut rng = StdRng::seed_from_u64(0x5132);
    let minus_one = PR::MINUS_ONE;
    let mut segments: Vec<Vec<PR>> = Vec::new();
    for length in [0usize, 1, 31, 32, 33, 64, 100] {
        segments.push(vec![minus_one; length]);
        segments.push(
            (0..length)
                .map(|index| {
                    let value = random_canonical(&mut rng);
                    if index.is_multiple_of(2) {
                        value
                    } else {
                        *value.clone().negate()
                    }
                })
                .collect(),
        );
        segments.push((0..length).map(|_| random_canonical(&mut rng)).collect());
    }
    let mut values = Vec::new();
    let mut offsets = vec![0u32];
    for segment in &segments {
        values.extend_from_slice(segment);
        offsets.push(values.len() as u32);
    }
    let d_values = upload(&values, &context);
    let d_offsets = upload(&offsets, &context);
    let mut d_sums = upload(&vec![PR::ZERO; segments.len()], &context);
    pr_sum32_probe(
        &d_values,
        &d_offsets,
        &mut d_sums,
        context.get_exec_stream(),
    )
    .unwrap();
    let sums = read_back(&d_sums, PR::ZERO, &context);
    for (index, (segment, actual)) in segments.iter().zip(&sums).enumerate() {
        let expected = segment
            .iter()
            .fold(PR::ZERO, |sum, value| *sum.clone().add_assign(value));
        assert!(
            actual.0 < PR::CHARACTERISTICS_U128,
            "segment {index} is not canonical"
        );
        assert_eq!(
            *actual,
            expected,
            "segment {index} of length {}",
            segment.len()
        );
    }
}
