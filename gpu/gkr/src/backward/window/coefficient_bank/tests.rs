use super::*;
use era_cudart::memory::{memory_copy_async, DeviceAllocation};

fn sample(seed: u32) -> E4 {
    E4::from_array_of_base(std::array::from_fn(|i| {
        BF::from_u32_with_reduction(seed.wrapping_mul(0x9e3779b1).wrapping_add(i as u32))
    }))
}

fn bank(counts: &[usize]) -> CoefficientBankBlob {
    let mut bank = CoefficientBankBlob::new(counts.len()).unwrap();
    for (slot, &count) in counts.iter().enumerate() {
        let monomials: Vec<_> = (0..count)
            .map(|i| BankMonomial {
                coeff: BF::from_u32_with_reduction((slot * 31 + i + 1) as u32),
                batch_power: [0, u16::MAX, 1, 31, 255][i % 5],
                challenge_idx_0: if i % 3 == 0 {
                    BWD_COEFF_CHALLENGE_ABSENT
                } else {
                    (i % BWD_COEFF_CHALLENGE_SLOTS) as u8
                },
                challenge_idx_1: if i % 4 == 0 {
                    BWD_COEFF_CHALLENGE_ABSENT
                } else {
                    ((i * 7 + 3) % BWD_COEFF_CHALLENGE_SLOTS) as u8
                },
                power_0: [0, 1, 31, u8::MAX][i % 4],
                power_1: [1, 0, 2, u8::MAX][i % 4],
                _pad: [0; 2],
            })
            .collect();
        let (kind, limb) = match slot % 6 {
            0 => (BWD_COEFF_PLAN_DIRECT, 0),
            1 => (BWD_COEFF_PLAN_SCALED, 0),
            n => (BWD_COEFF_PLAN_LINEAR_BASIS, (n - 2) as u8),
        };
        bank.push(
            slot,
            &monomials,
            kind,
            BF::from_u32_with_reduction(slot as u32 + 2),
            limb,
        )
        .unwrap();
    }
    bank
}

// Serial host field arithmetic is independent of the native Montgomery
// implementation and of the warp's lane assignment and reduction tree.
fn evaluate(bank: &CoefficientBankBlob, challenges: &[E4]) -> Vec<E4> {
    bank.recipes
        .iter()
        .map(|recipe| {
            let mut sum = E4::ZERO;
            let start = usize::from(recipe.monomial_offset);
            let end = start + usize::from(recipe.monomial_count);
            for monomial in &bank.monomials[start..end] {
                let mut term = E4::from_base(monomial.coeff);
                term.mul_assign(
                    &challenges[BWD_COEFF_CHALLENGE_CLAIM_BATCHING as usize]
                        .pow(u32::from(monomial.batch_power)),
                );
                for (index, power) in [
                    (monomial.challenge_idx_0, monomial.power_0),
                    (monomial.challenge_idx_1, monomial.power_1),
                ] {
                    if index != BWD_COEFF_CHALLENGE_ABSENT {
                        term.mul_assign(&challenges[index as usize].pow(u32::from(power)));
                    }
                }
                sum.add_assign(&term);
            }
            match recipe.kind {
                BWD_COEFF_PLAN_DIRECT => {}
                BWD_COEFF_PLAN_SCALED => {
                    sum.mul_assign_by_base(&recipe.scalar);
                }
                BWD_COEFF_PLAN_LINEAR_BASIS => {
                    let mut limbs = [BF::ZERO; 4];
                    limbs[recipe.limb as usize] = BF::ONE;
                    sum.mul_assign(&E4::from_array_of_base(limbs));
                }
                _ => unreachable!(),
            }
            sum
        })
        .collect()
}

#[test]
fn coefficient_bank_parallel_reduction_and_chunk_boundaries() {
    let stream = CudaStream::default();
    let mut cases: Vec<Vec<usize>> = [1, 3, 4, 5, 127, 128, 129, 1023, 1024, 1025, 1792]
        .into_iter()
        .map(|recipes| (0..recipes).map(|i| usize::from(i % 3 != 0)).collect())
        .collect();
    // Includes zero work in a live warp, multiple warp iterations, a full
    // monomial chunk, and a following chunk with a nonzero bank offset.
    cases.push(vec![
        0, 1, 2, 3, 4, 5, 7, 8, 31, 32, 33, 63, 64, 65, 297, 1536, 1,
    ]);
    for counts in cases {
        let bank = bank(&counts);
        let chunks = CoefficientBankChunks::build(&bank);
        let mut device_challenges =
            DeviceAllocation::<E4>::alloc(BWD_COEFF_CHALLENGE_SLOTS).unwrap();
        let mut device_bank = DeviceAllocation::<E4>::alloc(counts.len() + 2).unwrap();
        for kind in 0..3 {
            let challenges: Vec<_> = (0..BWD_COEFF_CHALLENGE_SLOTS)
                .map(|i| match kind {
                    0 => E4::ZERO,
                    1 => E4::ONE,
                    _ => sample(i as u32 + 1),
                })
                .collect();
            let expected = evaluate(&bank, &challenges);
            memory_copy_async(&mut device_challenges, &challenges[..], &stream).unwrap();
            for poison in [sample(991), sample(997)] {
                let initial = vec![poison; counts.len() + 2];
                memory_copy_async(&mut device_bank, &initial[..], &stream).unwrap();
                // SAFETY: the allocation has a canary on either side of the
                // bank prefix, and both allocations live through synchronization.
                let output = unsafe { device_bank.as_mut_ptr().add(1) };
                schedule_bwd_coeff_bank_fill(&chunks, device_challenges.as_ptr(), output, &stream)
                    .unwrap();
                let mut actual = vec![E4::ZERO; counts.len() + 2];
                let mut unchanged = vec![E4::ZERO; BWD_COEFF_CHALLENGE_SLOTS];
                memory_copy_async(&mut actual[..], &device_bank, &stream).unwrap();
                memory_copy_async(&mut unchanged[..], &device_challenges, &stream).unwrap();
                stream.synchronize().unwrap();
                assert_eq!(actual[0], poison);
                assert_eq!(actual[counts.len() + 1], poison);
                assert_eq!(&actual[1..counts.len() + 1], expected.as_slice());
                assert_eq!(unchanged, challenges);
            }
        }
    }
}
