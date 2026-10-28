use super::*;
use crate::upstream::Field;
use era_cudart::memory::memory_copy_async;
use field::FieldExtension;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::BF;
use prover::gkr::prover::merge_claims;

pub(crate) fn numeric_values() -> Vec<u32> {
    (0..67).map(|i| 11 + 7 * i + i * i).collect()
}

pub(crate) const NUMERIC_COORDINATES: [u32; 4] = [3, 5, 7, 11];

fn upload<T: Copy>(data: &[T], context: &ProverContext) -> DeviceAllocation<T> {
    let mut out = context
        .alloc(data.len(), AllocationPlacement::BestFit)
        .unwrap();
    if !data.is_empty() {
        memory_copy_async(&mut out, data, context.get_exec_stream()).unwrap();
    }
    out
}

#[test]
fn packed_handoff_cpu_parity_e4_merge_golden_vectors() {
    let context = crate::test_utils::make_test_context(256, 16);
    let scalar_values: Vec<_> = numeric_values()
        .into_iter()
        .map(|v| E4::from_base(BF::new(v)))
        .collect();
    let scalar_coordinates = NUMERIC_COORDINATES.map(|v| E4::from_base(BF::new(v)));
    let extension_values: Vec<_> = (0..67)
        .map(|i| {
            E4::from_array_of_base(std::array::from_fn(|j| {
                BF::new(13 + i * 17 + j as u32 * 19)
            }))
        })
        .collect();
    let extension_coordinates = std::array::from_fn::<_, 4, _>(|i| extension_values[60 + i]);
    for (values, coordinates) in [
        (&scalar_values, scalar_coordinates),
        (&extension_values, extension_coordinates),
    ] {
        for k in 1..=4 {
            let pack = 1usize << k;
            let d_coordinates = upload(&coordinates[..k as usize], &context);
            for count in [0, 1, pack - 1, pack, pack + 1, 2 * pack + 1] {
                let input = &values[..count];
                let expected = merge_claims(input, &coordinates[..k as usize]);
                let d_input = upload(input, &context);
                let canary = E4::from_base(BF::new(1234567));
                let mut output = upload(&vec![canary; expected.len() + 2], &context);
                launch_merge_claims_e4(
                    &d_input,
                    &d_coordinates,
                    k,
                    &mut output[1..1 + expected.len()],
                    &context,
                )
                .unwrap();
                let mut actual = vec![E4::ZERO; expected.len() + 2];
                memory_copy_async(&mut actual, &output, context.get_exec_stream()).unwrap();
                context.get_exec_stream().synchronize().unwrap();
                assert_eq!(actual[0], canary);
                assert_eq!(actual[actual.len() - 1], canary);
                assert_eq!(
                    &actual[1..1 + expected.len()],
                    &expected,
                    "k={k}, count={count}"
                );
            }
        }
    }
}
