use super::*;
use crate::upstream::Field;
use era_cudart::memory::memory_copy_async;
use field::FieldExtension;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::BF;
use prover::gkr::prover::merge_claims;

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
fn packed_merge_extension_tail_canary_and_pack_refusal() {
    let context = crate::test_utils::make_test_context(256, 16);
    let values: Vec<_> = (0..5)
        .map(|i| {
            E4::from_array_of_base(std::array::from_fn(|j| {
                BF::new(13 + i * 17 + j as u32 * 19)
            }))
        })
        .collect();
    let coordinates = [values[2], values[3]];
    let expected = merge_claims(&values, &coordinates);
    let input = upload(&values, &context);
    let point = upload(&coordinates, &context);
    let canary = values[4];
    let mut output = upload(&vec![canary; expected.len() + 2], &context);
    launch_merge_claims_e4(
        &input,
        &point,
        2,
        &mut output[1..1 + expected.len()],
        &context,
    )
    .unwrap();
    let mut actual = vec![E4::ZERO; expected.len() + 2];
    memory_copy_async(&mut actual, &output, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    assert_eq!(actual[0], canary);
    assert_eq!(actual[actual.len() - 1], canary);
    assert_eq!(&actual[1..1 + expected.len()], expected);
    let refusal_point = upload(&[coordinates[0]; 6], &context);
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        launch_merge_claims_e4(&input, &refusal_point, 6, &mut output[1..2], &context)
    }))
    .expect_err("pack_log2 = 6 must be refused");
    let message = panic
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| panic.downcast_ref::<&str>().copied())
        .unwrap();
    assert!(
        message.contains("E4 claim merging requires pack_log2 in 1..=5"),
        "{message}"
    );
}
