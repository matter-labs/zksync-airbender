use super::launch_bench_fwd_interp_smoke;

use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::field::BF;
use crate::prover::test_utils::make_test_context;

use era_cudart::memory::memory_copy_async;
use field::Field;
use serial_test::serial;

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn bench_stub_kernel_roundtrip() {
    let context = make_test_context(256, 32);
    let count = 256usize;
    let values = (0..count as u32).map(BF::new).collect::<Vec<_>>();

    let mut src_dev = context.alloc(count, AllocationPlacement::Top).unwrap();
    memory_copy_async(&mut src_dev, &values, context.get_exec_stream()).unwrap();
    let mut dst_dev = context.alloc(count, AllocationPlacement::Top).unwrap();

    launch_bench_fwd_interp_smoke(src_dev.as_ptr(), dst_dev.as_mut_ptr(), count, &context).unwrap();

    let mut host = vec![BF::ZERO; count];
    memory_copy_async(&mut host, &dst_dev, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();

    assert_eq!(host, values);
}
