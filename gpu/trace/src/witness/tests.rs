use era_cudart::memory::memory_copy_async;
use era_cudart::slice::DeviceSlice;
use field::Proth120;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_structures::DeviceMatrixMut;
use gpu_core::primitives::field::BF;
use gpu_core::primitives::static_host::alloc_static_pinned_box_from_slice;
use gpu_prover_context::{ProverContext, ProverContextConfig};
use std::mem::size_of;

fn runtime_context() -> ProverContext {
    ProverContext::new(&ProverContextConfig {
        allocator_block_log_size: 20,
        device_allocation_blocks_count: Some(64),
        host_allocator_block_log_size: 13,
        host_allocator_blocks_count: 64,
        ..Default::default()
    })
    .unwrap()
}

fn upload_slice<T: Copy>(values: &[T], context: &ProverContext) -> DeviceAllocation<T> {
    let mut device = context
        .alloc(values.len(), AllocationPlacement::BestFit)
        .unwrap();
    if !values.is_empty() {
        let pinned = alloc_static_pinned_box_from_slice(values).unwrap();
        memory_copy_async(&mut device, pinned.as_ref(), context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
    }
    device
}

fn read_slice<T: Copy + Default>(device: &DeviceSlice<T>, context: &ProverContext) -> Vec<T> {
    assert!(
        size_of::<T>() * device.len() <= 64 << 20,
        "Proth120 runtime bounded host copy"
    );
    let mut result = vec![T::default(); device.len()];
    if !result.is_empty() {
        memory_copy_async(result.as_mut_slice(), device, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
    }
    result
}

fn random_word(state: &mut u64) -> u32 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    (*state >> 16) as u32
}

pub(crate) trait MultiplicityField:
    Copy + Default + Send + Sync + std::fmt::Debug + PartialEq + 'static
{
    fn count(value: u32) -> Self;
    fn generate(
        mapping: &mut DeviceMatrixMut<'_, u32>,
        counts: &mut DeviceMatrixMut<'_, Self>,
        active: usize,
        context: &ProverContext,
    );
}

#[test]
#[cfg(not(no_cuda))]
fn multiplicity_contract() {
    // BabyBear keeps its counter shards in the output for (512, 1, 64) and in a transient buffer
    // for the other two cases, one with a two-column output; Proth120 runs the same cases.
    for (rows, columns, active) in [(512, 1, 64), (64, 2, 96), (2048, 1, 257)] {
        assert_multiplicity_contract::<BF>(rows, columns, active);
        assert_multiplicity_contract::<Proth120>(rows, columns, active);
    }
}

#[cfg(not(no_cuda))]
fn assert_multiplicity_contract<F: MultiplicityField>(rows: usize, columns: usize, active: usize) {
    let context = runtime_context();
    let mut state = 0x1205_0006_0002u64;
    let random: Vec<_> = (0..3 * rows)
        .map(|i| {
            if i.is_multiple_of(7) {
                u32::MAX
            } else {
                random_word(&mut state) % active as u32
            }
        })
        .collect();
    let mut boundaries = vec![u32::MAX; 3 * rows];
    for i in [
        0,
        31,
        32,
        63,
        64,
        127,
        128,
        rows - 1,
        rows,
        2 * rows - 1,
        2 * rows,
        3 * rows - 1,
    ] {
        boundaries[i] = (active - 1) as u32;
    }
    for (name, values) in [
        ("random holes", random),
        ("all equal", vec![7; 3 * rows]),
        ("shard boundaries", boundaries),
        ("empty", Vec::new()),
    ] {
        let mut mapping = upload_slice(&values, &context);
        let mut counts = upload_slice(&vec![F::count(17); rows * columns], &context);
        F::generate(
            &mut DeviceMatrixMut::new(&mut mapping, rows),
            &mut DeviceMatrixMut::new(&mut counts, rows),
            active,
            &context,
        );
        context.get_exec_stream().synchronize().unwrap();
        let mut histogram = vec![0u32; rows * columns];
        for &index in &values {
            if index != u32::MAX {
                histogram[index as usize] += 1;
            }
        }
        assert_eq!(
            read_slice(&counts, &context),
            histogram.into_iter().map(F::count).collect::<Vec<_>>(),
            "{} multiplicities {name}",
            std::any::type_name::<F>()
        );
        assert_eq!(
            read_slice(&mapping, &context),
            values
                .into_iter()
                .map(|index| if index == u32::MAX { 0 } else { index })
                .collect::<Vec<_>>(),
            "{} normalized holes {name}",
            std::any::type_name::<F>()
        );
    }
}
