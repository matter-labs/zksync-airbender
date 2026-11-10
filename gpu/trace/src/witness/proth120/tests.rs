use field::Proth120;

use super::relations::{Proth120LinearRelation, Proth120LinearTerm, Proth120LookupExpressions};
use crate::witness::Address;
use era_cudart::memory::memory_copy_async;
use era_cudart::slice::DeviceSlice;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_structures::DeviceMatrixMut;
use gpu_core::primitives::static_host::alloc_static_pinned_box_from_slice;
use gpu_prover_context::{ProverContext, ProverContextConfig};
use std::mem::{align_of, size_of};

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

#[test]
fn cpu_relations_abi_pins() {
    assert_eq!((size_of::<Address>(), align_of::<Address>()), (12, 4));
    assert_eq!(
        (
            size_of::<Proth120LinearTerm>(),
            align_of::<Proth120LinearTerm>()
        ),
        (32, 16)
    );
    assert_eq!(
        (
            size_of::<Proth120LinearRelation>(),
            align_of::<Proth120LinearRelation>()
        ),
        (160, 16)
    );
    assert_eq!(
        (
            size_of::<Proth120LookupExpressions>(),
            align_of::<Proth120LookupExpressions>()
        ),
        (16, 8)
    );
    let address = Address::InnerLayer {
        offset: 0x12345678,
        layer: 0x87654321,
    };
    let words =
        unsafe { std::slice::from_raw_parts((&address as *const Address).cast::<u32>(), 3) };
    assert_eq!(
        words,
        &[2, 0x12345678, 0x87654321],
        "Proth120 Address tag/offset/layer at 0/4/8"
    );
    for (address, tag) in [
        (Address::BaseLayerWitness(0), 0),
        (Address::BaseLayerMemory(0), 1),
        (
            Address::InnerLayer {
                offset: 0,
                layer: 0,
            },
            2,
        ),
        (Address::Setup(0), 3),
        (Address::ScratchSpace(0), 4),
        (
            Address::Cached {
                offset: 0,
                layer: 0,
            },
            5,
        ),
    ] {
        assert_eq!(
            unsafe { *(&address as *const Address).cast::<u32>() },
            tag,
            "Proth120 Address discriminant"
        );
    }
}

#[test]
#[cfg(not(no_cuda))]
fn multiplicity_contract() {
    let context = runtime_context();
    let rows = 2048usize;
    let active = 257;
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
        let mut counts = upload_slice(&vec![Proth120::new(17); rows], &context);
        super::generate_lookup_multiplicities(
            &mut DeviceMatrixMut::new(&mut mapping, rows),
            &mut DeviceMatrixMut::new(&mut counts, rows),
            active,
            &context,
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let mut histogram = vec![0u32; rows];
        for &index in &values {
            if index != u32::MAX {
                histogram[index as usize] += 1;
            }
        }
        assert_eq!(
            read_slice(&counts, &context),
            histogram
                .into_iter()
                .map(|count| Proth120::new(count as u128))
                .collect::<Vec<_>>(),
            "Proth120 multiplicities {name}"
        );
        assert_eq!(
            read_slice(&mapping, &context),
            values
                .into_iter()
                .map(|index| if index == u32::MAX { 0 } else { index })
                .collect::<Vec<_>>(),
            "Proth120 normalized holes {name}"
        );
    }
}
