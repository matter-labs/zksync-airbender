use field::{PrimeField, Proth120};
use gpu_core::primitives::field::BF;

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
    let circuit = serde_json::from_slice(include_bytes!(
        "../../../../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json"
    ))
    .unwrap();
    let _relations = super::LookupRelationsPr::new(&circuit);
    assert_eq!((size_of::<Address>(), align_of::<Address>()), (12, 4));
    assert_eq!(
        (
            size_of::<crate::witness::LinearTerm>(),
            align_of::<crate::witness::LinearTerm>()
        ),
        (16, 4)
    );
    assert_eq!(
        (
            size_of::<crate::witness::LinearRelation>(),
            align_of::<crate::witness::LinearRelation>()
        ),
        (72, 4)
    );
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
            size_of::<Proth120LookupExpressions<15>>(),
            align_of::<Proth120LookupExpressions<15>>()
        ),
        (2400, 16)
    );
    assert_eq!(size_of::<Proth120LookupExpressions<8>>(), 1280);
    assert_eq!(size_of::<super::LookupRelationsPr>(), 3680);
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

trait MultiplicityField: Copy + Default + Send + Sync + std::fmt::Debug + PartialEq + 'static {
    fn count(value: u32) -> Self;
    fn generate(
        mapping: &mut DeviceMatrixMut<'_, u32>,
        counts: &mut DeviceMatrixMut<'_, Self>,
        active: usize,
        context: &ProverContext,
    );
}
impl MultiplicityField for Proth120 {
    fn count(value: u32) -> Self {
        Proth120::new(value as u128)
    }
    fn generate(
        mapping: &mut DeviceMatrixMut<'_, u32>,
        counts: &mut DeviceMatrixMut<'_, Self>,
        active: usize,
        context: &ProverContext,
    ) {
        super::generate_lookup_multiplicities(mapping, counts, active, context).unwrap();
    }
}
impl MultiplicityField for BF {
    fn count(value: u32) -> Self {
        BF::from_u32_unchecked(value)
    }
    fn generate(
        mapping: &mut DeviceMatrixMut<'_, u32>,
        counts: &mut DeviceMatrixMut<'_, Self>,
        active: usize,
        context: &ProverContext,
    ) {
        crate::witness::multiplicities::generate_lookup_multiplicities(
            mapping, counts, active, context,
        )
        .unwrap();
    }
}
#[test]
#[cfg(not(no_cuda))]
fn multiplicity_contract() {
    // Preserve the BF alias/transient fixtures, including a multi-column output.
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
