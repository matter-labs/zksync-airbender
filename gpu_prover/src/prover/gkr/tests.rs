use super::*;
use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::HostAllocation;
use crate::primitives::field::{BF, E4};
use crate::prover::test_utils::make_test_context;

use crate::upstream::{Field, VirtualSetupPoly};
use era_cudart::memory::memory_copy_async;
use serial_test::serial;

impl<B> GpuBaseFieldPoly<B> {
    pub(crate) fn new(backing: DeviceAllocation<B>) -> Self {
        let len = backing.len();
        Self::from_arc(Arc::new(backing), 0, len)
    }

    pub(crate) fn offset(&self) -> usize {
        self.offset
    }

    pub(crate) fn shares_backing_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.backing, &other.backing)
    }
}

impl<E> GpuExtensionFieldPoly<E> {
    pub(crate) fn new(backing: DeviceAllocation<E>) -> Self {
        let len = backing.len();
        Self::from_arc(Arc::new(backing), 0, len)
    }

    pub(crate) fn offset(&self) -> usize {
        self.offset
    }

    pub(crate) fn shares_backing_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.backing, &other.backing)
    }

    pub(crate) fn as_device_chunk(&self) -> DeviceVectorChunk<'_, E> {
        DeviceVectorChunk::new(self.backing.as_ref(), self.offset, self.len)
    }
}

pub(crate) struct GpuSumcheckRound0HostLaunchDescriptors<B, E> {
    pub(crate) base_field_inputs: HostAllocation<[GpuBaseFieldPolySource<B>]>,
    pub(crate) extension_field_inputs: HostAllocation<[GpuExtensionFieldPolyInitialSource<E>]>,
    pub(crate) base_field_outputs: HostAllocation<[GpuBaseFieldPolySource<B>]>,
    pub(crate) extension_field_outputs: HostAllocation<[GpuExtensionFieldPolyInitialSource<E>]>,
}

pub(crate) struct GpuSumcheckRound0DeviceLaunchDescriptors<B, E> {
    pub(crate) base_field_inputs: DeviceAllocation<GpuBaseFieldPolySource<B>>,
    pub(crate) extension_field_inputs: DeviceAllocation<GpuExtensionFieldPolyInitialSource<E>>,
    pub(crate) base_field_outputs: DeviceAllocation<GpuBaseFieldPolySource<B>>,
    pub(crate) extension_field_outputs: DeviceAllocation<GpuExtensionFieldPolyInitialSource<E>>,
}

pub(crate) struct GpuSumcheckRound0ScheduledLaunchDescriptors<B, E> {
    #[allow(dead_code)]
    pub(crate) callbacks: Callbacks<'static>,
    pub(crate) host: GpuSumcheckRound0HostLaunchDescriptors<B, E>,
    pub(crate) device: GpuSumcheckRound0DeviceLaunchDescriptors<B, E>,
}

pub(crate) struct GpuSumcheckRound1DeviceLaunchDescriptors<B, E> {
    pub(crate) base_field_inputs:
        DeviceAllocation<GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E>>,
    pub(crate) extension_field_inputs:
        DeviceAllocation<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
}

pub(crate) struct GpuSumcheckRound1ScheduledLaunchDescriptors<B, E> {
    pub(crate) device: GpuSumcheckRound1DeviceLaunchDescriptors<B, E>,
}

#[derive(Clone, Debug)]
pub(crate) struct GpuSumcheckRound1HostLaunchDescriptors<B, E: Copy> {
    pub(crate) base_field_inputs: Vec<GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<B, E>>,
    pub(crate) extension_field_inputs: Vec<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
}

pub(crate) struct GpuSumcheckRound2DeviceLaunchDescriptors<B, E> {
    pub(crate) base_field_inputs:
        DeviceAllocation<GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E>>,
    pub(crate) extension_field_inputs:
        DeviceAllocation<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
}

pub(crate) struct GpuSumcheckRound2ScheduledLaunchDescriptors<B, E> {
    pub(crate) device: GpuSumcheckRound2DeviceLaunchDescriptors<B, E>,
}

#[derive(Clone, Debug)]
pub(crate) struct GpuSumcheckRound2HostLaunchDescriptors<B, E: Copy> {
    pub(crate) base_field_inputs: Vec<GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor<B, E>>,
    pub(crate) extension_field_inputs: Vec<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
}

pub(crate) struct GpuSumcheckRound3AndBeyondDeviceLaunchDescriptors<E> {
    pub(crate) base_field_inputs:
        DeviceAllocation<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
    pub(crate) extension_field_inputs:
        DeviceAllocation<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
}

pub(crate) struct GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E> {
    pub(crate) device: GpuSumcheckRound3AndBeyondDeviceLaunchDescriptors<E>,
}

#[derive(Clone, Debug)]
pub(crate) struct GpuSumcheckRound3AndBeyondHostLaunchDescriptors<E: Copy> {
    pub(crate) base_field_inputs: Vec<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
    pub(crate) extension_field_inputs: Vec<GpuExtensionFieldPolyContinuingLaunchDescriptor<E>>,
}

pub(crate) fn alloc_host_and_schedule_copy<T: Copy + Send + Sync + 'static>(
    context: &ProverContext,
    callbacks: &mut Callbacks<'static>,
    values: Vec<T>,
) -> HostAllocation<[T]> {
    let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
    let host_accessor = host.get_mut_accessor();
    callbacks
        .schedule(
            move || unsafe {
                host_accessor.get_mut().copy_from_slice(&values);
            },
            context.get_exec_stream(),
        )
        .expect("failed to schedule host copy callback");
    host
}

pub(crate) fn alloc_device_and_schedule_upload<T: Copy>(
    context: &ProverContext,
    host: &HostAllocation<[T]>,
) -> CudaResult<DeviceAllocation<T>> {
    let mut device = context.alloc(host.len(), AllocationPlacement::Top)?;
    memory_copy_async(&mut device, host, context.get_exec_stream())?;
    Ok(device)
}

fn alloc_and_copy<T: Copy>(context: &ProverContext, values: &[T]) -> DeviceAllocation<T> {
    let mut allocation = context
        .alloc(values.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut allocation, values, context.get_exec_stream()).unwrap();
    allocation
}

fn copy_device_values<T: Copy>(context: &ProverContext, values: &DeviceAllocation<T>) -> Vec<T> {
    let mut allocation = unsafe { context.alloc_host_uninit_slice(values.len()) };
    memory_copy_async(&mut allocation, values, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    unsafe { allocation.get_accessor().get().to_vec() }
}

fn sample_ext(seed: u32) -> E4 {
    E4::from_array_of_base([
        BF::new(seed),
        BF::new(seed + 1),
        BF::new(seed + 2),
        BF::new(seed + 3),
    ])
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn insert_get_try_get_and_purge_match_cpu_semantics() {
    let context = make_test_context(64, 8);
    let mut storage = GpuGKRStorage::<BF, E4>::default();

    let base_memory = GpuBaseFieldPoly::new(alloc_and_copy(
        &context,
        &(0..8).map(|i| BF::new(i as u32 + 1)).collect::<Vec<_>>(),
    ));
    let base_setup = GpuBaseFieldPoly::new(alloc_and_copy(
        &context,
        &(10..18).map(|i| BF::new(i as u32)).collect::<Vec<_>>(),
    ));
    let ext_inner = GpuExtensionFieldPoly::new(alloc_and_copy(
        &context,
        &(0..8)
            .map(|i| sample_ext(i as u32 + 20))
            .collect::<Vec<_>>(),
    ));

    let base_memory_ptr = base_memory.as_ptr();
    let base_setup_ptr = base_setup.as_ptr();
    let ext_inner_ptr = ext_inner.as_ptr();

    storage.insert_base_field_at_layer(0, GKRAddress::BaseLayerMemory(0), base_memory);
    storage.insert_base_field_at_layer(0, GKRAddress::Setup(0), base_setup);
    storage.insert_extension_at_layer(
        1,
        GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        },
        ext_inner,
    );

    assert_eq!(storage.get_base_layer_mem(0).as_ptr(), base_memory_ptr);
    assert_eq!(
        storage.get_base_layer(GKRAddress::Setup(0)).as_ptr(),
        base_setup_ptr
    );
    assert_eq!(
        storage
            .try_get_base_poly(GKRAddress::BaseLayerMemory(0))
            .unwrap()
            .as_ptr(),
        base_memory_ptr
    );
    assert_eq!(
        storage
            .try_get_ext_poly(GKRAddress::InnerLayer {
                layer: 1,
                offset: 0
            })
            .unwrap()
            .as_ptr(),
        ext_inner_ptr
    );
    assert_eq!(
        storage
            .get_ext_poly(GKRAddress::InnerLayer {
                layer: 1,
                offset: 0
            })
            .as_ptr(),
        ext_inner_ptr
    );

    storage.purge_up_to_layer(0);
    assert_eq!(storage.layers.len(), 1);
    assert!(storage
        .try_get_ext_poly(GKRAddress::InnerLayer {
            layer: 1,
            offset: 0
        })
        .is_none());
    assert_eq!(storage.get_base_layer_mem(0).as_ptr(), base_memory_ptr);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn shared_views_support_subviews_and_drop_on_last_reference() {
    let context = make_test_context(64, 8);
    let baseline = context.get_used_mem_current();

    let backing = Arc::new(alloc_and_copy(
        &context,
        &(0..16).map(|i| BF::new(i as u32 + 1)).collect::<Vec<_>>(),
    ));

    let col0 = GpuBaseFieldPoly::from_arc(Arc::clone(&backing), 0, 8);
    let col1 = GpuBaseFieldPoly::from_arc(Arc::clone(&backing), 8, 8);
    let col0_copy = col0.clone_shared();

    assert!(col0.shares_backing_with(&col1));
    assert!(col0.shares_backing_with(&col0_copy));
    assert_eq!(col0.offset(), 0);
    assert_eq!(col1.offset(), 8);
    assert_eq!(unsafe { col1.as_ptr().offset_from(col0.as_ptr()) }, 8);

    let mut storage = GpuGKRStorage::<BF, E4>::default();
    storage.insert_base_field_at_layer(0, GKRAddress::BaseLayerMemory(0), col0);
    storage.insert_base_field_at_layer(0, GKRAddress::BaseLayerMemory(1), col1);

    assert!(context.get_used_mem_current() > baseline);

    drop(storage);
    assert!(context.get_used_mem_current() > baseline);

    drop(col0_copy);
    drop(backing);
    assert_eq!(context.get_used_mem_current(), baseline);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn round_builders_allocate_and_reuse_scratch() {
    let context = make_test_context(64, 8);
    let baseline = context.get_used_mem_current();

    let mut storage = GpuGKRStorage::<BF, E4>::default();
    let base_backing = Arc::new(alloc_and_copy(
        &context,
        &(0..16).map(|i| BF::new(i as u32 + 1)).collect::<Vec<_>>(),
    ));
    let ext_values = (0..8)
        .map(|i| sample_ext(i as u32 + 40))
        .collect::<Vec<_>>();
    let ext_poly = GpuExtensionFieldPoly::new(alloc_and_copy(&context, &ext_values));
    let base_input = GpuBaseFieldPoly::from_arc(base_backing, 0, 8);
    let base_output = GpuBaseFieldPoly::new(alloc_and_copy(
        &context,
        &(100..108).map(|i| BF::new(i as u32)).collect::<Vec<_>>(),
    ));
    let ext_output = GpuExtensionFieldPoly::new(alloc_and_copy(
        &context,
        &(0..8)
            .map(|i| sample_ext(i as u32 + 60))
            .collect::<Vec<_>>(),
    ));

    let base_input_ptr = base_input.as_ptr();
    let base_output_ptr = base_output.as_ptr();
    let ext_input_ptr = ext_poly.as_ptr();
    let ext_output_ptr = ext_output.as_ptr();

    storage.insert_base_field_at_layer(0, GKRAddress::BaseLayerMemory(0), base_input);
    storage.insert_base_field_at_layer(
        1,
        GKRAddress::InnerLayer {
            layer: 1,
            offset: 1,
        },
        base_output,
    );
    storage.insert_extension_at_layer(
        1,
        GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        },
        ext_poly,
    );
    storage.insert_extension_at_layer(
        1,
        GKRAddress::InnerLayer {
            layer: 1,
            offset: 2,
        },
        ext_output,
    );

    let inputs = GKRInputs {
        inputs_in_base: vec![GKRAddress::BaseLayerMemory(0), GKRAddress::placeholder()],
        inputs_in_extension: vec![
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 0,
            },
            GKRAddress::placeholder(),
        ],
        outputs_in_base: vec![
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 1,
            },
            GKRAddress::placeholder(),
        ],
        outputs_in_extension: vec![
            GKRAddress::InnerLayer {
                layer: 1,
                offset: 2,
            },
            GKRAddress::placeholder(),
        ],
    };

    {
        let round0 = storage
            .schedule_upload_for_sumcheck_round_0(&inputs, &context)
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let round0_base_inputs = copy_device_values(&context, &round0.device.base_field_inputs);
        let round0_base_outputs = copy_device_values(&context, &round0.device.base_field_outputs);
        let round0_ext_inputs = copy_device_values(&context, &round0.device.extension_field_inputs);
        let round0_ext_outputs =
            copy_device_values(&context, &round0.device.extension_field_outputs);
        assert_eq!(round0_base_inputs[0].start, base_input_ptr);
        assert_eq!(round0_base_outputs[0].start, base_output_ptr);
        assert_eq!(round0_ext_inputs[0].start, ext_input_ptr);
        assert_eq!(round0_ext_outputs[0].start, ext_output_ptr);
        assert!(round0_base_inputs[1].start.is_null());
        assert!(round0_ext_inputs[1].start.is_null());
    }

    let _r1 = sample_ext(100);
    {
        let mut callbacks = Callbacks::new();
        let round1 = storage
            .prepare_for_sumcheck_round_1(&inputs, 0, &context)
            .unwrap()
            .schedule_upload_launch_descriptors(&context, &mut callbacks)
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let round1_base_inputs_device =
            copy_device_values(&context, &round1.device.base_field_inputs);
        let round1_ext_inputs_device =
            copy_device_values(&context, &round1.device.extension_field_inputs);
        assert_eq!(
            round1_base_inputs_device[0].base_input_start,
            base_input_ptr
        );
        assert!(round1_base_inputs_device[1].base_input_start.is_null());
        assert_eq!(
            round1_ext_inputs_device[0].previous_layer_start,
            ext_input_ptr
        );
        assert!(round1_ext_inputs_device[0].first_access);
        assert!(round1_ext_inputs_device[1].previous_layer_start.is_null());
    }
    let used_after_round1 = context.get_used_mem_current();
    assert!(used_after_round1 > baseline);

    let _r2 = sample_ext(200);
    let (base_round2_cache_ptr, ext_round2_cache_ptr) = {
        let mut callbacks = Callbacks::new();
        let round2_first = storage
            .prepare_for_sumcheck_round_2(&inputs, 0, &context)
            .unwrap()
            .schedule_upload_launch_descriptors(&context, &mut callbacks)
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let round2_first_base_inputs_device =
            copy_device_values(&context, &round2_first.device.base_field_inputs);
        let round2_first_ext_inputs_device =
            copy_device_values(&context, &round2_first.device.extension_field_inputs);
        assert!(round2_first_base_inputs_device[0].first_access);
        assert!(round2_first_ext_inputs_device[0].first_access);
        (
            round2_first_base_inputs_device[0].this_layer_cache_start,
            round2_first_ext_inputs_device[0].this_layer_start,
        )
    };

    {
        let mut callbacks = Callbacks::new();
        let round2_second = storage
            .prepare_for_sumcheck_round_2(&inputs, 0, &context)
            .unwrap()
            .schedule_upload_launch_descriptors(&context, &mut callbacks)
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let round2_second_base_inputs_device =
            copy_device_values(&context, &round2_second.device.base_field_inputs);
        let round2_second_ext_inputs_device =
            copy_device_values(&context, &round2_second.device.extension_field_inputs);
        assert!(!round2_second_base_inputs_device[0].first_access);
        assert!(!round2_second_ext_inputs_device[0].first_access);
        assert_eq!(
            round2_second_base_inputs_device[0].this_layer_cache_start,
            base_round2_cache_ptr
        );
        assert_eq!(
            round2_second_ext_inputs_device[0].this_layer_start,
            ext_round2_cache_ptr
        );
    }

    let _r3 = sample_ext(300);
    let (round3_base_cache_ptr, round3_ext_cache_ptr) = {
        let mut callbacks = Callbacks::new();
        let round3_first = storage
            .prepare_for_sumcheck_round_3_and_beyond(&inputs, 0, 3, &context)
            .unwrap()
            .schedule_upload_launch_descriptors(&context, &mut callbacks)
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let round3_first_base_inputs_device =
            copy_device_values(&context, &round3_first.device.base_field_inputs);
        let round3_first_ext_inputs_device =
            copy_device_values(&context, &round3_first.device.extension_field_inputs);
        assert!(round3_first_base_inputs_device[0].first_access);
        assert!(round3_first_ext_inputs_device[0].first_access);
        assert_eq!(
            unsafe {
                round3_first_base_inputs_device[0]
                    .this_layer_start
                    .offset_from(round3_first_base_inputs_device[0].previous_layer_start)
            },
            2
        );
        assert_eq!(
            unsafe {
                round3_first_ext_inputs_device[0]
                    .this_layer_start
                    .offset_from(round3_first_ext_inputs_device[0].previous_layer_start)
            },
            1
        );
        assert_eq!(round3_first_base_inputs_device[0].this_layer_size, 1);
        assert_eq!(round3_first_ext_inputs_device[0].this_layer_size, 1);
        (
            round3_first_base_inputs_device[0].this_layer_start,
            round3_first_ext_inputs_device[0].this_layer_start,
        )
    };

    {
        let mut callbacks = Callbacks::new();
        let round3_second = storage
            .prepare_for_sumcheck_round_3_and_beyond(&inputs, 0, 3, &context)
            .unwrap()
            .schedule_upload_launch_descriptors(&context, &mut callbacks)
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let round3_second_base_inputs_device =
            copy_device_values(&context, &round3_second.device.base_field_inputs);
        let round3_second_ext_inputs_device =
            copy_device_values(&context, &round3_second.device.extension_field_inputs);
        assert!(!round3_second_base_inputs_device[0].first_access);
        assert!(!round3_second_ext_inputs_device[0].first_access);
        assert_eq!(
            round3_second_base_inputs_device[0].this_layer_start,
            round3_base_cache_ptr
        );
        assert_eq!(
            round3_second_ext_inputs_device[0].this_layer_start,
            round3_ext_cache_ptr
        );
    }

    {
        let mut callbacks = Callbacks::new();
        let round2_reuse_after_round3 = storage
            .prepare_for_sumcheck_round_2(&inputs, 0, &context)
            .unwrap()
            .schedule_upload_launch_descriptors(&context, &mut callbacks)
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let round2_reuse_base_inputs_device = copy_device_values(
            &context,
            &round2_reuse_after_round3.device.base_field_inputs,
        );
        let round2_reuse_ext_inputs_device = copy_device_values(
            &context,
            &round2_reuse_after_round3.device.extension_field_inputs,
        );
        assert!(!round2_reuse_base_inputs_device[0].first_access);
        assert!(!round2_reuse_ext_inputs_device[0].first_access);
        assert_eq!(
            round2_reuse_base_inputs_device[0].this_layer_cache_start,
            base_round2_cache_ptr
        );
        assert_eq!(
            round2_reuse_ext_inputs_device[0].this_layer_start,
            ext_round2_cache_ptr
        );
    }

    drop(storage);
    assert_eq!(context.get_used_mem_current(), baseline);
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn virtual_setup_sources_lower_to_synthetic_descriptors() {
    let context = make_test_context(64, 8);
    let mut storage = GpuGKRStorage::<BF, E4>::default();
    let base_values = (0..8)
        .map(|idx| BF::new(idx as u32 + 1))
        .collect::<Vec<_>>();
    storage.insert_base_field_at_layer(
        0,
        GKRAddress::BaseLayerMemory(0),
        GpuBaseFieldPoly::new(alloc_and_copy(&context, &base_values)),
    );

    let inputs = GKRInputs {
        inputs_in_base: vec![
            GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits),
            GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
        ],
        inputs_in_extension: Vec::new(),
        outputs_in_base: Vec::new(),
        outputs_in_extension: Vec::new(),
    };

    let round0 = storage.get_for_sumcheck_round_0(&inputs);
    assert!(round0.base_field_inputs[0].start.is_null());
    assert_eq!(round0.base_field_inputs[0].next_layer_size, 4);
    assert_eq!(
        round0.base_field_inputs[0].source_kind,
        GpuBaseFieldSourceKind::VirtualRangeCheck16Bits
    );
    assert!(round0.base_field_inputs[1].start.is_null());
    assert_eq!(round0.base_field_inputs[1].next_layer_size, 4);
    assert_eq!(
        round0.base_field_inputs[1].source_kind,
        GpuBaseFieldSourceKind::VirtualInitsAndTeardownsHigh
    );

    let round1 = storage
        .prepare_for_sumcheck_round_1(&inputs, 0, &context)
        .unwrap();
    assert!(round1.base_field_inputs[0].base_input_start.is_null());
    assert_eq!(round1.base_field_inputs[0].base_layer_half_size, 4);
    assert_eq!(round1.base_field_inputs[0].next_layer_size, 2);
    assert_eq!(
        round1.base_field_inputs[0].source_kind,
        GpuBaseFieldSourceKind::VirtualRangeCheck16Bits
    );
    assert!(round1.base_field_inputs[1].base_input_start.is_null());
    assert_eq!(
        round1.base_field_inputs[1].source_kind,
        GpuBaseFieldSourceKind::VirtualInitsAndTeardownsHigh
    );

    let round2_first = storage
        .prepare_for_sumcheck_round_2(&inputs, 0, &context)
        .unwrap();
    assert!(round2_first.base_field_inputs[0].base_input_start.is_null());
    assert_eq!(round2_first.base_field_inputs[0].base_layer_half_size, 4);
    assert_eq!(round2_first.base_field_inputs[0].base_quarter_size, 2);
    assert_eq!(round2_first.base_field_inputs[0].next_layer_size, 1);
    assert!(round2_first.base_field_inputs[0].first_access);
    assert_eq!(
        round2_first.base_field_inputs[0].source_kind,
        GpuBaseFieldSourceKind::VirtualRangeCheck16Bits
    );
    assert!(round2_first.base_field_inputs[1].base_input_start.is_null());
    assert!(round2_first.base_field_inputs[1].first_access);
    assert_eq!(
        round2_first.base_field_inputs[1].source_kind,
        GpuBaseFieldSourceKind::VirtualInitsAndTeardownsHigh
    );

    let round2_second = storage
        .prepare_for_sumcheck_round_2(&inputs, 0, &context)
        .unwrap();
    assert!(!round2_second.base_field_inputs[0].first_access);
    assert!(!round2_second.base_field_inputs[1].first_access);
    assert_eq!(
        round2_second.base_field_inputs[0].source_kind,
        GpuBaseFieldSourceKind::VirtualRangeCheck16Bits
    );
    assert_eq!(
        round2_second.base_field_inputs[1].source_kind,
        GpuBaseFieldSourceKind::VirtualInitsAndTeardownsHigh
    );
}

impl<B: 'static, E: Field + 'static> GpuSumcheckRound1PreparedStorage<B, E> {
    pub(crate) fn build_launch_descriptors(&self) -> GpuSumcheckRound1HostLaunchDescriptors<B, E> {
        let base_field_inputs = self
            .base_field_inputs
            .iter()
            .map(
                |plan| GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                    base_layer_half_size: plan.base_layer_half_size,
                    next_layer_size: plan.next_layer_size,
                    base_input_start: plan.base_input_start,
                    this_layer_cache_start: plan.this_layer_cache_start,
                    first_access: plan.first_access,
                    source_kind: plan.source_kind,
                    _marker: core::marker::PhantomData,
                },
            )
            .collect();
        let extension_field_inputs = self
            .extension_field_inputs
            .iter()
            .map(|plan| GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: plan.previous_layer_start,
                this_layer_start: plan.this_layer_start,
                this_layer_size: plan.this_layer_size,
                next_layer_size: plan.next_layer_size,
                first_access: plan.first_access,
            })
            .collect();
        GpuSumcheckRound1HostLaunchDescriptors {
            base_field_inputs,
            extension_field_inputs,
        }
    }

    pub(crate) fn schedule_upload_launch_descriptors(
        &self,
        context: &ProverContext,
        callbacks: &mut Callbacks<'static>,
    ) -> CudaResult<GpuSumcheckRound1ScheduledLaunchDescriptors<B, E>> {
        let descriptors = self.build_launch_descriptors();
        let host_base =
            alloc_host_and_schedule_copy(context, callbacks, descriptors.base_field_inputs);
        let base_field_inputs_device = alloc_device_and_schedule_upload(context, &host_base)?;
        drop(host_base);
        let host_ext =
            alloc_host_and_schedule_copy(context, callbacks, descriptors.extension_field_inputs);
        let extension_field_inputs_device = alloc_device_and_schedule_upload(context, &host_ext)?;
        drop(host_ext);
        let device = GpuSumcheckRound1DeviceLaunchDescriptors {
            base_field_inputs: base_field_inputs_device,
            extension_field_inputs: extension_field_inputs_device,
        };
        Ok(GpuSumcheckRound1ScheduledLaunchDescriptors { device })
    }
}

impl<B: 'static, E: Field + 'static> GpuSumcheckRound2PreparedStorage<B, E> {
    pub(crate) fn build_launch_descriptors(&self) -> GpuSumcheckRound2HostLaunchDescriptors<B, E> {
        let base_field_inputs = self
            .base_field_inputs
            .iter()
            .map(
                |plan| GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor {
                    base_input_start: plan.base_input_start,
                    this_layer_cache_start: plan.this_layer_cache_start,
                    base_layer_half_size: plan.base_layer_half_size,
                    base_quarter_size: plan.base_quarter_size,
                    next_layer_size: plan.next_layer_size,
                    first_access: plan.first_access,
                    source_kind: plan.source_kind,
                },
            )
            .collect();
        let extension_field_inputs = self
            .extension_field_inputs
            .iter()
            .map(|plan| GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: plan.previous_layer_start,
                this_layer_start: plan.this_layer_start,
                this_layer_size: plan.this_layer_size,
                next_layer_size: plan.next_layer_size,
                first_access: plan.first_access,
            })
            .collect();
        GpuSumcheckRound2HostLaunchDescriptors {
            base_field_inputs,
            extension_field_inputs,
        }
    }

    pub(crate) fn schedule_upload_launch_descriptors(
        &self,
        context: &ProverContext,
        callbacks: &mut Callbacks<'static>,
    ) -> CudaResult<GpuSumcheckRound2ScheduledLaunchDescriptors<B, E>> {
        let descriptors = self.build_launch_descriptors();
        let host_base =
            alloc_host_and_schedule_copy(context, callbacks, descriptors.base_field_inputs);
        let base_field_inputs_device = alloc_device_and_schedule_upload(context, &host_base)?;
        drop(host_base);
        let host_ext =
            alloc_host_and_schedule_copy(context, callbacks, descriptors.extension_field_inputs);
        let extension_field_inputs_device = alloc_device_and_schedule_upload(context, &host_ext)?;
        drop(host_ext);
        let device = GpuSumcheckRound2DeviceLaunchDescriptors {
            base_field_inputs: base_field_inputs_device,
            extension_field_inputs: extension_field_inputs_device,
        };
        Ok(GpuSumcheckRound2ScheduledLaunchDescriptors { device })
    }
}

impl<E: Field + 'static> GpuSumcheckRound3AndBeyondPreparedStorage<E> {
    pub(crate) fn build_launch_descriptors(
        &self,
    ) -> GpuSumcheckRound3AndBeyondHostLaunchDescriptors<E> {
        let base_field_inputs = self
            .base_field_inputs
            .iter()
            .map(|plan| GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: plan.previous_layer_start,
                this_layer_start: plan.this_layer_start,
                this_layer_size: plan.this_layer_size,
                next_layer_size: plan.next_layer_size,
                first_access: plan.first_access,
            })
            .collect();
        let extension_field_inputs = self
            .extension_field_inputs
            .iter()
            .map(|plan| GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: plan.previous_layer_start,
                this_layer_start: plan.this_layer_start,
                this_layer_size: plan.this_layer_size,
                next_layer_size: plan.next_layer_size,
                first_access: plan.first_access,
            })
            .collect();
        GpuSumcheckRound3AndBeyondHostLaunchDescriptors {
            base_field_inputs,
            extension_field_inputs,
        }
    }

    pub(crate) fn schedule_upload_launch_descriptors(
        &self,
        context: &ProverContext,
        callbacks: &mut Callbacks<'static>,
    ) -> CudaResult<GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E>> {
        let descriptors = self.build_launch_descriptors();
        let host_base =
            alloc_host_and_schedule_copy(context, callbacks, descriptors.base_field_inputs);
        let base_field_inputs_device = alloc_device_and_schedule_upload(context, &host_base)?;
        drop(host_base);
        let host_ext =
            alloc_host_and_schedule_copy(context, callbacks, descriptors.extension_field_inputs);
        let extension_field_inputs_device = alloc_device_and_schedule_upload(context, &host_ext)?;
        drop(host_ext);
        let device = GpuSumcheckRound3AndBeyondDeviceLaunchDescriptors {
            base_field_inputs: base_field_inputs_device,
            extension_field_inputs: extension_field_inputs_device,
        };
        Ok(GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors { device })
    }
}
