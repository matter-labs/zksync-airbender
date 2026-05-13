use era_cudart::result::CudaResult;
use field::Field;

use super::{
    alloc_device_and_schedule_upload, alloc_host_and_schedule_copy,
    GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor,
    GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor,
    GpuExtensionFieldPolyContinuingLaunchDescriptor, GpuSumcheckRound1DeviceLaunchDescriptors,
    GpuSumcheckRound1HostLaunchDescriptors, GpuSumcheckRound1PreparedStorage,
    GpuSumcheckRound1ScheduledLaunchDescriptors, GpuSumcheckRound2DeviceLaunchDescriptors,
    GpuSumcheckRound2HostLaunchDescriptors, GpuSumcheckRound2PreparedStorage,
    GpuSumcheckRound2ScheduledLaunchDescriptors, GpuSumcheckRound3AndBeyondDeviceLaunchDescriptors,
    GpuSumcheckRound3AndBeyondHostLaunchDescriptors, GpuSumcheckRound3AndBeyondPreparedStorage,
    GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors,
};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::ProverContext;

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
