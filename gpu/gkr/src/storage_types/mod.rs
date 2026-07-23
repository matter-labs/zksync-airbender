mod ffi_descriptors;
mod views;

pub(crate) use ffi_descriptors::*;
pub(crate) use views::*;

// `#[doc(hidden)] pub` re-exports: apex e2e tests + proof orchestration name
// these across the crate boundary (rows 37/38/39 + cluster C).
#[doc(hidden)]
pub use ffi_descriptors::{
    GpuBaseFieldPolySource, GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor,
    GpuExtensionFieldPolyContinuingLaunchDescriptor, GpuExtensionFieldPolyInitialSource,
    GpuSumcheckRound0LaunchDescriptors,
};
#[doc(hidden)]
pub use views::{
    GpuBaseFieldPoly, GpuExtensionFieldPoly, GpuGKRStorage,
    GpuSumcheckRound1DeviceLaunchDescriptors, GpuSumcheckRound1ScheduledLaunchDescriptors,
};
