use core::mem::size_of;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::OnceLock;

use era_cudart::error::get_last_error;
use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::memory::{memory_copy_async, memory_get_info, memory_set_async, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaError;
use field::{Field, PrimeField};
use gkr_eval_ir::FieldKind;
use gpu_gkr_compiler::backward::LeanSourceBinding;
use serde::{Deserialize, Serialize};

use crate::abi::{BF, E4};
use crate::geometry::{build_lean_allocation_plan, LeanAllocationPlan};
use crate::kernels::launch_finalize;
use crate::r0_abi::{
    classify_r0_coefficient, R0CoefficientRef, R0VmDesc, R0WindowAddr, R0_COEFFICIENT_CAPACITY,
    R0_EQ_HIGH_ELEMENTS,
};
use crate::r0_artifact::{
    decode_r0_bundle, validate_r0_coordinate, FrozenR0Coordinate, R0_CORPUS_BYTES,
};
use crate::r0_geometry::{R0Geometry, R0LaunchMetadata, R0MemoryPreflight};
use crate::r0_input::{
    build_r0_input, validate_r0_input, validate_r0_production_input, FrozenE4, FrozenField,
    PreparedR0ProductionInput, R0HostBacking, ResolvedR0Input,
};
use crate::r0_kernels::{
    launch_r0_geometry, r0_coefficient_bank_device_ptr, r0_eq_high_device_ptr,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0Observed {
    pub cells: [FrozenE4; 27],
    pub checksum: String,
    pub launch: R0LaunchMetadata,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct R0TimingConfig {
    warmups: u32,
    samples: u32,
}

impl R0TimingConfig {
    pub const fn production_traversal() -> Self {
        Self {
            warmups: 5,
            samples: 50,
        }
    }

    pub const fn screen(warmups: u32, samples: u32) -> Result<Self, &'static str> {
        if samples == 0 || warmups > 50 || samples > 50 {
            return Err("prototype timing requires <=50 warmups and 1..=50 samples");
        }
        Ok(Self { warmups, samples })
    }

    pub const fn warmups(self) -> u32 {
        self.warmups
    }

    pub const fn samples(self) -> u32 {
        self.samples
    }

    pub fn sample_kinds(self) -> impl Iterator<Item = bool> {
        (0..self.warmups + self.samples).map(move |index| index < self.warmups)
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct R0TimedSample {
    pub warmup: bool,
    pub milliseconds: f64,
}

#[derive(Clone, Debug, PartialEq)]
pub struct R0TimedSession {
    pub launch: R0LaunchMetadata,
    pub correctness_checksum: String,
    pub post_session_checksum: String,
    pub samples: Vec<R0TimedSample>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0HarnessHashes {
    pub bundle_sha256: String,
    pub coordinate_sha256: String,
    pub input_sha256: String,
    pub source_data_sha256: String,
    pub independent_source_sha256: String,
    pub derived_source_sha256: Option<String>,
    pub coefficient_sha256: String,
    pub direct_eq_sha256: String,
    pub factored_eq_sha256: String,
    pub executable_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R0ProductionError {
    Arithmetic(String),
    CudaMemoryInfo(String),
    InsufficientDeviceMemory {
        requested_bytes: u64,
        free_bytes: u64,
        preflight: Box<R0MemoryPreflight>,
    },
}

impl core::fmt::Display for R0ProductionError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Arithmetic(error) => write!(formatter, "preflight-arithmetic: {error}"),
            Self::CudaMemoryInfo(error) => write!(formatter, "preflight-cuda-memory-info: {error}"),
            Self::InsufficientDeviceMemory {
                requested_bytes,
                free_bytes,
                ..
            } => write!(
                formatter,
                "preflight-capacity: requested={requested_bytes} free={free_bytes}"
            ),
        }
    }
}

impl std::error::Error for R0ProductionError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R0ProductionSetupError {
    Prelaunch(String),
    Cuda {
        stage: &'static str,
        error: String,
        oom: bool,
        preflight: R0MemoryPreflight,
    },
}

impl R0ProductionSetupError {
    pub fn is_oom(&self) -> bool {
        matches!(self, Self::Cuda { oom: true, .. })
    }

    pub fn preflight(&self) -> Option<&R0MemoryPreflight> {
        match self {
            Self::Prelaunch(_) => None,
            Self::Cuda { preflight, .. } => Some(preflight),
        }
    }

    pub fn failure_code(&self) -> &'static str {
        match self {
            Self::Prelaunch(_) => "production-prelaunch-failure",
            Self::Cuda { oom: true, .. } => "production-incomplete-oom",
            Self::Cuda { .. } => "production-setup-cuda-failure",
        }
    }
}

impl core::fmt::Display for R0ProductionSetupError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Prelaunch(error) => write!(formatter, "production-prelaunch-failure: {error}"),
            Self::Cuda {
                stage, error, oom, ..
            } => write!(
                formatter,
                "{}: stage={stage} cuda={error}",
                if *oom {
                    "production-incomplete-oom"
                } else {
                    "production-setup-cuda-failure"
                }
            ),
        }
    }
}

impl std::error::Error for R0ProductionSetupError {}

pub fn production_memory_preflight(
    coordinate: &FrozenR0Coordinate,
    runtime_bytes: u64,
) -> Result<R0MemoryPreflight, R0ProductionError> {
    // Complete all checked host arithmetic before the first CUDA interaction.
    R0MemoryPreflight::for_coordinate(
        coordinate,
        coordinate.trace_len.ilog2(),
        runtime_bytes,
        None,
    )
    .map_err(|error| R0ProductionError::Arithmetic(error.to_string()))?;
    let (free, total) = memory_get_info()
        .map_err(|error| R0ProductionError::CudaMemoryInfo(format!("{error:?}")))?;
    let free = u64::try_from(free)
        .map_err(|_| R0ProductionError::Arithmetic("device free bytes exceed u64".to_owned()))?;
    let total = u64::try_from(total)
        .map_err(|_| R0ProductionError::Arithmetic("device total bytes exceed u64".to_owned()))?;
    let preflight = R0MemoryPreflight::for_coordinate(
        coordinate,
        coordinate.trace_len.ilog2(),
        runtime_bytes,
        Some((free, total)),
    )
    .map_err(|error| R0ProductionError::Arithmetic(error.to_string()))?;
    ensure_preflight_capacity(preflight)
}

pub fn production_memory_preflight_for_binding(
    binding: &LeanSourceBinding,
    log_trace: u32,
    coefficient_elements: usize,
    runtime_bytes: u64,
    device_memory: Option<(u64, u64)>,
) -> Result<R0MemoryPreflight, R0ProductionError> {
    let source_plan = build_lean_allocation_plan(binding, log_trace)
        .map_err(|error| R0ProductionError::Arithmetic(error.to_string()))?;
    let source_backing_bytes = source_plan
        .backings
        .iter()
        .map(|backing| {
            u64::try_from(backing.bytes).map_err(|_| {
                R0ProductionError::Arithmetic("source backing bytes exceed u64".to_owned())
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let eq_low_bytes = checked_e4_bytes(
        u64::try_from(source_plan.eq_low_elements).map_err(|_| {
            R0ProductionError::Arithmetic("low equality elements exceed u64".to_owned())
        })?,
        "low equality bytes",
    )?;
    let eq_high_elements = source_plan
        .eq_sizes
        .high
        .into_iter()
        .try_fold(0u64, |sum, bits| {
            let elements = if bits == 0 {
                0
            } else {
                1u64.checked_shl(bits).ok_or_else(|| {
                    R0ProductionError::Arithmetic("high equality elements overflow".to_owned())
                })?
            };
            sum.checked_add(elements).ok_or_else(|| {
                R0ProductionError::Arithmetic("high equality elements overflow".to_owned())
            })
        })?;
    let eq_high_bytes = checked_e4_bytes(eq_high_elements, "high equality bytes")?;
    let partial_elements = u64::try_from(source_plan.partial_elements)
        .map_err(|_| R0ProductionError::Arithmetic("partial elements exceed u64".to_owned()))?;
    let partial_bytes = checked_e4_bytes(partial_elements, "partial bytes")?;
    let final_bytes = checked_e4_bytes(
        u64::try_from(source_plan.final_elements)
            .map_err(|_| R0ProductionError::Arithmetic("final elements exceed u64".to_owned()))?,
        "final bytes",
    )?;
    let coefficient_bytes = checked_e4_bytes(
        u64::try_from(coefficient_elements).map_err(|_| {
            R0ProductionError::Arithmetic("coefficient elements exceed u64".to_owned())
        })?,
        "coefficient bytes",
    )?;
    let descriptor_bytes = size_of::<R0VmDesc>() as u64;
    let requested_bytes = source_backing_bytes
        .iter()
        .copied()
        .chain([
            eq_low_bytes,
            eq_high_bytes,
            partial_bytes,
            final_bytes,
            coefficient_bytes,
            descriptor_bytes,
            runtime_bytes,
        ])
        .try_fold(0u64, |sum, bytes| {
            sum.checked_add(bytes)
                .ok_or_else(|| R0ProductionError::Arithmetic("requested bytes overflow".to_owned()))
        })?;
    let source_slots = u32::try_from(binding.source_slots.len())
        .map_err(|_| R0ProductionError::Arithmetic("source slot count exceeds u32".to_owned()))?;
    let preflight = R0MemoryPreflight {
        source_backing_bytes,
        eq_low_bytes,
        eq_high_bytes,
        partial_bytes,
        final_bytes,
        coefficient_bytes,
        descriptor_bytes,
        runtime_bytes,
        requested_bytes,
        source_slots,
        device_free_bytes: device_memory.map(|memory| memory.0),
        device_total_bytes: device_memory.map(|memory| memory.1),
    };
    ensure_preflight_capacity(preflight)
}

fn checked_e4_bytes(elements: u64, resource: &str) -> Result<u64, R0ProductionError> {
    elements
        .checked_mul(size_of::<E4>() as u64)
        .ok_or_else(|| R0ProductionError::Arithmetic(format!("{resource} overflow")))
}

fn ensure_preflight_capacity(
    preflight: R0MemoryPreflight,
) -> Result<R0MemoryPreflight, R0ProductionError> {
    if let (Some(free_bytes), Some(total_bytes)) =
        (preflight.device_free_bytes, preflight.device_total_bytes)
    {
        if free_bytes > total_bytes {
            return Err(R0ProductionError::Arithmetic(
                "device free bytes exceed total bytes".to_owned(),
            ));
        }
        if preflight.requested_bytes > free_bytes {
            let requested_bytes = preflight.requested_bytes;
            return Err(R0ProductionError::InsufficientDeviceMemory {
                requested_bytes,
                free_bytes,
                preflight: Box::new(preflight),
            });
        }
    }
    Ok(preflight)
}

enum OwnedR0Backing {
    Bf(DeviceAllocation<BF>),
    E4(DeviceAllocation<E4>),
}

static R0_CONSTANTS_IN_USE: AtomicBool = AtomicBool::new(false);

struct R0ConstantLease;

impl R0ConstantLease {
    fn acquire() -> Result<Self, Box<dyn std::error::Error>> {
        R0_CONSTANTS_IN_USE
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .map(|_| Self)
            .map_err(|_| "another R0 harness owns the process-global CUDA constants".into())
    }
}

impl Drop for R0ConstantLease {
    fn drop(&mut self) {
        let was_in_use = R0_CONSTANTS_IN_USE.swap(false, Ordering::Release);
        debug_assert!(was_in_use, "R0 constant lease released twice");
    }
}

impl OwnedR0Backing {
    fn as_u8_ptr(&self) -> *const u8 {
        match self {
            Self::Bf(allocation) => allocation.as_ptr().cast(),
            Self::E4(allocation) => allocation.as_ptr().cast(),
        }
    }
}

pub struct R0Harness {
    coordinate: FrozenR0Coordinate,
    hashes: R0HarnessHashes,
    log_trace: u32,
    _backings: Vec<OwnedR0Backing>,
    _eq_low: DeviceAllocation<E4>,
    partials: DeviceAllocation<E4>,
    final_output: DeviceAllocation<E4>,
    stream: CudaStream,
    desc: R0VmDesc,
    production_preflight: Option<R0MemoryPreflight>,
    // Fields drop in declaration order, so this releases the process-global
    // constant state only after every allocation and the stream above it.
    _constant_lease: R0ConstantLease,
}

impl R0Harness {
    pub fn new(
        coordinate: &FrozenR0Coordinate,
        input: &ResolvedR0Input,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES)?;
        let frozen_coordinate = bundle
            .coordinates
            .iter()
            .find(|candidate| {
                candidate.circuit == coordinate.circuit && candidate.layer == coordinate.layer
            })
            .ok_or_else(|| {
                format!(
                    "coordinate {}:{} is absent from the checked R0 bundle",
                    coordinate.circuit, coordinate.layer
                )
            })?;
        if frozen_coordinate != coordinate {
            return Err(format!(
                "coordinate {}:{} differs from its checked bundle payload",
                coordinate.circuit, coordinate.layer
            )
            .into());
        }
        validate_r0_coordinate(coordinate)?;
        validate_r0_input(input)?;
        if input.identity.circuit != coordinate.circuit || input.identity.layer != coordinate.layer
        {
            return Err("resolved input belongs to another R0 coordinate".into());
        }
        validate_pinned_input(coordinate, input)?;

        let log_trace = input.identity.log_trace;
        let allocation_plan = build_lean_allocation_plan(&coordinate.binding, log_trace)?;
        validate_source_plan(&allocation_plan, input)?;
        let constant_lease = R0ConstantLease::acquire()?;
        let stream = CudaStream::default();

        let mut backings = Vec::with_capacity(input.sources.backings.len());
        for backing in &input.sources.backings {
            match backing {
                R0HostBacking::Bf(values) => {
                    let mut allocation = DeviceAllocation::<BF>::alloc(values.len())?;
                    memory_copy_async(&mut allocation, values.as_slice(), &stream)?;
                    backings.push(OwnedR0Backing::Bf(allocation));
                }
                R0HostBacking::E4(values) => {
                    let mut allocation = DeviceAllocation::<E4>::alloc(values.len())?;
                    memory_copy_async(&mut allocation, values.as_slice(), &stream)?;
                    backings.push(OwnedR0Backing::E4(allocation));
                }
            }
        }
        let backing_ptrs = backings
            .iter()
            .map(OwnedR0Backing::as_u8_ptr)
            .collect::<Vec<_>>();
        let window_bases = build_window_bases(&allocation_plan, &backing_ptrs)?;

        let mut eq_low = DeviceAllocation::<E4>::alloc(input.eq_tables.low.len())?;
        memory_copy_async(&mut eq_low, input.eq_tables.low.as_slice(), &stream)?;

        let mut coefficient_stage = [E4::ZERO; R0_COEFFICIENT_CAPACITY];
        coefficient_stage[..input.coefficient_bank.len()].copy_from_slice(&input.coefficient_bank);
        let coefficient_ptr = r0_coefficient_bank_device_ptr()?;
        let coefficient_dst =
            unsafe { DeviceSlice::from_raw_parts_mut(coefficient_ptr, R0_COEFFICIENT_CAPACITY) };
        memory_copy_async(coefficient_dst, &coefficient_stage, &stream)?;

        let mut eq_high_stage = [E4::ZERO; R0_EQ_HIGH_ELEMENTS];
        let high0_len = input.eq_tables.high[0].len();
        let high1_len = input.eq_tables.high[1].len();
        if high0_len > 256 || high1_len > 256 {
            return Err("factored high equality table exceeds its 256-element bank".into());
        }
        eq_high_stage[..high0_len].copy_from_slice(&input.eq_tables.high[0]);
        eq_high_stage[256..256 + high1_len].copy_from_slice(&input.eq_tables.high[1]);
        let eq_high_ptr = r0_eq_high_device_ptr()?;
        let eq_high_dst =
            unsafe { DeviceSlice::from_raw_parts_mut(eq_high_ptr, R0_EQ_HIGH_ELEMENTS) };
        memory_copy_async(eq_high_dst, &eq_high_stage, &stream)?;

        let mut partials = DeviceAllocation::<E4>::alloc(allocation_plan.partial_elements)?;
        let mut final_output = DeviceAllocation::<E4>::alloc(allocation_plan.final_elements)?;
        memory_set_async(unsafe { partials.transmute_mut() }, 0, &stream)?;
        memory_set_async(unsafe { final_output.transmute_mut() }, 0, &stream)?;
        let desc = build_descriptor(
            coordinate,
            input,
            &window_bases,
            eq_low.as_ptr(),
            partials.as_mut_ptr(),
        )?;

        let hashes = R0HarnessHashes {
            bundle_sha256: bundle_sha256()?,
            coordinate_sha256: coordinate.payload_sha256.clone(),
            input_sha256: input.identity.input_sha256.clone(),
            source_data_sha256: input.identity.source_data_sha256.clone(),
            independent_source_sha256: input.identity.independent_source_sha256.clone(),
            derived_source_sha256: input.identity.derived_source_sha256.clone(),
            coefficient_sha256: input.identity.coefficient_sha256.clone(),
            direct_eq_sha256: input.identity.direct_eq_sha256.clone(),
            factored_eq_sha256: input.identity.factored_eq_sha256.clone(),
            executable_sha256: executable_sha256()?,
        };

        stream.synchronize()?;
        require_no_cuda_error("R0 harness setup")?;
        Ok(Self {
            coordinate: coordinate.clone(),
            hashes,
            log_trace,
            _backings: backings,
            _eq_low: eq_low,
            partials,
            final_output,
            stream,
            desc,
            production_preflight: None,
            _constant_lease: constant_lease,
        })
    }

    pub fn new_production(
        coordinate: &FrozenR0Coordinate,
        input: &ResolvedR0Input,
        preflight: R0MemoryPreflight,
    ) -> Result<Self, R0ProductionSetupError> {
        Self::new_production_inner(coordinate, input, preflight, true)
    }

    pub fn new_prepared_production(
        coordinate: &FrozenR0Coordinate,
        prepared: PreparedR0ProductionInput,
        preflight: R0MemoryPreflight,
    ) -> Result<Self, R0ProductionSetupError> {
        let (prepared_coordinate, input) = prepared.into_parts();
        if prepared_coordinate != *coordinate {
            return Err(R0ProductionSetupError::Prelaunch(
                "prepared production coordinate differs from requested coordinate".to_owned(),
            ));
        }
        Self::new_production_inner(coordinate, &input, preflight, false)
    }

    fn new_production_inner(
        coordinate: &FrozenR0Coordinate,
        input: &ResolvedR0Input,
        preflight: R0MemoryPreflight,
        validate_input: bool,
    ) -> Result<Self, R0ProductionSetupError> {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES)
            .map_err(|error| R0ProductionSetupError::Prelaunch(error.to_string()))?;
        let frozen_coordinate = bundle
            .coordinates
            .iter()
            .find(|candidate| {
                candidate.circuit == coordinate.circuit && candidate.layer == coordinate.layer
            })
            .ok_or_else(|| {
                R0ProductionSetupError::Prelaunch(format!(
                    "coordinate {}:{} is absent from the checked R0 bundle",
                    coordinate.circuit, coordinate.layer
                ))
            })?;
        if frozen_coordinate != coordinate {
            return Err(R0ProductionSetupError::Prelaunch(format!(
                "coordinate {}:{} differs from its checked bundle payload",
                coordinate.circuit, coordinate.layer
            )));
        }
        validate_r0_coordinate(coordinate)
            .map_err(|error| R0ProductionSetupError::Prelaunch(error.to_string()))?;
        if validate_input {
            validate_r0_production_input(coordinate, input)
                .map_err(|error| R0ProductionSetupError::Prelaunch(error.to_string()))?;
        }
        let device_memory = match (preflight.device_free_bytes, preflight.device_total_bytes) {
            (Some(free), Some(total)) => Some((free, total)),
            _ => {
                return Err(R0ProductionSetupError::Prelaunch(
                    "production preflight lacks cudaMemGetInfo bytes".to_owned(),
                ));
            }
        };
        let expected_preflight = production_memory_preflight_for_binding(
            &coordinate.binding,
            input.identity.log_trace,
            coordinate.recipes.len(),
            preflight.runtime_bytes,
            device_memory,
        )?;
        if expected_preflight != preflight {
            return Err(R0ProductionSetupError::Prelaunch(
                "production preflight differs from the checked allocation plan".to_owned(),
            ));
        }

        let log_trace = input.identity.log_trace;
        let allocation_plan = build_lean_allocation_plan(&coordinate.binding, log_trace)
            .map_err(|error| R0ProductionSetupError::Prelaunch(error.to_string()))?;
        validate_source_plan(&allocation_plan, input)
            .map_err(|error| R0ProductionSetupError::Prelaunch(error.to_string()))?;
        let constant_lease = R0ConstantLease::acquire()
            .map_err(|error| R0ProductionSetupError::Prelaunch(error.to_string()))?;
        let stream = CudaStream::default();

        let mut backings = Vec::with_capacity(input.sources.backings.len());
        for backing in &input.sources.backings {
            match backing {
                R0HostBacking::Bf(values) => {
                    let mut allocation =
                        production_alloc::<BF>(values.len(), "source-bf-allocation", &preflight)?;
                    memory_copy_async(&mut allocation, values.as_slice(), &stream).map_err(
                        |error| production_cuda_error("source-bf-copy", error, &preflight),
                    )?;
                    backings.push(OwnedR0Backing::Bf(allocation));
                }
                R0HostBacking::E4(values) => {
                    let mut allocation =
                        production_alloc::<E4>(values.len(), "source-e4-allocation", &preflight)?;
                    memory_copy_async(&mut allocation, values.as_slice(), &stream).map_err(
                        |error| production_cuda_error("source-e4-copy", error, &preflight),
                    )?;
                    backings.push(OwnedR0Backing::E4(allocation));
                }
            }
        }
        let backing_ptrs = backings
            .iter()
            .map(OwnedR0Backing::as_u8_ptr)
            .collect::<Vec<_>>();
        let window_bases = build_window_bases(&allocation_plan, &backing_ptrs)
            .map_err(|error| R0ProductionSetupError::Prelaunch(error.to_string()))?;

        let mut eq_low =
            production_alloc::<E4>(input.eq_tables.low.len(), "eq-low-allocation", &preflight)?;
        memory_copy_async(&mut eq_low, input.eq_tables.low.as_slice(), &stream)
            .map_err(|error| production_cuda_error("eq-low-copy", error, &preflight))?;

        let mut coefficient_stage = [E4::ZERO; R0_COEFFICIENT_CAPACITY];
        coefficient_stage[..input.coefficient_bank.len()].copy_from_slice(&input.coefficient_bank);
        let coefficient_ptr = r0_coefficient_bank_device_ptr()
            .map_err(|error| production_cuda_error("coefficient-symbol", error, &preflight))?;
        let coefficient_dst =
            unsafe { DeviceSlice::from_raw_parts_mut(coefficient_ptr, R0_COEFFICIENT_CAPACITY) };
        memory_copy_async(coefficient_dst, &coefficient_stage, &stream)
            .map_err(|error| production_cuda_error("coefficient-copy", error, &preflight))?;

        let mut eq_high_stage = [E4::ZERO; R0_EQ_HIGH_ELEMENTS];
        let high0_len = input.eq_tables.high[0].len();
        let high1_len = input.eq_tables.high[1].len();
        if high0_len > 256 || high1_len > 256 {
            return Err(R0ProductionSetupError::Prelaunch(
                "factored high equality table exceeds its 256-element bank".to_owned(),
            ));
        }
        eq_high_stage[..high0_len].copy_from_slice(&input.eq_tables.high[0]);
        eq_high_stage[256..256 + high1_len].copy_from_slice(&input.eq_tables.high[1]);
        let eq_high_ptr = r0_eq_high_device_ptr()
            .map_err(|error| production_cuda_error("eq-high-symbol", error, &preflight))?;
        let eq_high_dst =
            unsafe { DeviceSlice::from_raw_parts_mut(eq_high_ptr, R0_EQ_HIGH_ELEMENTS) };
        memory_copy_async(eq_high_dst, &eq_high_stage, &stream)
            .map_err(|error| production_cuda_error("eq-high-copy", error, &preflight))?;

        let mut partials = production_alloc::<E4>(
            allocation_plan.partial_elements,
            "partial-allocation",
            &preflight,
        )?;
        let mut final_output = production_alloc::<E4>(
            allocation_plan.final_elements,
            "final-allocation",
            &preflight,
        )?;
        memory_set_async(unsafe { partials.transmute_mut() }, 0, &stream)
            .map_err(|error| production_cuda_error("partial-clear", error, &preflight))?;
        memory_set_async(unsafe { final_output.transmute_mut() }, 0, &stream)
            .map_err(|error| production_cuda_error("final-clear", error, &preflight))?;
        let desc = build_descriptor(
            coordinate,
            input,
            &window_bases,
            eq_low.as_ptr(),
            partials.as_mut_ptr(),
        )
        .map_err(|error| R0ProductionSetupError::Prelaunch(error.to_string()))?;

        let hashes = R0HarnessHashes {
            bundle_sha256: bundle_sha256()
                .map_err(|error| R0ProductionSetupError::Prelaunch(error.to_string()))?,
            coordinate_sha256: coordinate.payload_sha256.clone(),
            input_sha256: input.identity.input_sha256.clone(),
            source_data_sha256: input.identity.source_data_sha256.clone(),
            independent_source_sha256: input.identity.independent_source_sha256.clone(),
            derived_source_sha256: input.identity.derived_source_sha256.clone(),
            coefficient_sha256: input.identity.coefficient_sha256.clone(),
            direct_eq_sha256: input.identity.direct_eq_sha256.clone(),
            factored_eq_sha256: input.identity.factored_eq_sha256.clone(),
            executable_sha256: executable_sha256()
                .map_err(|error| R0ProductionSetupError::Prelaunch(error.to_string()))?,
        };

        stream
            .synchronize()
            .map_err(|error| production_cuda_error("setup-synchronize", error, &preflight))?;
        let error = get_last_error();
        if error != CudaError::Success {
            return Err(production_cuda_error("setup-last-error", error, &preflight));
        }
        Ok(Self {
            coordinate: coordinate.clone(),
            hashes,
            log_trace,
            _backings: backings,
            _eq_low: eq_low,
            partials,
            final_output,
            stream,
            desc,
            production_preflight: Some(preflight),
            _constant_lease: constant_lease,
        })
    }

    pub fn coordinate(&self) -> &FrozenR0Coordinate {
        &self.coordinate
    }

    pub fn hashes(&self) -> &R0HarnessHashes {
        &self.hashes
    }

    pub fn log_trace(&self) -> u32 {
        self.log_trace
    }

    pub(crate) fn prototype_descriptor_seed(&self) -> R0VmDesc {
        self.desc
    }

    pub(crate) fn stage_prototype_coefficients(
        &mut self,
        coefficients: &[E4],
    ) -> Result<(), R0ProductionSetupError> {
        let preflight = self.production_preflight.clone();
        if coefficients.len() > R0_COEFFICIENT_CAPACITY {
            return Err(R0ProductionSetupError::Prelaunch(format!(
                "prototype coefficient capacity exceeded: {} > {}",
                coefficients.len(),
                R0_COEFFICIENT_CAPACITY
            )));
        }
        let mut stage = [E4::ZERO; R0_COEFFICIENT_CAPACITY];
        stage[..coefficients.len()].copy_from_slice(coefficients);
        let coefficient_ptr = r0_coefficient_bank_device_ptr().map_err(|error| {
            specialized_cuda_error("prototype-coefficient-symbol", error, preflight.as_ref())
        })?;
        let coefficient_dst =
            unsafe { DeviceSlice::from_raw_parts_mut(coefficient_ptr, R0_COEFFICIENT_CAPACITY) };
        memory_copy_async(coefficient_dst, &stage, &self.stream).map_err(|error| {
            specialized_cuda_error("prototype-coefficient-copy", error, preflight.as_ref())
        })?;
        self.stream.synchronize().map_err(|error| {
            specialized_cuda_error(
                "prototype-coefficient-synchronize",
                error,
                preflight.as_ref(),
            )
        })?;
        let error = get_last_error();
        if error != CudaError::Success {
            return Err(specialized_cuda_error(
                "prototype-coefficient-last-error",
                error,
                preflight.as_ref(),
            ));
        }
        Ok(())
    }

    pub fn production_preflight(&self) -> Option<&R0MemoryPreflight> {
        self.production_preflight.as_ref()
    }

    pub fn run_once(
        &mut self,
        geometry: R0Geometry,
    ) -> Result<R0Observed, Box<dyn std::error::Error>> {
        let plan = geometry.launch_plan(self.log_trace)?;
        memory_set_async(unsafe { self.partials.transmute_mut() }, 0, &self.stream)?;
        memory_set_async(
            unsafe { self.final_output.transmute_mut() },
            0,
            &self.stream,
        )?;
        let launch = launch_r0_geometry(geometry, self.desc, plan, &self.stream)?;
        launch_finalize(
            self.desc.partials,
            self.final_output.as_mut_ptr(),
            plan.partial_rows,
            &self.stream,
        )?;
        let mut output = [E4::ZERO; 27];
        memory_copy_async(&mut output, &self.final_output, &self.stream)?;
        self.stream.synchronize()?;
        require_no_cuda_error(geometry.as_str())?;
        let cells = core::array::from_fn(|index| FrozenE4::from_e4(output[index]));
        let checksum = r0_cells_sha256(&cells)?;
        Ok(R0Observed {
            cells,
            checksum,
            launch,
        })
    }

    pub fn run_once_production(
        &mut self,
        geometry: R0Geometry,
    ) -> Result<R0Observed, R0ProductionSetupError> {
        let desc = self.desc;
        self.run_specialized_once(geometry, move |stream, plan| {
            launch_r0_geometry(geometry, desc, plan, stream)
        })
    }

    pub(crate) fn run_specialized_once<F>(
        &mut self,
        geometry: R0Geometry,
        launch_vm: F,
    ) -> Result<R0Observed, R0ProductionSetupError>
    where
        F: FnOnce(
            &CudaStream,
            crate::r0_geometry::R0LaunchPlan,
        ) -> era_cudart::result::CudaResult<R0LaunchMetadata>,
    {
        let preflight = self.production_preflight.clone();
        let plan = geometry
            .launch_plan(self.log_trace)
            .map_err(|error| R0ProductionSetupError::Prelaunch(error.to_string()))?;
        memory_set_async(unsafe { self.partials.transmute_mut() }, 0, &self.stream)
            .map_err(|error| specialized_cuda_error("partial-clear", error, preflight.as_ref()))?;
        memory_set_async(
            unsafe { self.final_output.transmute_mut() },
            0,
            &self.stream,
        )
        .map_err(|error| specialized_cuda_error("final-clear", error, preflight.as_ref()))?;
        let launch = launch_vm(&self.stream, plan)
            .map_err(|error| specialized_cuda_error("vm-launch", error, preflight.as_ref()))?;
        launch_finalize(
            self.desc.partials,
            self.final_output.as_mut_ptr(),
            plan.partial_rows,
            &self.stream,
        )
        .map_err(|error| specialized_cuda_error("finalizer-launch", error, preflight.as_ref()))?;
        let mut output = [E4::ZERO; 27];
        memory_copy_async(&mut output, &self.final_output, &self.stream)
            .map_err(|error| specialized_cuda_error("output-copy", error, preflight.as_ref()))?;
        self.stream.synchronize().map_err(|error| {
            specialized_cuda_error("launch-synchronize", error, preflight.as_ref())
        })?;
        let error = get_last_error();
        if error != CudaError::Success {
            return Err(specialized_cuda_error(
                "launch-last-error",
                error,
                preflight.as_ref(),
            ));
        }
        let cells = core::array::from_fn(|index| FrozenE4::from_e4(output[index]));
        let checksum = r0_cells_sha256(&cells)
            .map_err(|error| R0ProductionSetupError::Prelaunch(error.to_string()))?;
        Ok(R0Observed {
            cells,
            checksum,
            launch,
        })
    }

    pub fn measure_geometry(
        &mut self,
        geometry: R0Geometry,
        config: R0TimingConfig,
    ) -> Result<R0TimedSession, R0ProductionSetupError> {
        let desc = self.desc;
        self.measure_specialized(geometry, config, move |stream, plan| {
            launch_r0_geometry(geometry, desc, plan, stream)
        })
    }

    pub(crate) fn measure_specialized<F>(
        &mut self,
        geometry: R0Geometry,
        config: R0TimingConfig,
        mut launch_vm: F,
    ) -> Result<R0TimedSession, R0ProductionSetupError>
    where
        F: FnMut(
            &CudaStream,
            crate::r0_geometry::R0LaunchPlan,
        ) -> era_cudart::result::CudaResult<R0LaunchMetadata>,
    {
        let correctness =
            self.run_specialized_once(geometry, |stream, plan| launch_vm(stream, plan))?;
        let preflight = self.production_preflight.clone().ok_or_else(|| {
            R0ProductionSetupError::Prelaunch(
                "production timing requires a production harness".to_owned(),
            )
        })?;
        let plan = geometry
            .launch_plan(self.log_trace)
            .map_err(|error| R0ProductionSetupError::Prelaunch(error.to_string()))?;
        let start = CudaEvent::create()
            .map_err(|error| production_cuda_error("timing-start-event", error, &preflight))?;
        let stop = CudaEvent::create()
            .map_err(|error| production_cuda_error("timing-stop-event", error, &preflight))?;
        let mut samples = Vec::with_capacity((config.warmups + config.samples) as usize);

        for warmup in config.sample_kinds() {
            memory_set_async(unsafe { self.partials.transmute_mut() }, 0, &self.stream).map_err(
                |error| production_cuda_error("timing-partial-clear", error, &preflight),
            )?;
            memory_set_async(
                unsafe { self.final_output.transmute_mut() },
                0,
                &self.stream,
            )
            .map_err(|error| production_cuda_error("timing-final-clear", error, &preflight))?;
            self.stream.synchronize().map_err(|error| {
                production_cuda_error("timing-clear-synchronize", error, &preflight)
            })?;

            start
                .record(&self.stream)
                .map_err(|error| production_cuda_error("timing-start-record", error, &preflight))?;
            let launch = launch_vm(&self.stream, plan)
                .map_err(|error| production_cuda_error("timing-vm-launch", error, &preflight))?;
            if launch != correctness.launch {
                return Err(R0ProductionSetupError::Prelaunch(
                    "timing launch metadata differs from correctness launch".to_owned(),
                ));
            }
            launch_finalize(
                self.desc.partials,
                self.final_output.as_mut_ptr(),
                plan.partial_rows,
                &self.stream,
            )
            .map_err(|error| production_cuda_error("timing-finalizer-launch", error, &preflight))?;
            stop.record(&self.stream)
                .map_err(|error| production_cuda_error("timing-stop-record", error, &preflight))?;
            stop.synchronize().map_err(|error| {
                production_cuda_error("timing-stop-synchronize", error, &preflight)
            })?;
            let error = get_last_error();
            if error != CudaError::Success {
                return Err(production_cuda_error(
                    "timing-launch-last-error",
                    error,
                    &preflight,
                ));
            }
            let milliseconds = elapsed_time(&start, &stop)
                .map_err(|error| production_cuda_error("timing-elapsed", error, &preflight))?;
            samples.push(R0TimedSample {
                warmup,
                milliseconds: f64::from(milliseconds),
            });
        }

        let mut output = [E4::ZERO; 27];
        memory_copy_async(&mut output, &self.final_output, &self.stream)
            .map_err(|error| production_cuda_error("timing-checksum-copy", error, &preflight))?;
        self.stream.synchronize().map_err(|error| {
            production_cuda_error("timing-checksum-synchronize", error, &preflight)
        })?;
        let cells = core::array::from_fn(|index| FrozenE4::from_e4(output[index]));
        let post_session_checksum = r0_cells_sha256(&cells)
            .map_err(|error| R0ProductionSetupError::Prelaunch(error.to_string()))?;
        if post_session_checksum != correctness.checksum {
            return Err(R0ProductionSetupError::Prelaunch(format!(
                "timing checksum drift: correctness={} post-session={post_session_checksum}",
                correctness.checksum
            )));
        }

        Ok(R0TimedSession {
            launch: correctness.launch,
            correctness_checksum: correctness.checksum,
            post_session_checksum,
            samples,
        })
    }
}

impl From<R0ProductionError> for R0ProductionSetupError {
    fn from(error: R0ProductionError) -> Self {
        Self::Prelaunch(error.to_string())
    }
}

fn production_alloc<T>(
    length: usize,
    stage: &'static str,
    preflight: &R0MemoryPreflight,
) -> Result<DeviceAllocation<T>, R0ProductionSetupError> {
    DeviceAllocation::alloc(length).map_err(|error| production_cuda_error(stage, error, preflight))
}

fn production_cuda_error(
    stage: &'static str,
    error: CudaError,
    preflight: &R0MemoryPreflight,
) -> R0ProductionSetupError {
    R0ProductionSetupError::Cuda {
        stage,
        error: format!("{error:?}"),
        oom: error == CudaError::ErrorMemoryAllocation,
        preflight: preflight.clone(),
    }
}

fn specialized_cuda_error(
    stage: &'static str,
    error: CudaError,
    preflight: Option<&R0MemoryPreflight>,
) -> R0ProductionSetupError {
    match preflight {
        Some(preflight) => production_cuda_error(stage, error, preflight),
        None => R0ProductionSetupError::Prelaunch(format!(
            "specialized-cuda-failure: stage={stage} cuda={error:?}"
        )),
    }
}

fn validate_pinned_input(
    coordinate: &FrozenR0Coordinate,
    input: &ResolvedR0Input,
) -> Result<(), Box<dyn std::error::Error>> {
    let expected = build_r0_input(coordinate, input.identity.log_trace, input.identity.seed)?;
    if expected != *input {
        return Err("resolved input differs from the pinned coordinate semantics".into());
    }
    Ok(())
}

pub fn r0_cells_sha256(cells: &[FrozenE4; 27]) -> Result<String, Box<dyn std::error::Error>> {
    let mut bytes = Vec::with_capacity(27 * 4 * size_of::<u32>());
    for cell in cells {
        for limb in cell.limbs {
            bytes.extend_from_slice(&limb.to_le_bytes());
        }
    }
    sha256_bytes(&bytes)
}

fn validate_source_plan(
    plan: &LeanAllocationPlan,
    input: &ResolvedR0Input,
) -> Result<(), Box<dyn std::error::Error>> {
    if plan.trace_len != input.sources.trace_len
        || plan.windows.len() != input.sources.windows.len()
        || plan.backings.len() != input.sources.backings.len()
        || plan.eq_sizes != input.eq_tables.sizes
        || plan.eq_low_elements != input.eq_tables.low.len()
    {
        return Err("resolved input and shared lean allocation plan differ".into());
    }
    for (index, (planned, actual)) in plan
        .backings
        .iter()
        .zip(&input.sources.backings)
        .enumerate()
    {
        let matches = match (planned.field, actual) {
            (FieldKind::Base, R0HostBacking::Bf(values)) => {
                values.len().checked_mul(size_of::<BF>()) == Some(planned.bytes)
            }
            (FieldKind::Ext, R0HostBacking::E4(values)) => {
                values.len().checked_mul(size_of::<E4>()) == Some(planned.bytes)
            }
            _ => false,
        };
        if !matches {
            return Err(format!("resolved source backing {index} differs from shared plan").into());
        }
    }
    for (index, (planned, actual)) in plan.windows.iter().zip(&input.sources.windows).enumerate() {
        let field = match planned.field {
            FieldKind::Base => FrozenField::Bf,
            FieldKind::Ext => FrozenField::E4,
        };
        if actual.field != field
            || actual.backing_index != planned.backing
            || actual.first_element != planned.base_element
            || actual.procedural_kind != planned.procedural_kind
        {
            return Err(format!("resolved source window {index} differs from shared plan").into());
        }
    }
    Ok(())
}

fn build_window_bases(
    plan: &LeanAllocationPlan,
    backing_ptrs: &[*const u8],
) -> Result<Vec<R0WindowAddr>, Box<dyn std::error::Error>> {
    if plan.backings.len() != backing_ptrs.len() {
        return Err("device backing pointers and shared allocation plan differ".into());
    }
    plan.windows
        .iter()
        .enumerate()
        .map(|(index, window)| {
            let base = match window.backing {
                Some(backing) => backing_ptrs
                    .get(backing)
                    .copied()
                    .ok_or_else(|| format!("window {index} has a missing device backing"))?
                    .wrapping_add(window.base_offset_bytes),
                None if window.procedural_kind.is_some() => core::ptr::null(),
                None => return Err(format!("window {index} has no backing or procedure")),
            };
            Ok(R0WindowAddr {
                base,
                log2_stride: window.log2_stride,
                origin: window.origin,
                procedural_kind: window.procedural_kind.unwrap_or(u8::MAX),
                reserved: [0; 5],
            })
        })
        .collect::<Result<Vec<_>, String>>()
        .map_err(Into::into)
}

fn build_descriptor(
    coordinate: &FrozenR0Coordinate,
    input: &ResolvedR0Input,
    window_bases: &[R0WindowAddr],
    eq_low: *const E4,
    partials: *mut E4,
) -> Result<R0VmDesc, Box<dyn std::error::Error>> {
    Ok(R0VmDesc::from_coordinate(
        coordinate,
        window_bases,
        input.identity.log_trace,
        eq_low,
        partials,
        input.eq_tables.sizes,
        input.coefficient_bank.len(),
    )?)
}

fn bundle_sha256() -> Result<String, Box<dyn std::error::Error>> {
    static HASH: OnceLock<Result<String, String>> = OnceLock::new();
    HASH.get_or_init(|| sha256_bytes(R0_CORPUS_BYTES).map_err(|error| error.to_string()))
        .clone()
        .map_err(Into::into)
}

fn executable_sha256() -> Result<String, Box<dyn std::error::Error>> {
    static HASH: OnceLock<Result<String, String>> = OnceLock::new();
    HASH.get_or_init(|| {
        let path = std::env::current_exe().map_err(|error| error.to_string())?;
        sha256_file(&path).map_err(|error| error.to_string())
    })
    .clone()
    .map_err(Into::into)
}

fn sha256_bytes(bytes: &[u8]) -> Result<String, Box<dyn std::error::Error>> {
    let mut child = Command::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    child
        .stdin
        .as_mut()
        .ok_or("sha256sum stdin is unavailable")?
        .write_all(bytes)?;
    parse_sha256_output(child.wait_with_output()?)
}

fn sha256_file(path: &Path) -> Result<String, Box<dyn std::error::Error>> {
    parse_sha256_output(Command::new("sha256sum").arg(path).output()?)
}

fn parse_sha256_output(output: std::process::Output) -> Result<String, Box<dyn std::error::Error>> {
    if !output.status.success() {
        return Err("sha256sum failed".into());
    }
    let output = String::from_utf8(output.stdout)?;
    let hash = output.split_whitespace().next().unwrap_or_default();
    if hash.len() != 64
        || !hash
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err("sha256sum output is not lowercase SHA-256".into());
    }
    Ok(hash.to_owned())
}

fn require_no_cuda_error(context: &str) -> Result<(), Box<dyn std::error::Error>> {
    let error = get_last_error();
    if error == CudaError::Success {
        Ok(())
    } else {
        Err(format!("{context}: CUDA error {error:?}").into())
    }
}

#[cfg(test)]
mod tests {
    use field::PrimeField;

    use crate::abi::C_INIT_NONE;
    use crate::r0_artifact::{decode_r0_bundle, pack_r0_source, R0_CORPUS_BYTES};
    use crate::r0_input::{build_r0_input, refresh_r0_input_hashes};
    use gpu_gkr_compiler::backward::{
        LeanBoundColumn, LeanBoundWindow, LeanSourceBinding, LeanSourceSlot, WindowFamily,
    };

    use super::*;

    #[test]
    fn cpu_timing_config_pins_five_warmups_then_fifty_samples() {
        let config = R0TimingConfig::production_traversal();
        assert_eq!(config.warmups(), 5);
        assert_eq!(config.samples(), 50);
        let kinds = config.sample_kinds().collect::<Vec<_>>();
        assert_eq!(kinds.len(), 55);
        assert!(kinds[..5].iter().all(|warmup| *warmup));
        assert!(kinds[5..].iter().all(|warmup| !*warmup));
    }

    #[test]
    fn cpu_prepared_production_constructor_keeps_checked_public_boundary() {
        let source = include_str!("r0_harness.rs");
        assert!(source.contains("Self::new_production_inner(coordinate, input, preflight, true)"));
        assert!(source.contains("Self::new_production_inner(coordinate, &input, preflight, false)"));
        assert!(source.contains("if validate_input {\n            validate_r0_production_input"));
    }

    struct DescriptorFixture {
        desc: R0VmDesc,
        window_bases: Vec<R0WindowAddr>,
        literal_coefficient_uses: usize,
        banked_coefficient_uses: usize,
    }

    fn perturb_backing_element(backing: &mut R0HostBacking, index: usize) {
        match backing {
            R0HostBacking::Bf(values) => {
                values[index].add_assign(&BF::ONE);
            }
            R0HostBacking::E4(values) => {
                values[index].add_assign(&E4::ONE);
            }
        }
    }

    fn rehashed_source_mutation(input: &ResolvedR0Input, derived: bool) -> ResolvedR0Input {
        for (backing_index, backing) in input.sources.backings.iter().enumerate() {
            let len = match backing {
                R0HostBacking::Bf(values) => values.len(),
                R0HostBacking::E4(values) => values.len(),
            };
            if len == 0 {
                continue;
            }
            let candidates = [0, len / 2, len - 1];
            for element_index in candidates {
                let mut mutated = input.clone();
                perturb_backing_element(
                    &mut mutated.sources.backings[backing_index],
                    element_index,
                );
                refresh_r0_input_hashes(&mut mutated).unwrap();
                let selected_hash_changed = if derived {
                    mutated.identity.derived_source_sha256 != input.identity.derived_source_sha256
                } else {
                    mutated.identity.independent_source_sha256
                        != input.identity.independent_source_sha256
                };
                if selected_hash_changed {
                    return mutated;
                }
            }
        }
        panic!("fixture has no mutable requested source class");
    }

    fn build_r0_descriptor_fixture(
        coordinate: &FrozenR0Coordinate,
    ) -> Result<DescriptorFixture, Box<dyn std::error::Error>> {
        let input = build_r0_input(coordinate, 3, 0)?;
        let plan = build_lean_allocation_plan(&coordinate.binding, 3)?;
        validate_source_plan(&plan, &input)?;
        let backing_ptrs = (0..plan.backings.len())
            .map(|index| (0x1000usize + index * 0x10_0000) as *const u8)
            .collect::<Vec<_>>();
        let window_bases = build_window_bases(&plan, &backing_ptrs)?;
        let desc = build_descriptor(
            coordinate,
            &input,
            &window_bases,
            core::ptr::NonNull::<E4>::dangling().as_ptr(),
            core::ptr::NonNull::<E4>::dangling().as_ptr(),
        )?;
        let mut literal_coefficient_uses = 0;
        let mut banked_coefficient_uses = 0;
        for record in coordinate.program_words.chunks_exact(4) {
            match classify_r0_coefficient(u32::from(record[0] & 0x1fff), coordinate.recipes.len())?
            {
                R0CoefficientRef::One | R0CoefficientRef::NegOne => {
                    literal_coefficient_uses += 1;
                }
                R0CoefficientRef::Banked(_) => banked_coefficient_uses += 1,
            }
        }
        Ok(DescriptorFixture {
            desc,
            window_bases,
            literal_coefficient_uses,
            banked_coefficient_uses,
        })
    }

    #[test]
    fn cpu_r0_descriptor_builder_is_exact_and_zero_fills_capacity() {
        let coordinate = decode_r0_bundle(R0_CORPUS_BYTES)
            .unwrap()
            .coordinates
            .into_iter()
            .find(|coordinate| {
                coordinate.circuit == "add_sub_lui_auipc_mop" && coordinate.layer == 0
            })
            .unwrap();
        let built = build_r0_descriptor_fixture(&coordinate).unwrap();

        assert_eq!(
            &built.desc.program[..coordinate.program_words.len()],
            coordinate.program_words
        );
        assert!(built.desc.program[coordinate.program_words.len()..]
            .iter()
            .all(|word| *word == 0));
        assert_eq!(
            built.desc.record_count as usize,
            coordinate.term_count as usize
        );
        assert_eq!(
            built.desc.source_count as usize,
            coordinate.binding.source_slots.len()
        );
        assert_eq!(
            built.desc.banked_coefficient_count as usize,
            coordinate.recipes.len()
        );
        assert_eq!(built.desc.c_init, C_INIT_NONE);
        assert!(
            built.desc.source_slots[coordinate.binding.source_slots.len()..]
                .iter()
                .all(|source| *source == 0)
        );
        for (actual, source) in built
            .desc
            .source_slots
            .iter()
            .zip(&coordinate.binding.source_slots)
        {
            assert_eq!(
                *actual,
                pack_r0_source(source.window, source.column).unwrap()
            );
        }
        assert!(built.desc.window_bases[coordinate.binding.windows.len()..]
            .iter()
            .all(|window| window.is_zero()));
        assert_eq!(
            &built.desc.window_bases[..coordinate.binding.windows.len()],
            built.window_bases.as_slice()
        );
        let actual_program_bytes = built.desc.program[..coordinate.program_words.len()]
            .iter()
            .flat_map(|word| word.to_ne_bytes())
            .collect::<Vec<_>>();
        let expected_program_bytes = coordinate
            .program_words
            .iter()
            .flat_map(|word| word.to_le_bytes())
            .collect::<Vec<_>>();
        assert_eq!(actual_program_bytes, expected_program_bytes);
        assert_eq!(
            built.literal_coefficient_uses + built.banked_coefficient_uses,
            coordinate.term_count as usize
        );

        let zero_cells = core::array::from_fn(|_| FrozenE4 { limbs: [0; 4] });
        assert_eq!(
            r0_cells_sha256(&zero_cells).unwrap(),
            "1fe2373734955e60c172999142934b52e69ba7ab9039b3c18ea54082ba32afcd"
        );
    }

    #[test]
    fn cpu_r0_constant_lease_is_exclusive_and_releases() {
        let first = R0ConstantLease::acquire().unwrap();
        assert!(R0ConstantLease::acquire().is_err());
        drop(first);
        assert!(R0ConstantLease::acquire().is_ok());
    }

    #[test]
    fn cpu_production_preflight_counts_mixed_sparse_backings_exactly() {
        let binding = LeanSourceBinding {
            windows: vec![
                LeanBoundWindow {
                    family: WindowFamily::BaseLayerMemory,
                    first_column: 0,
                    columns: vec![LeanBoundColumn {
                        column: 0,
                        source: 0,
                    }],
                },
                LeanBoundWindow {
                    family: WindowFamily::BaseLayerMemory,
                    first_column: 128,
                    columns: vec![LeanBoundColumn {
                        column: 130,
                        source: 1,
                    }],
                },
                LeanBoundWindow {
                    family: WindowFamily::LayerOutput {
                        layer: 0,
                        ext: true,
                    },
                    first_column: 0,
                    columns: vec![LeanBoundColumn {
                        column: 3,
                        source: 2,
                    }],
                },
            ],
            source_slots: vec![
                LeanSourceSlot {
                    window: 0,
                    column: 0,
                },
                LeanSourceSlot {
                    window: 2,
                    column: 3,
                },
            ],
        };
        let preflight =
            production_memory_preflight_for_binding(&binding, 3, 3, 4_096, Some((30_000, 40_000)))
                .unwrap();
        assert_eq!(
            preflight.source_backing_bytes,
            vec![131 * 8 * 4, 4 * 8 * 16]
        );
        assert_eq!(preflight.source_backing_bytes.iter().sum::<u64>(), 4_704);
        assert!(
            preflight.source_backing_bytes.iter().sum::<u64>()
                > preflight.source_slots as u64 * 8 * 16
        );
        assert_eq!(preflight.eq_low_bytes, 16);
        assert_eq!(preflight.eq_high_bytes, 0);
        assert_eq!(preflight.partial_bytes, 27 * 16);
        assert_eq!(preflight.final_bytes, 27 * 16);
        assert_eq!(preflight.coefficient_bytes, 3 * 16);
        assert_eq!(preflight.descriptor_bytes, 17_536);
        assert_eq!(preflight.runtime_bytes, 4_096);
        assert_eq!(preflight.requested_bytes, 27_264);
        assert_eq!(preflight.device_free_bytes, Some(30_000));
        assert_eq!(preflight.device_total_bytes, Some(40_000));
    }

    #[test]
    fn cpu_production_preflight_rejects_overflow_and_capacity_before_allocation() {
        let binding = LeanSourceBinding {
            windows: vec![LeanBoundWindow {
                family: WindowFamily::BaseLayerMemory,
                first_column: 0,
                columns: vec![LeanBoundColumn {
                    column: 0,
                    source: 0,
                }],
            }],
            source_slots: vec![LeanSourceSlot {
                window: 0,
                column: 0,
            }],
        };
        assert!(matches!(
            production_memory_preflight_for_binding(&binding, 3, 0, u64::MAX, None),
            Err(R0ProductionError::Arithmetic(_))
        ));
        let error =
            production_memory_preflight_for_binding(&binding, 3, 0, 0, Some((1, 2))).unwrap_err();
        assert!(matches!(
            error,
            R0ProductionError::InsufficientDeviceMemory { .. }
        ));
    }

    #[test]
    fn cpu_checked_harness_rejects_rehashed_coordinate_semantic_mutations() {
        let coordinate = decode_r0_bundle(R0_CORPUS_BYTES)
            .unwrap()
            .coordinates
            .into_iter()
            .find(|coordinate| {
                coordinate.circuit == "add_sub_lui_auipc_mop" && coordinate.layer == 0
            })
            .unwrap();
        let input = build_r0_input(&coordinate, 8, 0).unwrap();
        let mut coefficient = input.clone();
        coefficient.coefficient_bank[0].add_assign(&E4::ONE);
        refresh_r0_input_hashes(&mut coefficient).unwrap();
        let independent_source = rehashed_source_mutation(&input, false);
        let derived_source = rehashed_source_mutation(&input, true);

        for mutated in [coefficient, independent_source, derived_source] {
            validate_r0_input(&mutated).unwrap();
            assert!(validate_pinned_input(&coordinate, &mutated).is_err());
        }
    }

    #[test]
    #[ignore = "requires the repository GPU lock"]
    fn gpu_second_live_r0_harness_is_rejected_before_constant_staging() {
        let coordinate = decode_r0_bundle(R0_CORPUS_BYTES)
            .unwrap()
            .coordinates
            .into_iter()
            .find(|coordinate| {
                coordinate.circuit == "add_sub_lui_auipc_mop" && coordinate.layer == 0
            })
            .unwrap();
        let first_input = build_r0_input(&coordinate, 3, 0).unwrap();
        let second_input = build_r0_input(&coordinate, 3, 1).unwrap();
        let _first = R0Harness::new(&coordinate, &first_input).unwrap();
        let error = match R0Harness::new(&coordinate, &second_input) {
            Ok(_) => panic!("second live harness silently replaced global constants"),
            Err(error) => error,
        };
        assert!(error
            .to_string()
            .contains("another R0 harness owns the process-global CUDA constants"));
    }
}
