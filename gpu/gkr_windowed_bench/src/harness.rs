use core::mem::size_of;

use era_cudart::error::get_last_error;
use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::memory::{memory_copy_async, memory_set_async, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaError;

use crate::abi::{
    WindowAddrSlot, WindowBaseRecord, WindowInstruction, WindowVmDesc, BF, C_INIT_NONE, E4,
    IMMEDIATE_CAPACITY, PROGRAM_CAPACITY, SLOT_CAPACITY, WINDOW_CELLS,
};
use crate::artifact::{
    decode_artifact, decode_program, FrozenArtifact, FrozenField, WindowAtom, WindowClass,
    WindowTerm, ADD_SUB_LAYER0_BYTES,
};
use crate::geometry::{build_allocation_plan, AllocationPlan, GeometryError};
use crate::kernels::{
    coefficient_bank_device_ptr, configure_window_vm_shared_carveout, eq_high_device_ptr,
    launch_finalize, launch_init_bf, launch_init_e4, launch_window_vm, COEFFICIENT_CAPACITY,
    EQ_HIGH_ELEMENTS,
};
use crate::nvtx::NvtxRange;
use crate::timing::{summarize_samples, TimingSummary};

const PROFILE_RANGE: &str = "gkr_windowed_add_sub_l0_first_window";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AllocationReport {
    pub backing_bytes: Vec<(crate::artifact::FrozenWindowFamily, usize)>,
    pub bf_backing_bytes: usize,
    pub e4_backing_bytes: usize,
    pub program_bytes: usize,
    pub source_bytes: usize,
    pub slot_bytes: usize,
    pub immediate_bytes: usize,
    pub eq_low_bytes: usize,
    pub launch_parameter_bytes: usize,
    pub partial_bytes: usize,
    pub final_bytes: usize,
    pub constant_bytes: usize,
    pub total_resident_bytes: usize,
    pub logical_rows: u32,
    pub num_blocks: u32,
}

impl AllocationReport {
    pub fn from_plan(
        artifact: &FrozenArtifact,
        plan: &AllocationPlan,
        coefficient_capacity: usize,
    ) -> Result<Self, BenchError> {
        let backing_bytes = plan
            .backings
            .iter()
            .map(|backing| (backing.family, backing.bytes))
            .collect::<Vec<_>>();
        let bf_backing_bytes = plan
            .backings
            .iter()
            .filter(|backing| backing.field == FrozenField::Base)
            .try_fold(0usize, |sum, backing| sum.checked_add(backing.bytes))
            .ok_or_else(|| BenchError("BF backing byte count overflow".to_owned()))?;
        let e4_backing_bytes = plan
            .backings
            .iter()
            .filter(|backing| backing.field == FrozenField::Ext)
            .try_fold(0usize, |sum, backing| sum.checked_add(backing.bytes))
            .ok_or_else(|| BenchError("E4 backing byte count overflow".to_owned()))?;
        let program_bytes = artifact.program.len() * size_of::<WindowInstruction>();
        let slot_bytes = plan.windows.len() * size_of::<WindowBaseRecord>();
        let immediate_bytes = artifact.immediates.len() * size_of::<u32>();
        let eq_low_bytes = plan.eq_low_elements * size_of::<E4>();
        let launch_parameter_bytes = size_of::<WindowVmDesc>();
        let partial_bytes = plan.partial_elements * size_of::<E4>();
        let final_bytes = plan.final_elements * size_of::<E4>();
        let constant_bytes = (coefficient_capacity + EQ_HIGH_ELEMENTS) * size_of::<E4>();
        let total_resident_bytes = [
            bf_backing_bytes,
            e4_backing_bytes,
            eq_low_bytes,
            partial_bytes,
            final_bytes,
            constant_bytes,
        ]
        .into_iter()
        .try_fold(0usize, usize::checked_add)
        .ok_or_else(|| BenchError("total resident byte count overflow".to_owned()))?;
        Ok(Self {
            backing_bytes,
            bf_backing_bytes,
            e4_backing_bytes,
            program_bytes,
            source_bytes: 0,
            slot_bytes,
            immediate_bytes,
            eq_low_bytes,
            launch_parameter_bytes,
            partial_bytes,
            final_bytes,
            constant_bytes,
            total_resident_bytes,
            logical_rows: plan.logical_rows,
            num_blocks: plan.num_blocks,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BenchError(pub String);

impl BenchError {
    fn cuda(context: &str, error: CudaError) -> Self {
        Self(format!("{context}: {error:?}"))
    }
}

impl core::fmt::Display for BenchError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for BenchError {}

impl From<GeometryError> for BenchError {
    fn from(error: GeometryError) -> Self {
        Self(format!("allocation geometry: {error}"))
    }
}

fn window_base_records(slots: &[WindowAddrSlot]) -> Vec<WindowBaseRecord> {
    slots
        .iter()
        .map(|slot| WindowBaseRecord { base: slot.base })
        .collect()
}

enum OwnedBacking {
    Bf(DeviceAllocation<BF>),
    E4(DeviceAllocation<E4>),
}

impl OwnedBacking {
    fn as_u8_ptr(&self) -> *const u8 {
        match self {
            Self::Bf(allocation) => allocation.as_ptr().cast(),
            Self::E4(allocation) => allocation.as_ptr().cast(),
        }
    }
}

pub struct WindowedHarness {
    stream: CudaStream,
    artifact: FrozenArtifact,
    plan: AllocationPlan,
    _backings: Vec<OwnedBacking>,
    _eq_low: DeviceAllocation<E4>,
    descriptor: WindowVmDesc,
    partials: DeviceAllocation<E4>,
    final_output: DeviceAllocation<E4>,
    report: AllocationReport,
}

impl WindowedHarness {
    pub fn new(log_trace: u32) -> Result<Self, BenchError> {
        let artifact = decode_artifact(ADD_SUB_LAYER0_BYTES)
            .map_err(|error| BenchError(format!("decode frozen artifact: {error}")))?;
        if artifact.coefficient_count as usize > COEFFICIENT_CAPACITY {
            return Err(BenchError(format!(
                "artifact needs {} coefficients, compiled capacity is {COEFFICIENT_CAPACITY}",
                artifact.coefficient_count
            )));
        }
        let plan = build_allocation_plan(&artifact, log_trace)?;
        let report = AllocationReport::from_plan(&artifact, &plan, COEFFICIENT_CAPACITY)?;
        let inline_program =
            inline_table::<WindowInstruction, PROGRAM_CAPACITY>(&artifact.program, "program")?;
        let inline_immediates =
            inline_table::<u32, IMMEDIATE_CAPACITY>(&artifact.immediates, "immediate table")?;
        let stream = CudaStream::default();
        configure_window_vm_shared_carveout()
            .map_err(|error| BenchError::cuda("configure window VM shared carveout", error))?;

        let mut backings = Vec::with_capacity(plan.backings.len());
        for (index, backing) in plan.backings.iter().enumerate() {
            let seed = 0x1000u32.wrapping_add(index as u32 * 0x101);
            match backing.field {
                FrozenField::Base => {
                    let mut allocation =
                        DeviceAllocation::<BF>::alloc(backing.bytes / size_of::<BF>())
                            .map_err(|error| BenchError::cuda("allocate BF backing", error))?;
                    launch_init_bf(&mut allocation, seed, &stream)
                        .map_err(|error| BenchError::cuda("initialize BF backing", error))?;
                    backings.push(OwnedBacking::Bf(allocation));
                }
                FrozenField::Ext => {
                    let mut allocation =
                        DeviceAllocation::<E4>::alloc(backing.bytes / size_of::<E4>())
                            .map_err(|error| BenchError::cuda("allocate E4 backing", error))?;
                    launch_init_e4(&mut allocation, seed, &stream)
                        .map_err(|error| BenchError::cuda("initialize E4 backing", error))?;
                    backings.push(OwnedBacking::E4(allocation));
                }
            }
        }

        let host_slots = plan
            .windows
            .iter()
            .map(|window| WindowAddrSlot {
                base: window
                    .backing
                    .map(|index| {
                        backings[index]
                            .as_u8_ptr()
                            .wrapping_add(window.base_offset_bytes)
                    })
                    .unwrap_or(core::ptr::null()),
                log2_stride: window.log2_stride,
                origin: window.origin,
                procedural_kind: window.procedural_kind,
                reserved: [0; 5],
            })
            .collect::<Vec<_>>();
        let window_bases = window_base_records(&host_slots);
        let inline_window_bases =
            inline_table::<WindowBaseRecord, SLOT_CAPACITY>(&window_bases, "window base table")?;
        let mut eq_low = DeviceAllocation::<E4>::alloc(plan.eq_low_elements)
            .map_err(|error| BenchError::cuda("allocate low equality table", error))?;
        launch_init_e4(&mut eq_low, 0x4000, &stream)
            .map_err(|error| BenchError::cuda("initialize low equality table", error))?;
        let mut partials = DeviceAllocation::<E4>::alloc(plan.partial_elements)
            .map_err(|error| BenchError::cuda("allocate block partials", error))?;
        let mut final_output = DeviceAllocation::<E4>::alloc(plan.final_elements)
            .map_err(|error| BenchError::cuda("allocate final output", error))?;
        memory_set_async(unsafe { partials.transmute_mut() }, 0, &stream)
            .map_err(|error| BenchError::cuda("clear block partials", error))?;
        memory_set_async(unsafe { final_output.transmute_mut() }, 0, &stream)
            .map_err(|error| BenchError::cuda("clear final output", error))?;

        let mut constant_staging = DeviceAllocation::<E4>::alloc(EQ_HIGH_ELEMENTS)
            .map_err(|error| BenchError::cuda("allocate constant staging", error))?;
        launch_init_e4(&mut constant_staging, 0x6000, &stream)
            .map_err(|error| BenchError::cuda("initialize constant staging", error))?;
        let coefficient_ptr = coefficient_bank_device_ptr()
            .map_err(|error| BenchError::cuda("resolve coefficient bank", error))?;
        let coefficient_dst =
            unsafe { DeviceSlice::from_raw_parts_mut(coefficient_ptr, COEFFICIENT_CAPACITY) };
        memory_copy_async(
            coefficient_dst,
            &constant_staging[..COEFFICIENT_CAPACITY],
            &stream,
        )
        .map_err(|error| BenchError::cuda("upload coefficient bank", error))?;
        let eq_high_ptr = eq_high_device_ptr()
            .map_err(|error| BenchError::cuda("resolve high equality table", error))?;
        let eq_high_dst = unsafe { DeviceSlice::from_raw_parts_mut(eq_high_ptr, EQ_HIGH_ELEMENTS) };
        memory_copy_async(eq_high_dst, &constant_staging, &stream)
            .map_err(|error| BenchError::cuda("upload high equality table", error))?;

        let descriptor = WindowVmDesc {
            program: inline_program,
            window_bases: inline_window_bases,
            immediates: inline_immediates,
            eq_low: eq_low.as_ptr(),
            partials: partials.as_mut_ptr(),
            program_records: artifact.program.len() as u32,
            term_count: artifact.term_count,
            record_count: artifact.record_count,
            num_immediates: artifact.immediates.len() as u32,
            num_coefficients: artifact.coefficient_count,
            c_init_coeff: artifact.c_init_coeff.unwrap_or(C_INIT_NONE),
            log_rows: plan.log_rows,
            eq_sizes: plan.eq_sizes,
        };
        stream
            .synchronize()
            .map_err(|error| BenchError::cuda("synchronize initialization", error))?;
        let last_error = get_last_error();
        if last_error != CudaError::Success {
            return Err(BenchError::cuda("initialization CUDA error", last_error));
        }

        Ok(Self {
            stream,
            artifact,
            plan,
            _backings: backings,
            _eq_low: eq_low,
            descriptor,
            partials,
            final_output,
            report,
        })
    }

    pub fn launch_pair(&mut self) -> Result<(), BenchError> {
        launch_window_vm(self.descriptor, self.plan.num_blocks, &self.stream)
            .map_err(|error| BenchError::cuda("launch window VM", error))?;
        launch_finalize(
            self.partials.as_ptr(),
            self.final_output.as_mut_ptr(),
            self.plan.num_blocks,
            &self.stream,
        )
        .map_err(|error| BenchError::cuda("launch final reduction", error))?;
        Ok(())
    }

    pub fn measure(
        &mut self,
        warmup: u32,
        iterations: u32,
        profile: bool,
    ) -> Result<TimingSummary, BenchError> {
        if iterations == 0 {
            return Err(BenchError("iterations must be nonzero".to_owned()));
        }
        for _ in 0..warmup {
            self.launch_pair()?;
        }
        self.stream
            .synchronize()
            .map_err(|error| BenchError::cuda("synchronize warmup", error))?;

        let start =
            CudaEvent::create().map_err(|error| BenchError::cuda("create start event", error))?;
        let end =
            CudaEvent::create().map_err(|error| BenchError::cuda("create end event", error))?;
        let measured_iterations = if profile { 1 } else { iterations };
        let mut samples = Vec::with_capacity(measured_iterations as usize);
        for _ in 0..measured_iterations {
            start
                .record(&self.stream)
                .map_err(|error| BenchError::cuda("record start event", error))?;
            let range = if profile {
                Some(
                    NvtxRange::start(PROFILE_RANGE)
                        .map_err(|error| BenchError(format!("create NVTX range: {error}")))?,
                )
            } else {
                None
            };
            self.launch_pair()?;
            drop(range);
            end.record(&self.stream)
                .map_err(|error| BenchError::cuda("record end event", error))?;
            end.synchronize()
                .map_err(|error| BenchError::cuda("synchronize end event", error))?;
            samples.push(
                elapsed_time(&start, &end)
                    .map_err(|error| BenchError::cuda("measure CUDA events", error))?,
            );
        }
        summarize_samples(samples).map_err(|error| BenchError(error.to_owned()))
    }

    pub fn observe_final(&mut self) -> Result<[E4; WINDOW_CELLS as usize], BenchError> {
        let mut output = vec![unsafe { core::mem::zeroed::<E4>() }; WINDOW_CELLS as usize];
        memory_copy_async(&mut output, &self.final_output, &self.stream)
            .map_err(|error| BenchError::cuda("copy final output", error))?;
        self.stream
            .synchronize()
            .map_err(|error| BenchError::cuda("synchronize final output", error))?;
        output
            .try_into()
            .map_err(|_| BenchError("final output length changed".to_owned()))
    }

    pub fn allocation_report(&self) -> &AllocationReport {
        &self.report
    }

    pub fn artifact(&self) -> &FrozenArtifact {
        &self.artifact
    }

    pub fn plan(&self) -> &AllocationPlan {
        &self.plan
    }

    pub fn stream(&self) -> &CudaStream {
        &self.stream
    }
}

fn inline_table<T: Copy + Default, const N: usize>(
    values: &[T],
    name: &str,
) -> Result<[T; N], BenchError> {
    if values.len() > N {
        return Err(BenchError(format!(
            "{name} has {} entries, inline capacity is {N}",
            values.len()
        )));
    }
    let mut table = [T::default(); N];
    table[..values.len()].copy_from_slice(values);
    Ok(table)
}

pub fn estimated_source_bytes(
    artifact: &FrozenArtifact,
    plan: &AllocationPlan,
) -> Result<u64, BenchError> {
    let (atoms, _) = decode_program(artifact)
        .map_err(|error| BenchError(format!("decode program for byte estimate: {error}")))?;
    let bytes_per_lane_block = atoms.iter().try_fold(0u64, |sum, atom| {
        let atom_bytes = match atom {
            WindowAtom::Term(term) => estimated_term_source_bytes(term),
            WindowAtom::GroupBf { members, .. } | WindowAtom::GroupE4 { members, .. } => {
                members.iter().try_fold(0u64, |sum, member| {
                    sum.checked_add(estimated_term_source_bytes(member)?)
                })
            }
        }
        .ok_or_else(|| BenchError("source byte estimate overflow".to_owned()))?;
        sum.checked_add(atom_bytes)
            .ok_or_else(|| BenchError("source byte estimate overflow".to_owned()))
    })?;
    bytes_per_lane_block
        .checked_mul(32)
        .and_then(|bytes| bytes.checked_mul(u64::from(plan.num_blocks)))
        .ok_or_else(|| BenchError("source byte estimate overflow".to_owned()))
}

fn estimated_term_source_bytes(term: &WindowTerm) -> Option<u64> {
    match term.class {
        WindowClass::LinearBf => Some(4 * 2 * size_of::<BF>() as u64),
        WindowClass::LinearBfProceduralA => Some(0),
        WindowClass::LinearE4 => Some(4 * 2 * size_of::<E4>() as u64),
        WindowClass::ProductBfBf => Some(32 * 2 * size_of::<BF>() as u64),
        WindowClass::ProductBfBfProceduralB => Some(32 * size_of::<BF>() as u64),
        WindowClass::ProductBfE4 => Some(32 * (size_of::<BF>() + size_of::<E4>()) as u64),
        WindowClass::ProductE4E4 => Some(32 * 2 * size_of::<E4>() as u64),
        WindowClass::GroupBf | WindowClass::GroupE4 => None,
    }
}

#[cfg(test)]
mod tests {
    use crate::geometry::{build_allocation_plan, tests::geometry_fixture};

    use super::*;

    #[test]
    fn allocation_report_accounts_for_dynamic_and_constant_storage() {
        let artifact = geometry_fixture();
        let plan = build_allocation_plan(&artifact, 8).unwrap();
        let report = AllocationReport::from_plan(&artifact, &plan, 80).unwrap();

        assert_eq!(report.bf_backing_bytes, 134_144);
        assert_eq!(report.e4_backing_bytes, 16_384);
        assert_eq!(report.program_bytes, 8);
        assert_eq!(report.source_bytes, 0);
        assert_eq!(report.slot_bytes, 32);
        assert_eq!(report.immediate_bytes, 0);
        assert_eq!(report.eq_low_bytes, 512);
        assert_eq!(report.launch_parameter_bytes, 1_536);
        assert_eq!(report.partial_bytes, 432);
        assert_eq!(report.final_bytes, 432);
        assert_eq!(report.constant_bytes, 9_472);
        assert_eq!(report.total_resident_bytes, 161_376);
    }

    #[test]
    fn inline_table_zero_fills_unused_capacity() {
        let table = inline_table::<u32, 4>(&[11, 22], "test table").unwrap();
        assert_eq!(table, [11, 22, 0, 0]);
    }

    #[test]
    fn inline_table_rejects_values_past_capacity() {
        let error = inline_table::<u32, 2>(&[11, 22, 33], "test table").unwrap_err();
        assert_eq!(error.0, "test table has 3 entries, inline capacity is 2");
    }

    #[test]
    fn source_byte_estimate_counts_all_nine_warp_selector_shapes() {
        let artifact = geometry_fixture();
        let plan = build_allocation_plan(&artifact, 8).unwrap();
        assert_eq!(estimated_source_bytes(&artifact, &plan).unwrap(), 1_024);
    }

    #[test]
    fn procedural_operands_add_no_source_load_bytes() {
        let artifact = decode_artifact(ADD_SUB_LAYER0_BYTES).unwrap();
        let plan = build_allocation_plan(&artifact, 8).unwrap();
        assert_eq!(estimated_source_bytes(&artifact, &plan).unwrap(), 1_078_272);
    }
}
