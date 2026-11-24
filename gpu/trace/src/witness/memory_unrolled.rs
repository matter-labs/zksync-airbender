use crate::witness::option::u32::Option;
use crate::witness::ram_access::{RamAuxComparisonSet, RamQuery};
use crate::witness::Address;

use crate::upstream::{
    GKRAuxLayoutData, GKRMachineState, GKRMemoryLayout, NUM_TIMESTAMP_COLUMNS_FOR_RAM,
    REGISTER_SIZE,
};
use std::ops::Deref;
#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct MachineState {
    pub pc: [u32; REGISTER_SIZE],
    pub timestamp: [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
}

impl From<GKRMachineState> for MachineState {
    fn from(value: GKRMachineState) -> Self {
        Self {
            pc: value.pc.map(|x| x as u32),
            timestamp: value.timestamp.map(|x| x as u32),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct MachineStatePermutationDescription {
    pub execute: u32,
    pub initial_state: MachineState,
    pub final_state: MachineState,
}

impl From<crate::upstream::CSMachineStatePermutationDescription>
    for MachineStatePermutationDescription
{
    fn from(value: crate::upstream::CSMachineStatePermutationDescription) -> Self {
        Self {
            execute: value.execute as u32,
            initial_state: value.initial_state.into(),
            final_state: value.final_state.into(),
        }
    }
}

const MAX_CIRCUIT_FAMILY_MASK_BITS: usize = 32;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct DecoderPlacementDescription {
    pub rs1_index: u32,
    pub rs2_index: Address,
    pub rd_index: Address,
    pub circuit_family_mask_bits_count: u32,
    pub circuit_family_mask_bits: [Address; MAX_CIRCUIT_FAMILY_MASK_BITS],
    pub decoder_witness_is_in_memory: bool,
    pub imm: [u32; REGISTER_SIZE],
    pub funct3: Option<u32>,
}

impl From<crate::upstream::CSDecoderPlacementDescription> for DecoderPlacementDescription {
    fn from(value: crate::upstream::CSDecoderPlacementDescription) -> Self {
        let rs1_index = value.rs1_index as u32;
        let rs2_index = value.rs2_index.into();
        let rd_index = value.rd_index.into();
        let circuit_family_mask_bits_len = value.circuit_family_mask_bits.len();
        assert!(circuit_family_mask_bits_len <= MAX_CIRCUIT_FAMILY_MASK_BITS);
        let circuit_family_mask_bits_count = circuit_family_mask_bits_len as u32;
        let mut circuit_family_mask_bits = [Address::default(); MAX_CIRCUIT_FAMILY_MASK_BITS];
        for (&src, dst) in value
            .circuit_family_mask_bits
            .iter()
            .zip(circuit_family_mask_bits.iter_mut())
        {
            *dst = src.into();
        }
        let decoder_witness_is_in_memory = value.decoder_witness_is_in_memory;
        let imm = value.imm.map(|x| x as u32);
        let funct3 = value.funct3.map(|x| x as u32).into();
        Self {
            rs1_index,
            rs2_index,
            rd_index,
            circuit_family_mask_bits_count,
            circuit_family_mask_bits,
            decoder_witness_is_in_memory,
            imm,
            funct3,
        }
    }
}

pub(crate) const MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT: usize = 4;
pub(crate) const MAX_INITS_AND_TEARDOWNS_SETS_COUNT: usize = 16;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct UnrolledMemoryLayout {
    pub shuffle_ram_access_sets_count: u32,
    pub shuffle_ram_access_sets: [RamQuery; MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT],
    pub machine_state: MachineStatePermutationDescription,
    pub decoder_input: DecoderPlacementDescription,
    pub decoder_lookup_offset: u32,
}

impl UnrolledMemoryLayout {
    pub(crate) fn from_parts(value: &GKRMemoryLayout, decoder_lookup_offset: u32) -> Self {
        let (shuffle_ram_access_sets_count, shuffle_ram_access_sets) = {
            let ram_access_sets = &value.ram_access_sets;
            let len = ram_access_sets.len();
            assert!(len <= MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT);
            let count = len as u32;
            let mut sets = [RamQuery::default(); MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
            for (&src, dst) in ram_access_sets.iter().zip(sets.iter_mut()) {
                *dst = src.into();
            }
            (count, sets)
        };
        let machine_state = value
            .machine_state
            .expect(
                "GKR memory layout must include machine_state for unrolled memory witness teardown",
            )
            .into();
        let decoder_input = value
            .decoder_input
            .clone()
            .expect(
                "GKR memory layout must include decoder_input for unrolled memory witness teardown",
            )
            .into();
        Self {
            shuffle_ram_access_sets_count,
            shuffle_ram_access_sets,
            machine_state,
            decoder_input,
            decoder_lookup_offset,
        }
    }
}

impl From<&GKRMemoryLayout> for UnrolledMemoryLayout {
    fn from(value: &GKRMemoryLayout) -> Self {
        Self::from_parts(value, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::upstream::GKRAddress;

    fn dummy_machine_state() -> cs::definitions::gkr::MachineStatePermutationDescription {
        cs::definitions::gkr::MachineStatePermutationDescription {
            execute: 1,
            initial_state: cs::definitions::gkr::GKRMachineState {
                pc: [0; REGISTER_SIZE],
                timestamp: [0; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
            },
            final_state: cs::definitions::gkr::GKRMachineState {
                pc: [0; REGISTER_SIZE],
                timestamp: [0; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
            },
        }
    }

    fn dummy_decoder_input() -> cs::definitions::gkr::DecoderPlacementDescription {
        cs::definitions::gkr::DecoderPlacementDescription {
            rs1_index: 0,
            rs2_index: GKRAddress::BaseLayerMemory(0),
            rd_index: GKRAddress::BaseLayerMemory(0),
            circuit_family_mask_bits: Box::new([]),
            decoder_witness_is_in_memory: false,
            imm: [0; REGISTER_SIZE],
            funct3: None,
        }
    }

    #[test]
    #[should_panic(
        expected = "GKR memory layout must include machine_state for unrolled memory witness teardown"
    )]
    fn missing_machine_state_has_explicit_panic_message() {
        let layout = GKRMemoryLayout {
            ram_access_sets: Vec::new(),
            machine_state: None,
            delegation_state: None,
            decoder_input: Some(dummy_decoder_input()),
            indirect_access_variable_offsets: Vec::new(),
            teardown_sets: Vec::new(),
            total_width: 0,
            inits_and_teardowns_word_bits: None,
        };

        let _ = UnrolledMemoryLayout::from_parts(&layout, 0);
    }

    #[test]
    #[should_panic(
        expected = "GKR memory layout must include decoder_input for unrolled memory witness teardown"
    )]
    fn missing_decoder_input_has_explicit_panic_message() {
        let layout = GKRMemoryLayout {
            ram_access_sets: Vec::new(),
            machine_state: Some(dummy_machine_state()),
            delegation_state: None,
            decoder_input: None,
            indirect_access_variable_offsets: Vec::new(),
            teardown_sets: Vec::new(),
            total_width: 0,
            inits_and_teardowns_word_bits: None,
        };

        let _ = UnrolledMemoryLayout::from_parts(&layout, 0);
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct AuxLayoutData {
    pub shuffle_ram_timestamp_comparison_aux_vars:
        [RamAuxComparisonSet; MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT],
}

impl From<&GKRAuxLayoutData> for AuxLayoutData {
    fn from(value: &GKRAuxLayoutData) -> Self {
        let vars = &value.shuffle_ram_timestamp_comparison_aux_vars;
        let len = vars.len();
        assert!(len <= MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT);
        let mut shuffle_ram_timestamp_comparison_aux_vars =
            [RamAuxComparisonSet::default(); MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
        assert!(value.relative_timestamp_groups.is_empty());
        for (&src, dst) in vars
            .iter()
            .zip(shuffle_ram_timestamp_comparison_aux_vars.iter_mut())
        {
            *dst = src
                .expect("unrolled circuits compare every RAM access")
                .into();
        }
        Self {
            shuffle_ram_timestamp_comparison_aux_vars,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct InitsAndTeardownsLayout {
    pub teardown_timestamps_columns: [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub teardown_values_columns: [u32; 2],
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct InitsAndTeardownsLayouts {
    pub count: u32,
    pub layouts: [InitsAndTeardownsLayout; MAX_INITS_AND_TEARDOWNS_SETS_COUNT],
}

impl<
        T: Deref<
            Target = [(
                [crate::upstream::GKRAddress; 2],
                [crate::upstream::GKRAddress; 2],
            )],
        >,
    > From<&T> for InitsAndTeardownsLayouts
{
    fn from(value: &T) -> Self {
        let len = value.len();
        assert!(len <= MAX_INITS_AND_TEARDOWNS_SETS_COUNT);
        let count = len as u32;
        let mut layouts = [InitsAndTeardownsLayout::default(); MAX_INITS_AND_TEARDOWNS_SETS_COUNT];
        for (&(timestamps, values), dst) in value.iter().zip(layouts.iter_mut()) {
            dst.teardown_timestamps_columns = timestamps.map(|address| match address {
                crate::upstream::GKRAddress::BaseLayerMemory(offset) => offset as u32,
                _ => panic!(
                    "init/teardown memory layout expects base-layer memory timestamp columns"
                ),
            });
            dst.teardown_values_columns = values.map(|address| match address {
                crate::upstream::GKRAddress::BaseLayerMemory(offset) => offset as u32,
                _ => panic!("init/teardown memory layout expects base-layer memory value columns"),
            });
        }
        Self { count, layouts }
    }
}

// Keep the field-specific symbols and public launcher names at their instantiations.
macro_rules! define_inits_and_teardowns {
    ($field:ty, $name:ident, $kernel:ident) => {
        era_cudart::cuda_kernel!(GenerateInitsAndTeardowns,
            $kernel(
                init_and_teardown_layouts: $crate::witness::memory_unrolled::InitsAndTeardownsLayouts,
                trace: $crate::witness::trace_unrolled::InitsAndTeardownsTraceRaw,
                memory: gpu_core::primitives::device_structures::MutPtrAndStride<$field>,
                page_size_log2: u32,
                pages_per_set_log2: u32,
            )
        );
        pub fn $name(
            layout: &$crate::upstream::GKRMemoryLayout,
            trace_len_log2: u32,
            page_size_log2: u32,
            trace_device: &$crate::witness::trace_unrolled::InitsAndTeardownsTraceDevice,
            memory: &mut impl gpu_core::primitives::device_structures::DeviceMatrixMutImpl<$field>,
            stream: &era_cudart::stream::CudaStream,
        ) -> era_cudart::result::CudaResult<()> {
            use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
            use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
            use gpu_ops::simple::set_to_zero;

            assert_eq!(memory.cols(), layout.total_width);
            assert_eq!(memory.stride(), 1usize << trace_len_log2);
            assert!(page_size_log2 < trace_len_log2);
            set_to_zero(memory.slice_mut(), stream)?;
            let num_pages = trace_device.page_indices.len();
            if num_pages == 0 {
                return Ok(());
            }
            let total_words = num_pages
                .checked_shl(page_size_log2)
                .expect("inits-and-teardowns total word count overflows usize");
            assert!(total_words <= u32::MAX as usize);
            let pages_per_set_log2 = trace_len_log2 - page_size_log2;
            let layouts = (&layout.teardown_sets).into();
            let trace_raw: $crate::witness::trace_unrolled::InitsAndTeardownsTraceRaw = trace_device.into();
            let memory = memory.as_mut_ptr_and_stride();
            let (grid_dim, block_dim) =
                get_grid_block_dims_for_threads_count(WARP_SIZE * 8, total_words as u32);
            let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
            let args = GenerateInitsAndTeardownsArguments::new(
                layouts,
                trace_raw,
                memory,
                page_size_log2,
                pages_per_set_log2,
            );
            GenerateInitsAndTeardownsFunction::default()
                .launch(&config, &args)
        }
    };
}
pub(crate) use define_inits_and_teardowns;
