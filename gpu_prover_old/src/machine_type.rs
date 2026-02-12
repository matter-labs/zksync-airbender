use riscv_transpiler::ir::{
    FullMachineDecoderConfig, FullUnsignedMachineDecoderConfig, ReducedMachineDecoderConfig,
};
use std::any::{type_name, TypeId};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum MachineType {
    Full,
    FullUnsigned,
    Reduced,
}

impl MachineType {
    pub fn from_machine_config<C: prover::risc_v_simulator::cycle::MachineConfig>() -> Self {
        if setups::is_default_machine_configuration::<C>() {
            MachineType::Full
        } else if setups::is_machine_without_signed_mul_div_configuration::<C>() {
            MachineType::FullUnsigned
        } else if setups::is_reduced_machine_configuration::<C>() {
            MachineType::Reduced
        } else {
            panic!("unknown machine configuration {:?}", type_name::<C>());
        }
    }

    pub fn from_decoder_config<D: riscv_transpiler::ir::DecodingOptions>() -> Self {
        let id = TypeId::of::<D>();
        if id == TypeId::of::<FullMachineDecoderConfig>() {
            MachineType::Full
        } else if id == TypeId::of::<FullUnsignedMachineDecoderConfig>() {
            MachineType::FullUnsigned
        } else if id == TypeId::of::<ReducedMachineDecoderConfig>() {
            MachineType::Reduced
        } else {
            panic!("unknown decoder configuration {:?}", type_name::<D>());
        }
    }
}
