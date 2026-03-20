use riscv_transpiler::cycle::{
    IMStandardIsaConfig, IMStandardIsaConfigWithUnsignedMulDiv,
    IWithoutByteAccessIsaConfigWithDelegation,
};
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
    pub fn from_machine_config<C: riscv_transpiler::cycle::MachineConfig>() -> Self {
        let id = TypeId::of::<C>();
        if id == TypeId::of::<IMStandardIsaConfig>() {
            MachineType::Full
        } else if id == TypeId::of::<IMStandardIsaConfigWithUnsignedMulDiv>() {
            MachineType::FullUnsigned
        } else if id == TypeId::of::<IWithoutByteAccessIsaConfigWithDelegation>() {
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
