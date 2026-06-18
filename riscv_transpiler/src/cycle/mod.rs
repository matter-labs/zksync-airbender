use std::hash::Hash;

// Machine profiles tie together the ISA features used by preprocessing, setup
// generation, and recursion layout.
pub trait MachineConfig:
    'static
    + Clone
    + Copy
    + Send
    + Sync
    + Hash
    + std::fmt::Debug
    + PartialEq
    + Eq
    + Default
    + serde::Serialize
    + serde::de::DeserializeOwned
{
    type DecodingOptions: DecodingOptions;
    const ALLOWED_DELEGATION_CSRS: &'static [u32];
}

mod markers;

pub mod state {
    pub const NUM_REGISTERS: usize = 32;
}

use crate::ir::{
    DecodingOptions, FullMachineDecoderConfig, FullUnsignedMachineDecoderConfig,
    ReducedMachineDecoderConfig,
};

pub use self::markers::{CycleMarker, CycleMarkerHooks, Mark};
pub use state::NUM_REGISTERS;

#[derive(
    Clone, Copy, Debug, Hash, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize,
)]
pub struct IMStandardIsaConfig;

impl MachineConfig for IMStandardIsaConfig {
    type DecodingOptions = FullMachineDecoderConfig;
    const ALLOWED_DELEGATION_CSRS: &'static [u32] = &[
        common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
        common_constants::delegation_types::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
        common_constants::delegation_types::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER,
    ];
}

#[derive(
    Clone, Copy, Debug, Hash, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize,
)]
pub struct IMStandardIsaConfigUnsignedMulDivOnly;

impl MachineConfig for IMStandardIsaConfigUnsignedMulDivOnly {
    type DecodingOptions = FullUnsignedMachineDecoderConfig;
    const ALLOWED_DELEGATION_CSRS: &'static [u32] = &[
        common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
        common_constants::delegation_types::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
        common_constants::delegation_types::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER,
    ];
}

#[derive(
    Clone, Copy, Debug, Hash, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize,
)]
pub struct ReducedMachineWithDelegation;

impl MachineConfig for ReducedMachineWithDelegation {
    type DecodingOptions = ReducedMachineDecoderConfig;
    const ALLOWED_DELEGATION_CSRS: &'static [u32] = &[
        common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
    ];
}

#[derive(
    Clone, Copy, Debug, Hash, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize,
)]
pub struct ReducedMachineWithoutDelegation;

impl MachineConfig for ReducedMachineWithoutDelegation {
    type DecodingOptions = ReducedMachineDecoderConfig;
    const ALLOWED_DELEGATION_CSRS: &'static [u32] = &[];
}
