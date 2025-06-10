use std::hash::Hash;

mod decoder_utils;
pub mod opcode_formats;
pub mod state;
pub mod state_new;
pub mod status_registers;
mod utils;

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
    const SUPPORT_MUL: bool;
    const SUPPORT_DIV: bool;
    const SUPPORT_SIGNED_MUL: bool;
    const SUPPORT_SIGNED_DIV: bool;
    const SUPPORT_SIGNED_LOAD: bool;
    const SUPPORT_LOAD_LESS_THAN_WORD: bool;
    const SUPPORT_SRA: bool;
    const SUPPORT_ROT: bool;
    const SUPPORT_MOPS: bool;
    const HANDLE_EXCEPTIONS: bool;
    const SUPPORT_STANDARD_CSRS: bool;
    const SUPPORT_ONLY_CSRRW: bool;
    const ALLOWED_DELEGATION_CSRS: &'static [u32];
}

#[derive(
    Clone, Copy, Debug, Hash, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize,
)]
pub struct IMStandardIsaConfig;

impl MachineConfig for IMStandardIsaConfig {
    const SUPPORT_MUL: bool = true;
    const SUPPORT_DIV: bool = true;
    const SUPPORT_SIGNED_MUL: bool = true;
    const SUPPORT_SIGNED_DIV: bool = true;
    const SUPPORT_SIGNED_LOAD: bool = true;
    const SUPPORT_LOAD_LESS_THAN_WORD: bool = true;
    const SUPPORT_SRA: bool = true;
    const SUPPORT_ROT: bool = false;
    const SUPPORT_MOPS: bool = false;
    const HANDLE_EXCEPTIONS: bool = false;
    const SUPPORT_STANDARD_CSRS: bool = false;
    const SUPPORT_ONLY_CSRRW: bool = true;
    #[cfg(not(feature = "delegation"))]
    const ALLOWED_DELEGATION_CSRS: &'static [u32] = &[];
    #[cfg(feature = "delegation")]
    const ALLOWED_DELEGATION_CSRS: &'static [u32] =
        &[
            crate::delegations::blake2_round_function_with_compression_mode::BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID,
            crate::delegations::u256_ops_with_control::U256_OPS_WITH_CONTROL_ACCESS_ID,
        ];
}

#[derive(
    Clone, Copy, Debug, Hash, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize,
)]
pub struct IMWithoutSignedMulDivIsaConfig;

impl MachineConfig for IMWithoutSignedMulDivIsaConfig {
    const SUPPORT_MUL: bool = true;
    const SUPPORT_DIV: bool = true;
    const SUPPORT_SIGNED_MUL: bool = false;
    const SUPPORT_SIGNED_DIV: bool = false;
    const SUPPORT_SIGNED_LOAD: bool = true;
    const SUPPORT_LOAD_LESS_THAN_WORD: bool = true;
    const SUPPORT_SRA: bool = true;
    const SUPPORT_ROT: bool = false;
    const SUPPORT_MOPS: bool = false;
    const HANDLE_EXCEPTIONS: bool = false;
    const SUPPORT_STANDARD_CSRS: bool = false;
    const SUPPORT_ONLY_CSRRW: bool = true;
    #[cfg(not(feature = "delegation"))]
    const ALLOWED_DELEGATION_CSRS: &'static [u32] = &[];
    #[cfg(feature = "delegation")]
    const ALLOWED_DELEGATION_CSRS: &'static [u32] =
        &[
            crate::delegations::blake2_round_function_with_compression_mode::BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID,
            crate::delegations::u256_ops_with_control::U256_OPS_WITH_CONTROL_ACCESS_ID,
        ];
}

#[derive(
    Clone, Copy, Debug, Hash, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize,
)]
pub struct IWithoutByteAccessIsaConfigWithDelegation;

impl MachineConfig for IWithoutByteAccessIsaConfigWithDelegation {
    const SUPPORT_MUL: bool = false;
    const SUPPORT_DIV: bool = false;
    const SUPPORT_SIGNED_MUL: bool = false;
    const SUPPORT_SIGNED_DIV: bool = false;
    const SUPPORT_SIGNED_LOAD: bool = false;
    const SUPPORT_LOAD_LESS_THAN_WORD: bool = false;
    const SUPPORT_SRA: bool = true;
    const SUPPORT_ROT: bool = false;
    const SUPPORT_MOPS: bool = true;
    const HANDLE_EXCEPTIONS: bool = false;
    const SUPPORT_STANDARD_CSRS: bool = false;
    const SUPPORT_ONLY_CSRRW: bool = true;
    #[cfg(not(feature = "delegation"))]
    const ALLOWED_DELEGATION_CSRS: &'static [u32] = &[];
    #[cfg(feature = "delegation")]
    const ALLOWED_DELEGATION_CSRS: &'static [u32] = &[
        crate::delegations::blake2_round_function_with_compression_mode::BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID,
    ];
}

#[derive(
    Clone, Copy, Debug, Hash, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize,
)]
pub struct IWithoutByteAccessIsaConfig;

impl MachineConfig for IWithoutByteAccessIsaConfig {
    const SUPPORT_MUL: bool = false;
    const SUPPORT_DIV: bool = false;
    const SUPPORT_SIGNED_MUL: bool = false;
    const SUPPORT_SIGNED_DIV: bool = false;
    const SUPPORT_SIGNED_LOAD: bool = false;
    const SUPPORT_LOAD_LESS_THAN_WORD: bool = false;
    const SUPPORT_SRA: bool = true;
    const SUPPORT_ROT: bool = false;
    const SUPPORT_MOPS: bool = true;
    const HANDLE_EXCEPTIONS: bool = false;
    const SUPPORT_STANDARD_CSRS: bool = false;
    const SUPPORT_ONLY_CSRRW: bool = true;
    const ALLOWED_DELEGATION_CSRS: &'static [u32] = &[];
}

#[derive(
    Clone, Copy, Debug, Hash, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize,
)]
pub struct IMIsaConfigWithAllDelegations;

impl MachineConfig for IMIsaConfigWithAllDelegations {
    const SUPPORT_MUL: bool = true;
    const SUPPORT_DIV: bool = true;
    const SUPPORT_SIGNED_MUL: bool = true;
    const SUPPORT_SIGNED_DIV: bool = true;
    const SUPPORT_SIGNED_LOAD: bool = true;
    const SUPPORT_LOAD_LESS_THAN_WORD: bool = true;
    const SUPPORT_SRA: bool = true;
    const SUPPORT_ROT: bool = false;
    const SUPPORT_MOPS: bool = true;
    const HANDLE_EXCEPTIONS: bool = false;
    const SUPPORT_STANDARD_CSRS: bool = false;
    const SUPPORT_ONLY_CSRRW: bool = true;
    #[cfg(not(feature = "delegation"))]
    const ALLOWED_DELEGATION_CSRS: &'static [u32] = &[];
    #[cfg(feature = "delegation")]
    const ALLOWED_DELEGATION_CSRS: &'static [u32] = &[
        crate::delegations::blake2_round_function_with_compression_mode::BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID,
        crate::delegations::u256_ops_with_control::U256_OPS_WITH_CONTROL_ACCESS_ID,
    ];
}
