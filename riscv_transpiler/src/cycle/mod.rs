use std::hash::Hash;

// These machine profiles remain here because the rest of the workspace still
// keys decoder selection, setup generation, and recursion layout on them.
//
// The old simulator state machines are gone, but the marker types still define
// the supported ISA surface for the active proving path.
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

// The active witnesses still use the architectural register count through the
// historical `cycle::state::NUM_REGISTERS` path, so we preserve that path as a
// tiny compatibility shim instead of touching unrelated consumers.
pub mod state {
    pub const NUM_REGISTERS: usize = 32;
}

pub use state::NUM_REGISTERS;

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
    const ALLOWED_DELEGATION_CSRS: &'static [u32] = &[
        common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
        common_constants::delegation_types::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
        common_constants::delegation_types::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER,
    ];
}

#[derive(
    Clone, Copy, Debug, Hash, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize,
)]
pub struct IMStandardIsaConfigWithUnsignedMulDiv;

impl MachineConfig for IMStandardIsaConfigWithUnsignedMulDiv {
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
    const ALLOWED_DELEGATION_CSRS: &'static [u32] = &[
        common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
        common_constants::delegation_types::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
        common_constants::delegation_types::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER,
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
        common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
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
        common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
        common_constants::delegation_types::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
        common_constants::delegation_types::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER,
    ];
}
