pub(crate) mod decode;
pub(crate) mod encoding_types;
pub(crate) mod instructions;
pub mod simple_instruction_set;

use self::decode::*;
use self::encoding_types::*;
use self::instructions::*;

pub trait DecodingOptions: 'static + Sized {
    const SUPPORT_SUBWORD_MEM_ACCESS: bool;
    const SUPPORT_MUL_DIV: bool;
    const SUPPORT_SIGNED_MUL_DIV: bool;
    const SUPPORT_MOP: bool;
}

pub struct FullMachineDecoderConfig;

impl DecodingOptions for FullMachineDecoderConfig {
    const SUPPORT_MOP: bool = false;
    const SUPPORT_MUL_DIV: bool = true;
    const SUPPORT_SIGNED_MUL_DIV: bool = true;
    const SUPPORT_SUBWORD_MEM_ACCESS: bool = true;
}

pub struct FullUnsignedMachineDecoderConfig;

impl DecodingOptions for FullUnsignedMachineDecoderConfig {
    const SUPPORT_MOP: bool = true;
    const SUPPORT_MUL_DIV: bool = true;
    const SUPPORT_SIGNED_MUL_DIV: bool = false;
    const SUPPORT_SUBWORD_MEM_ACCESS: bool = true;
}

pub struct ReducedMachineDecoderConfig;

impl DecodingOptions for ReducedMachineDecoderConfig {
    const SUPPORT_MOP: bool = true;
    const SUPPORT_MUL_DIV: bool = false;
    const SUPPORT_SIGNED_MUL_DIV: bool = false;
    const SUPPORT_SUBWORD_MEM_ACCESS: bool = false;
}

// Special config to allow sending text over UART in recursive verifiers
pub struct DebugReducedMachineDecoderConfig;

impl DecodingOptions for DebugReducedMachineDecoderConfig {
    const SUPPORT_MOP: bool = true;
    const SUPPORT_MUL_DIV: bool = false;
    const SUPPORT_SIGNED_MUL_DIV: bool = false;
    const SUPPORT_SUBWORD_MEM_ACCESS: bool = true;
}
