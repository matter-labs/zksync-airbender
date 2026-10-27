//! Unified *extended* machine: one GKR circuit for every opcode of the unified reduced
//! machine plus unsigned `MUL`/`MULHU` and sub-word loads/stores (`LH`/`LHU`/`LB`/`LBU`/
//! `SH`/`SB`). No division. Memory is ROM-free: every load/store is a RAM access of the
//! word-aligned cell (programs never read `.text`; `.rodata`/`.data` are initialised by
//! other means), so none of the ROM lookup tables of the standalone memory circuits exist.
//!
//! Families 1–3 are the reduced machine's bodies, reused verbatim together with its shared
//! scratch-pool optimisation; the two new families fit entirely into that pool (see
//! `circuit.rs`), so the circuit commits the same scratch width and only the flag columns
//! differ: 23 flags against the reduced machine's 19, and no ROM-gate column.
use super::*;

mod circuit;
mod decoder;
mod mem_subword;
mod mul;

pub use self::circuit::{
    build_unified_extended_artifact, build_unified_extended_artifact_core,
    unified_extended_machine_circuit_with_preprocessed_bytecode_for_gkr,
    unified_extended_machine_circuit_with_preprocessed_bytecode_for_gkr_core,
    unified_extended_machine_table_addition_fn, unified_extended_machine_table_driver_fn,
    unified_extended_register_all_tables, EXTENDED_MEMORY_NUM_FLAGS, EXTENDED_MUL_NUM_FLAGS,
    FAMILY_1_FLAG_OFFSET as EXTENDED_FAMILY_1_FLAG_OFFSET,
    FAMILY_2_FLAG_OFFSET as EXTENDED_FAMILY_2_FLAG_OFFSET,
    FAMILY_3_FLAG_OFFSET as EXTENDED_FAMILY_3_FLAG_OFFSET, MEM_FLAG_OFFSET, MEM_LOAD_BIT,
    MEM_LOAD_SUBWORD_BIT, MEM_STORE_BIT, MEM_STORE_SUBWORD_BIT, MULHU_BIT, MUL_BIT,
    MUL_FLAG_OFFSET, UNIFIED_EXTENDED_MACHINE_NUM_FLAGS,
};
pub use self::decoder::{
    UnifiedExtendedMachineDecoder, UnifiedExtendedMachineFamilyCircuitMask,
    EXTENDED_AUX_FLAGS_MASK, EXTENDED_RD_IS_ZERO_BIT, MEM_FUNCT3_BYTE_BIT, MEM_FUNCT3_SEXT_BIT,
};
