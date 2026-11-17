//! SKETCH: zero-knowledge masking of the unified reduced machine trace by executed opcodes.
//!
//! Instead of putting random values on unused trace rows, the guest spends cycles on a fixed
//! sequence of opcodes whose operands come from the non-determinism oracle. The sequence is
//! straight-line (the only taken branches are the public loop counters), so the PC, decoder and
//! opcode-flag columns of these rows are a function of the ROM and reveal nothing.
//!
//! The sequence runs once, as a part of [`crate::finish_execution_recursion_extended`], after the
//! outputs are in registers and nothing reads memory any more. It has two parts:
//! - [`REGISTER_GROUPS`] repetitions of 2 ADD/SUB, 2 comparisons and 4 shifts over 4 oracle
//!   words. ADD/SUB fill the two carry bits, SLTU/BLT fill the two comparison borrow bits,
//!   SLL/SRL with a random value and a random amount fill the shared scratch variables (shift
//!   amount, contribution bytes, operand byte splits). Every row also fills the register value
//!   limbs and the unconditional `rs1 * rs2` product column.
//! - [`MEMORY_WRITES`] stores of an oracle word to an oracle address, that put random final
//!   values and timestamps into the inline inits/teardowns columns.
//!
//! There is no plan negotiated with the oracle: the counts are constants sized for a single
//! chunk proven with the ethproofs soundcalc WHIR schedule (179 base-round queries, the figures
//! of the 2^23 unified reduced machine proof), where every secret column needs about 11.4k bits
//! of fresh randomness. They are estimates from reading the circuit, not validated on a trace.
//!
//! Oracle protocol: the sequence is one query of the memory-based oracle protocol (the one that
//! `riscv_transpiler::oracle::QueryDispatcher` serves). The guest writes [`MASKING_QUERY_ID`]
//! and then the input word, which is [`ORACLE_WORDS`], and reads exactly that many words: 4 per
//! register group, then an (address, value) pair per store. The responder is
//! `riscv_transpiler::oracle::zk_masking::MaskingResponder`; only the sequence and its
//! parameters live here, so this crate stays `no_std` without features.
//!
//! The store addresses are NOT checked by the guest. It is the oracle's job to answer with
//! word-aligned addresses outside of ROM and inside the memory covered by inits/teardowns; a
//! wrong address makes the execution unprovable and nothing else, because the program is over.
//!
//! Not covered: the read-timestamp and address columns of a program with secret-dependent
//! memory addresses, the ROM-read gate column, the control-flow columns of a program with
//! secret-dependent control flow, and the Proth120 two-field layout.

/// ID of the masking query, in the system subspace of the oracle protocol (`0x4000_0000` is the
/// disconnect query). No other query of the program may use it.
pub const MASKING_QUERY_ID: u32 = 0x4000_0001;

/// 11.4k ADD/SUB rows, 11.4k comparison rows and 22.8k shift rows: a column that gains one
/// random bit per row sets the count.
pub const REGISTER_GROUPS: u32 = 5_700;
pub const ORACLE_WORDS_PER_REGISTER_GROUP: u32 = 4;
/// 4 oracle reads, 8 operations, 2 rows of loop control.
pub const CYCLES_PER_REGISTER_GROUP: u32 = 14;

/// The inits/teardowns grand product ends with 16 explicit values per polynomial, one per
/// continuous sixteenth of the rows, and every such block needs its own randomness.
pub const INITS_AND_TEARDOWNS_ROW_BLOCKS: u32 = 16;
/// Inline inits/teardowns sets per row. Set `s` at row `r` holds the word at byte address
/// `4 * (s * trace_len + r)`.
pub const INITS_AND_TEARDOWNS_SETS: u32 = 2;
/// Continuous chunks of the address space that the stores are spread over.
pub const ADDRESS_CHUNKS: u32 = INITS_AND_TEARDOWNS_ROW_BLOCKS * INITS_AND_TEARDOWNS_SETS;
/// 64 stores of a 32-bit word per chunk, far above the 240 bits a block needs.
pub const MEMORY_WRITES_PER_ADDRESS_CHUNK: u32 = 64;
/// 1024 stores per set: about 16k bits in each 16-bit teardown value column.
pub const MEMORY_WRITES: u32 = ADDRESS_CHUNKS * MEMORY_WRITES_PER_ADDRESS_CHUNK;
/// Address, then value.
pub const ORACLE_WORDS_PER_MEMORY_WRITE: u32 = 2;
/// 2 oracle reads, the store, 2 rows of loop control.
pub const CYCLES_PER_MEMORY_WRITE: u32 = 5;

/// Words read after the query; also its input word, that the responder checks.
pub const ORACLE_WORDS: u32 = REGISTER_GROUPS * ORACLE_WORDS_PER_REGISTER_GROUP
    + MEMORY_WRITES * ORACLE_WORDS_PER_MEMORY_WRITE;

/// Cycles of the whole sequence: the two writes of the query with their operand loads (6), two
/// loop counter loads of two instructions each, two loops.
pub const MASKING_CYCLES: u32 = 6
    + 2
    + 2
    + REGISTER_GROUPS * CYCLES_PER_REGISTER_GROUP
    + MEMORY_WRITES * CYCLES_PER_MEMORY_WRITE;

/// The masking sequence as an `asm!` template. It uses only `t0`, `t1`, `t2` and `t4`
/// (x5, x6, x7, x29), so x10-x28 keep their values, and the local labels 2, 3 and 4.
///
/// The caller provides the `const` operands `masking_query_id`, `masking_oracle_words`,
/// `masking_register_groups` and `masking_memory_writes`, and has to treat the four registers
/// as clobbered. In every second
/// comparison the branch targets the next instruction: taken or not, the next PC is the same,
/// so it randomizes the branch-outcome column at no cost in control flow.
#[cfg(target_arch = "riscv32")]
macro_rules! masking_sequence_asm {
    () => {
        concat!(
            "li    t0, {masking_query_id}\n",
            "csrrw x0, 0x7c0, t0\n",
            "li    t0, {masking_oracle_words}\n",
            "csrrw x0, 0x7c0, t0\n",
            "li    t4, {masking_register_groups}\n",
            "2:\n",
            "csrrw t0, 0x7c0, x0\n",
            "csrrw t1, 0x7c0, x0\n",
            "add   t2, t0, t1\n",
            "sltu  t2, t1, t0\n",
            "sll   t2, t0, t1\n",
            "srl   t2, t1, t0\n",
            "csrrw t0, 0x7c0, x0\n",
            "csrrw t1, 0x7c0, x0\n",
            "sub   t2, t0, t1\n",
            "blt   t0, t1, 3f\n",
            "3:\n",
            "srl   t2, t0, t1\n",
            "sll   t2, t1, t0\n",
            "addi  t4, t4, -1\n",
            "bnez  t4, 2b\n",
            "li    t4, {masking_memory_writes}\n",
            "4:\n",
            "csrrw t0, 0x7c0, x0\n",
            "csrrw t1, 0x7c0, x0\n",
            "sw    t1, 0(t0)\n",
            "addi  t4, t4, -1\n",
            "bnez  t4, 4b\n",
        )
    };
}
#[cfg(target_arch = "riscv32")]
pub(crate) use masking_sequence_asm;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sequence_cost() {
        assert_eq!(ORACLE_WORDS, 5_700 * 4 + 2_048 * 2);
        assert_eq!(MASKING_CYCLES, 10 + 5_700 * 14 + 2_048 * 5);
        // a system query of the oracle protocol, next to the disconnect query
        assert_eq!(MASKING_QUERY_ID, 0x4000_0001);
    }
}
