//! SKETCH: zero-knowledge masking of the unified reduced machine trace by executed opcodes.
//!
//! Instead of putting random values on unused trace rows, the guest spends cycles on a fixed
//! loop of opcodes whose operands, memory addresses and one branch decision per iteration come
//! from the non-determinism oracle. It runs once, as a part of
//! [`crate::finish_execution_recursion_extended`], after the outputs are in registers and
//! nothing reads memory any more.
//!
//! One iteration, [`ITERATIONS`] times:
//! - ADD and the comparison of a branch fill the two carry bits (scratch Booleans 0 and 1);
//! - SLL/SRL with a random value and a random amount fill the shared scratch variables (shift
//!   amount, contribution bytes, operand byte splits);
//! - a three-input add (`ZimopTriAdd`, `rd = rd + rs1 + rs2`) fills the second carry bit of each
//!   limb (scratch Booleans 2 and 3), that only this opcode and the jump targets use;
//! - a load and a store at oracle addresses fill the read-timestamp columns of the memory
//!   accesses: the oracle answers with a never touched word or with one of the words that the
//!   loop touched before, each with probability 1/2. The low limb of the read timestamp gets
//!   the random age of a touched word, the high limb is zero for a never touched one. The store
//!   also puts a random final value and timestamp into the inline inits/teardowns columns;
//! - the branch is taken with probability 1/2 and skips one instruction, so the path of the
//!   execution is random. The loop is placed by the assembler across a 64 KiB boundary of the
//!   address space, with the skipped instruction as the last one below it: its row is the only
//!   one of the loop that sets the carry of `pc + 4` into the high PC limb, and the taken
//!   branch is the only one that sets the low carry of the jump target.
//!
//! Every row also fills the register value limbs and the unconditional `rs1 * rs2` product
//! column.
//!
//! An iteration is 14 or 15 rows, so from the first branch on the row of every later
//! instruction depends on the path, and so does every column that is a function of the PC or of
//! the time between two accesses of a register: the branch outcome, the carry of `pc + 4`, the
//! PC limbs, the register indexes and the decoder outputs that differ between the instructions
//! of the loop, the low limb of the register read timestamps. These columns do NOT have a
//! randomness of their own: all of them are functions of the same path, one bit per iteration,
//! which is what the openings of one column consume. So the loop hides the path-dependent
//! columns of a program only one at a time; hiding the control flow as a whole would take as
//! many bits of path per iteration as there are such columns (about 25), from instructions with
//! as many linearly independent decodings, and the first register operand's read timestamp
//! (below) would still not be covered.
//!
//! There is no plan negotiated with the oracle: the counts are constants sized for a single
//! chunk proven with the ethproofs soundcalc WHIR schedule (179 base-round queries, the figures
//! of the 2^23 unified reduced machine proof). Two budgets have to hold:
//! - per column: the base round opens 2 values of a column per query, and the evaluation claim
//!   adds 4, so 362 values of 31 bits, 11.2k bits, and 11.5k with the slack of a 2^-120
//!   statistical distance. The columns that gain one bit per iteration set the count: the
//!   high limbs of the memory read timestamps (the oracle's coin between a never touched and a
//!   touched word) and the path.
//! - in total: the later WHIR rounds open about 2,990 extension field values of the polynomial
//!   that batches all the columns, so over the 45 columns with a randomness of their own and one
//!   path-dependent column the proof shows about 890k bits of linear functions of the trace. An
//!   iteration consumes 3 random words, the path bit among them, and about 38 bits of address
//!   choices, 1.5M bits in total.
//!
//! The figures per column were measured on the witness of the add/sub verifier guest (two runs
//! with independent randomness); the total is a count of bits, not a proof that the opened
//! values are jointly uniform.
//!
//! The sequence is for a program that hashes with the special Blake2s opcodes
//! (`special_opcodes_extension`): there the secrets reach scratch Booleans 2 and 3 through the
//! three-input add, and the sequence masks them with the same opcode. It does not mask the
//! columns of the delegation circuits, so it is not enough for a program that hashes via a
//! delegation.
//!
//! Oracle protocol: the sequence is one query of the memory-based oracle protocol (the one that
//! `riscv_transpiler::oracle::QueryDispatcher` serves). The guest writes [`MASKING_QUERY_ID`]
//! and then the input word, which is [`ORACLE_WORDS`], and reads exactly that many words:
//! [`ORACLE_WORDS_PER_ITERATION`] per iteration, in the order of the loop below. The responder
//! is `riscv_transpiler::oracle::zk_masking::MaskingResponder`; only the sequence and its
//! parameters live here, so this crate stays `no_std` without features.
//!
//! The addresses are NOT checked by the guest. It is the oracle's job to answer with
//! word-aligned addresses outside of ROM and inside the memory covered by inits/teardowns; a
//! wrong address makes the execution unprovable and nothing else, because the program is over.
//!
//! Not covered, because no executed opcode can randomize them:
//! - scratch Boolean 4: the alignment constraints of jumps, loads and stores force it to zero
//!   on every row of a provable execution (the two-field Proth120 layout, that also puts a
//!   quotient bit there, is not handled at all);
//! - the high limb of the read timestamp of the first register operand, and its borrow bit: a
//!   register that an instruction reads was almost always accessed in the same 2^17 cycles;
//! - the borrow bits of the other two read timestamps: they are random only for the accesses
//!   to the words that were last touched before the latest wrap of the timestamp low limb (2^17
//!   cycles). The loop is longer than that, so it has one wrap, but where it falls depends on
//!   the program: in the middle of the loop it gives about 5k bits, at its ends nothing.
//!
//! Not covered by this loop: the ROM-read gate column, and the control flow of a program as a
//! whole, see above.
//!
//! # The loop
//!
//! ```text
//! loop: csrrw t0, 0x7c0, x0      a
//!       csrrw t1, 0x7c0, x0      b
//!       add   t2, t0, t1
//!       sll   t2, t0, t1
//!       srl   t2, t1, t0
//!       mop.rr.4 t0, t0, t0      three-input add: a tripled in place
//!       csrrw t5, 0x7c0, x0      load address
//!       lw    t6, 0(t5)
//!       csrrw t5, 0x7c0, x0      store address
//!       csrrw t2, 0x7c0, x0      v: store value
//!       sw    t2, 0(t5)
//!       blt   t0, t1, skip       64 KiB boundary - 8: taken if 3a < b
//!       mop.rr.4 t2, t2, t2      64 KiB boundary - 4: v tripled in place
//! skip: addi  t4, t4, -1         64 KiB boundary
//!       bnez  t4, loop
//! ```
//!
//! Tripling is a bijection of the 32-bit words, so `3a` is uniform and the branch is a fair
//! coin, independent of `v`. The second carries of a three-input add of a word with itself are
//! a fair bit for the low limb, and are set with probability 1/3 for the high limb (`3x >=
//! 2^33`): 0.92 bits per row, and every such row has its own oracle word, so the rows are
//! independent. With 1.5 such rows per iteration scratch Boolean 3 gains 1.38 bits per iteration.

use common_constants::mops::MOP_TRI_ADD;

/// ID of the masking query, in the system subspace of the oracle protocol (`0x4000_0000` is the
/// disconnect query). No other query of the program may use it.
pub const MASKING_QUERY_ID: u32 = 0x4000_0001;

/// One random bit per iteration in the columns that set the count (the high limbs of the
/// memory read timestamps, the path), against the 11.5k bits that a column needs.
pub const ITERATIONS: u32 = 11_600;
/// Two operands, the load address, the store address, the store value.
pub const ORACLE_WORDS_PER_ITERATION: u32 = 5;
/// The branch skips one of the 15 instructions of an iteration.
pub const MIN_CYCLES_PER_ITERATION: u32 = 14;
pub const MAX_CYCLES_PER_ITERATION: u32 = 15;

/// The inits/teardowns grand product ends with 16 explicit values per polynomial, one per
/// continuous sixteenth of the rows, and every such block needs its own randomness.
pub const INITS_AND_TEARDOWNS_ROW_BLOCKS: u32 = 16;
/// Inline inits/teardowns sets per row. Set `s` at row `r` holds the word at byte address
/// `4 * (s * trace_len + r)`.
pub const INITS_AND_TEARDOWNS_SETS: u32 = 2;
/// Continuous chunks of the address space that the stores to never touched words are spread
/// over.
pub const ADDRESS_CHUNKS: u32 = INITS_AND_TEARDOWNS_ROW_BLOCKS * INITS_AND_TEARDOWNS_SETS;
/// Stores of a 32-bit word to never touched words that every chunk has to get: far above the
/// 240 bits a block needs. The oracle spreads about half of the stores, 180 per chunk.
pub const MIN_FRESH_STORES_PER_ADDRESS_CHUNK: u32 = 64;
/// 1024 stores per set: 16k bits in each 16-bit teardown value column.
pub const MIN_FRESH_STORES: u32 = ADDRESS_CHUNKS * MIN_FRESH_STORES_PER_ADDRESS_CHUNK;

/// Words read after the query; also its input word, that the responder checks.
pub const ORACLE_WORDS: u32 = ITERATIONS * ORACLE_WORDS_PER_ITERATION;

/// Cycles outside of the iterations: the two writes of the query with their operand loads (6),
/// the load of the loop counter (2), the call (2), the jump over the padding, the return.
pub const FIXED_CYCLES: u32 = 6 + 2 + 2 + 1 + 1;
/// The number of cycles of the sequence depends on the path: every branch that is not taken
/// adds one.
pub const MIN_MASKING_CYCLES: u32 = FIXED_CYCLES + ITERATIONS * MIN_CYCLES_PER_ITERATION;
pub const MAX_MASKING_CYCLES: u32 = FIXED_CYCLES + ITERATIONS * MAX_CYCLES_PER_ITERATION;

/// The PC low limb is 16 bits: the loop is placed across a multiple of this.
pub const PC_LOW_LIMB_SPAN_BYTES: u32 = 1 << 16;
/// Instructions of the loop below the boundary; the last of them is the one that the branch
/// skips.
pub const LOOP_INSTRUCTIONS_BELOW_BOUNDARY: u32 = 13;
/// NOPs between the jump at the start of the section, that is aligned to the boundary, and the
/// head of the loop. They are never executed.
pub const PADDING_INSTRUCTIONS: u32 =
    PC_LOW_LIMB_SPAN_BYTES / 4 - 1 - LOOP_INSTRUCTIONS_BELOW_BOUNDARY;

// The loop, in a section of its own that is aligned to 64 KiB: the default `*(.text .text.*)`
// rule of the linker scripts places it, and the linker drops it from a program that does not
// call it. It uses t0, t1, t2, t4, t5, t6 (x5, x6, x7, x29, x30, x31) and returns via ra, so
// x10-x28 keep their values. Zimop is enabled for the section alone, so the crate builds for
// the targets without it too; relaxation is off, so the layout is the one written here. The
// assembler can not check the position of the boundary (a difference of labels is not an
// absolute expression for it): `tests::loop_layout` checks the count of the padding, and the
// test of the built guest in `verifier/tests/transpiler.rs` the addresses.
#[cfg(target_arch = "riscv32")]
core::arch::global_asm!(
    ".pushsection .text.airbender_zk_masking_loop, \"ax\", @progbits",
    ".option push",
    ".option arch, +zimop",
    ".option norelax",
    ".p2align 16",
    ".globl __airbender_zk_masking_loop",
    ".type __airbender_zk_masking_loop, @function",
    "__airbender_zk_masking_loop:",
    "j     2f",
    ".fill {padding}, 4, 0x00000013",
    "2:",
    "csrrw t0, 0x7c0, x0",
    "csrrw t1, 0x7c0, x0",
    "add   t2, t0, t1",
    "sll   t2, t0, t1",
    "srl   t2, t1, t0",
    "mop.rr.{tri_add} t0, t0, t0",
    "csrrw t5, 0x7c0, x0",
    "lw    t6, 0(t5)",
    "csrrw t5, 0x7c0, x0",
    "csrrw t2, 0x7c0, x0",
    "sw    t2, 0(t5)",
    "blt   t0, t1, 3f",
    "mop.rr.{tri_add} t2, t2, t2",
    "3:",
    "addi  t4, t4, -1",
    "bnez  t4, 2b",
    "ret",
    ".size __airbender_zk_masking_loop, . - __airbender_zk_masking_loop",
    ".option pop",
    ".popsection",
    padding = const PADDING_INSTRUCTIONS,
    tri_add = const MOP_TRI_ADD,
);

/// The masking sequence as an `asm!` template: the query, the loop counter and the call of the
/// loop. It clobbers `t0`, `t1`, `t2`, `t4`, `t5`, `t6` and `ra` (x5, x6, x7, x29, x30, x31,
/// x1), so x10-x28 keep their values.
///
/// The caller provides the `const` operands `masking_query_id`, `masking_oracle_words` and
/// `masking_iterations`.
#[cfg(target_arch = "riscv32")]
macro_rules! masking_sequence_asm {
    () => {
        concat!(
            "li    t0, {masking_query_id}\n",
            "csrrw x0, 0x7c0, t0\n",
            "li    t0, {masking_oracle_words}\n",
            "csrrw x0, 0x7c0, t0\n",
            "li    t4, {masking_iterations}\n",
            ".option push\n",
            ".option norelax\n",
            "call  __airbender_zk_masking_loop\n",
            ".option pop\n",
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
        assert_eq!(ORACLE_WORDS, 11_600 * 5);
        assert_eq!(MIN_MASKING_CYCLES, 12 + 11_600 * 14);
        assert_eq!(MAX_MASKING_CYCLES, 12 + 11_600 * 15);
        // the three `li` of the sequence are two instructions each
        for constant in [MASKING_QUERY_ID, ORACLE_WORDS, ITERATIONS] {
            assert!(constant >= 1 << 11);
        }
        // a system query of the oracle protocol, next to the disconnect query
        assert_eq!(MASKING_QUERY_ID, 0x4000_0001);
    }

    #[test]
    fn loop_layout() {
        // the jump, the padding and the instructions below the boundary fill 64 KiB exactly
        assert_eq!(
            (1 + PADDING_INSTRUCTIONS + LOOP_INSTRUCTIONS_BELOW_BOUNDARY) * 4,
            PC_LOW_LIMB_SPAN_BYTES
        );
        assert_eq!(
            MAX_CYCLES_PER_ITERATION,
            LOOP_INSTRUCTIONS_BELOW_BOUNDARY + 2
        );
        // enough stores to never touched words even if the oracle's coin is far off
        assert!(ITERATIONS / 4 >= MIN_FRESH_STORES);
        assert_eq!(MOP_TRI_ADD, 4);
    }
}
