//! Compiler instrumentation / stats (spec §11, §13 compiler-stats gate).
//!
//! `CompileStats` accumulates per-layer counters as the compiler emits instructions.
//! `report` renders a human-readable block per layer, useful for performance
//! diagnosis (§11 "loads/stores, evict/reload/recompute, special-source gathers,
//! max live cells, split counts").

/// Per-layer compilation counters (spec §11).
///
/// - `program_lanes`: total instruction count in the compiled `Program`.
/// - `op_counts`: count of [MOV, ADD, MUL, FMA] instructions respectively.
/// - `inline_reads`: operands resolved directly as source/special (no cell eviction).
///   SP1: not yet counted.
/// - `cell_reads`: `OperandLine::Smem` reads (cell loaded as operand).
///   SP1: not yet counted.
/// - `cell_loads`: cell-evict stores emitted by `lower_operand` (nested subexprs).
///   SP1: not yet counted.
/// - `cell_stores`: all cell-targeting MOVs into `Smem{cell}` — `DstFromAcc` evicts
///   (incl. split evicts) plus `DstFromSrc` source-residency loads (a reused Read
///   loaded once from DRAM into its cell). SP1: not yet counted.
/// - `evicts`: acc evictions during over-cap split (`emit_reduction_group`).
///   SP1: not yet counted.
/// - `reloads`: evict cells folded back in via ADD/MUL during splits.
///   SP1: not yet counted.
/// - `recomputes`: times a child had to be re-lowered into the acc (currently 0).
///   SP1: not yet counted.
/// - `special_gathers`: number of resolved-fold/gather (peek) `Special` descriptors in
///   `ctx.specials` after compilation, EXCLUDING computed `VirtualSetup` strategies (which
///   are resolver-computed, not a real gather — see `SpecialStrategy::VirtualSetup`). NOT
///   the raw `ctx.specials.len()`. REAL in SP1.
/// - `max_live_cells`: high-water mark of simultaneously live smem cells across
///   all roots. REAL in SP1 (from `trace.max_live_cells`).
/// - `split_count`: number of over-cap reduction groups that were split.
///   SP1: not yet counted.
/// - `avg_chunk`: average chunk size across all split groups (0.0 if no splits).
///   SP1: not yet counted.
/// - `dram_reads`: DRAM-read operands. SP1: not yet counted.
/// - `ldc_reads`: Ldc (load cache) operands. SP1: not yet counted.
/// - `special_reads`: resolved-fold `OperandLine::Special{desc}` operand-use count
///   (excludes `VirtualSetup` gathers, which are resolver-computed like a `SpecialLit`).
///   SP1: not yet counted.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct CompileStats {
    pub program_lanes: usize,
    pub op_counts: [usize; 4], // [MOV, ADD, MUL, FMA]
    pub inline_reads: usize,   // SP1: not yet counted
    pub cell_reads: usize,     // SP1: not yet counted
    pub cell_loads: usize,     // SP1: not yet counted
    pub cell_stores: usize,    // SP1: not yet counted
    pub evicts: usize,         // SP1: not yet counted
    pub reloads: usize,        // SP1: not yet counted
    pub recomputes: usize,     // SP1: not yet counted
    pub special_gathers: usize,
    pub max_live_cells: usize,
    pub split_count: usize,   // SP1: not yet counted
    pub avg_chunk: f64,       // SP1: not yet counted
    pub dram_reads: usize,    // SP1: not yet counted
    pub ldc_reads: usize,     // SP1: not yet counted
    pub special_reads: usize, // SP1: not yet counted
    /// Width-weighted DRAM traffic in cells: each real-DRAM read operand
    /// (`OperandLine::LogicalGlobal`, i.e. a Read/Prior backing) contributes its field width
    /// (Ext=4, Base=1). VirtualSetup is a computed `Special` strategy (0 traffic), not a
    /// Global backing — see `compile::tally_operand`. This is the Phase-1 / S3 primary
    /// objective. `dram_reads` above stays the per-operand transaction count
    /// (test-locked diagnostic).
    pub dram_traffic: usize,
}

/// Opcode indices for `op_counts`.
pub const OP_MOV: usize = 0;
pub const OP_ADD: usize = 1;
pub const OP_MUL: usize = 2;
pub const OP_FMA: usize = 3;

/// Render a per-layer stats block as a human-readable string.
///
/// The output always starts with a `"layer stats:"` header so callers and tests
/// can assert the header is present.
pub fn report(s: &CompileStats) -> String {
    format!(
        "layer stats: lanes={} mov={} add={} mul={} fma={} specials={} max_live_cells={} \
         inline_reads={} cell_reads={} cell_loads={} cell_stores={} \
         evicts={} reloads={} recomputes={} split_count={} avg_chunk={:.2} \
         dram_reads={} ldc_reads={} special_reads={}",
        s.program_lanes,
        s.op_counts[OP_MOV],
        s.op_counts[OP_ADD],
        s.op_counts[OP_MUL],
        s.op_counts[OP_FMA],
        s.special_gathers,
        s.max_live_cells,
        s.inline_reads,
        s.cell_reads,
        s.cell_loads,
        s.cell_stores,
        s.evicts,
        s.reloads,
        s.recomputes,
        s.split_count,
        s.avg_chunk,
        s.dram_reads,
        s.ldc_reads,
        s.special_reads,
    )
}
