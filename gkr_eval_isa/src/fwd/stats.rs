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
/// - `cell_stores`: all `MOV DstFromAcc Smem{cell}` emitted (evicts + split evicts).
///   SP1: not yet counted.
/// - `evicts`: acc evictions during over-cap split (`emit_reduction_group`).
///   SP1: not yet counted.
/// - `reloads`: evict cells folded back in via ADD/MUL during splits.
///   SP1: not yet counted.
/// - `recomputes`: times a child had to be re-lowered into the acc (currently 0).
///   SP1: not yet counted.
/// - `special_gathers`: number of resolved-fold `Special` operands emitted (= `ctx.specials.len()`
///   after compilation). REAL in SP1.
/// - `max_live_cells`: high-water mark of simultaneously live smem cells across
///   all roots. REAL in SP1 (from `trace.max_live_cells`).
/// - `split_count`: number of over-cap reduction groups that were split.
///   SP1: not yet counted.
/// - `avg_chunk`: average chunk size across all split groups (0.0 if no splits).
///   SP1: not yet counted.
/// - `dram_reads`: DRAM-read operands. SP1: not yet counted.
/// - `ldc_reads`: Ldc (load cache) operands. SP1: not yet counted.
/// - `special_reads`: `OperandLine::Special{desc}` operand-use count.
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
    pub split_count: usize,    // SP1: not yet counted
    pub avg_chunk: f64,        // SP1: not yet counted
    pub dram_reads: usize,     // SP1: not yet counted
    pub ldc_reads: usize,      // SP1: not yet counted
    pub special_reads: usize,  // SP1: not yet counted
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;
    use std::path::PathBuf;

    use cs::gkr_compiler::dag_ir::{lower_dag, validate};
    use cs::gkr_compiler::GKRCircuitArtifact;
    use field::baby_bear::base::BabyBearField;

    use crate::fwd::compile::{build_cross_layer_field_map, compile_layer};

    fn compiled_circuit_dir() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits")
    }

    fn load_fixture(name: &str) -> Option<GKRCircuitArtifact<BabyBearField>> {
        let dir = compiled_circuit_dir();
        let path = dir.join(format!("{}.json", name));
        let bytes = std::fs::read(&path).ok()?;
        serde_json::from_slice(&bytes).ok()
    }

    const BUDGET: usize = 1024;

    /// Step 1 (brief): compile `add_sub` layer 0 and assert:
    /// - `program_lanes > 0`
    /// - `op_counts.iter().sum() > 0`
    /// - `max_live_cells <= budget`
    /// - `special_gathers == ctx.specials.len()` (number of resolved folds in layer 0)
    /// - `report(&stats)` contains the per-layer header substring
    #[test]
    fn add_sub_layer0_stats() {
        let artifact = match load_fixture("add_sub_lui_auipc_mop_layout_gkr") {
            Some(a) => a,
            None => {
                eprintln!("add_sub_lui_auipc_mop_layout_gkr fixture not found — skipping stats gate");
                return;
            }
        };

        let dag = lower_dag(&artifact).expect("lower_dag failed");
        validate(&dag).expect("validate failed");

        let dag_layer = &dag.layers[0];
        let art_layer = &artifact.layers[0];
        let cross_layer_fields = build_cross_layer_field_map(&dag);
        let compiled =
            compile_layer(dag_layer, art_layer, &BTreeMap::new(), &cross_layer_fields, BUDGET)
                .expect("compile_layer failed");

        let stats = &compiled.stats;

        // program_lanes > 0: at least one instruction was emitted
        assert!(stats.program_lanes > 0,
            "expected program_lanes > 0, got {}", stats.program_lanes);

        // op_counts.sum() > 0: at least one opcode counted
        let total_ops: usize = stats.op_counts.iter().sum();
        assert!(total_ops > 0,
            "expected op_counts sum > 0, got {:?}", stats.op_counts);

        // program_lanes == total instruction count
        assert_eq!(stats.program_lanes, compiled.program.instrs.len(),
            "program_lanes mismatch");

        // op_counts sum equals program_lanes
        assert_eq!(total_ops, stats.program_lanes,
            "op_counts sum {} != program_lanes {}", total_ops, stats.program_lanes);

        // max_live_cells within budget
        assert!(stats.max_live_cells <= BUDGET,
            "max_live_cells {} > budget {}", stats.max_live_cells, BUDGET);

        // special_gathers == number of resolved folds in ctx (SpecialTable length)
        let expected_specials = compiled.ctx.specials.len();
        assert_eq!(stats.special_gathers, expected_specials,
            "special_gathers {} != ctx.specials.len() {}", stats.special_gathers, expected_specials);

        // report contains the per-layer header
        let r = report(stats);
        assert!(r.contains("layer stats:"),
            "report missing 'layer stats:' header: {}", r);
    }

    fn count_global_reads(instr: &crate::fwd::isa::Instr) -> usize {
        use crate::fwd::isa::{Instr, OperandLine};
        let mut n = 0;
        let mut tally = |op: &OperandLine| if matches!(op, OperandLine::Global { .. }) { n += 1 };
        match instr {
            Instr::Add { operands, .. } | Instr::Mul { operands, .. } => operands.iter().for_each(&mut tally),
            Instr::Fma { pairs, .. } => pairs.iter().for_each(|(l, r)| { tally(l); tally(r); }),
            Instr::Mov { src: Some(op), .. } => tally(op),
            Instr::Mov { src: None, .. } => {}
        }
        n
    }

    #[test]
    fn add_sub_layer0_dram_reads_counted() {
        let artifact = match load_fixture("add_sub_lui_auipc_mop_layout_gkr") { Some(a) => a, None => return };
        let dag = lower_dag(&artifact).expect("lower_dag");
        validate(&dag).expect("validate");
        let cross = build_cross_layer_field_map(&dag);
        let compiled = compile_layer(&dag.layers[0], &artifact.layers[0], &BTreeMap::new(), &cross, BUDGET).expect("compile");
        let s = &compiled.stats;
        // add_sub L0 reads real BaseLayerMemory/Witness/Setup/VirtualSetup columns + Prior caches.
        assert!(s.dram_reads > 0, "expected dram_reads > 0, got {}", s.dram_reads);
        // Sanity: every Global operand in the program is counted exactly once.
        let mut manual = 0usize;
        for instr in &compiled.program.instrs {
            manual += count_global_reads(instr); // helper below, test-local
        }
        // Alias operands (zero-lane CopyAlias) are DRAM reads too when Global.
        for (_, out) in &compiled.root_outputs {
            if let crate::fwd::context::RootOutput::Alias(crate::fwd::isa::OperandLine::Global { .. }) = out {
                manual += 1;
            }
        }
        assert_eq!(s.dram_reads, manual, "dram_reads {} != manual global-read count {} (instrs + alias globals)", s.dram_reads, manual);
    }

    // Immutable per-stage baselines — never overwrite; later stages add their own const and assert `<`.
    pub const ADD_SUB_S1_DRAM_READS: usize = 85;
    pub const MUL_DIV_S1_DRAM_READS: usize = 110;

    fn dram_reads_of(name: &str) -> usize {
        let artifact = load_fixture(name).expect("fixture");
        let dag = lower_dag(&artifact).unwrap();
        validate(&dag).unwrap();
        let cross = build_cross_layer_field_map(&dag);
        let compiled = compile_layer(&dag.layers[0], &artifact.layers[0], &artifact.scratch_space_mapping, &cross, BUDGET).unwrap();
        compiled.stats.dram_reads
    }

    #[test]
    fn s1_dram_reads_baselines() {
        if load_fixture("add_sub_lui_auipc_mop_layout_gkr").is_none() { return; }
        assert_eq!(dram_reads_of("add_sub_lui_auipc_mop_layout_gkr"), ADD_SUB_S1_DRAM_READS, "add_sub S1 dram_reads changed");
        assert_eq!(dram_reads_of("unsigned_mul_div_layout_gkr"), MUL_DIV_S1_DRAM_READS, "unsigned_mul_div S1 dram_reads changed");
    }

    #[test]
    fn report_renders_dram_ldc_and_special_read_counters() {
        let mut s = CompileStats::default();
        s.dram_reads = 7;
        s.ldc_reads = 3;
        s.special_reads = 5;
        let r = report(&s);
        assert!(r.contains("dram_reads=7"), "report missing dram_reads: {r}");
        assert!(r.contains("ldc_reads=3"), "report missing ldc_reads: {r}");
        assert!(r.contains("special_reads=5"), "report missing special_reads: {r}");
    }
}
