//! Static and dynamic instrumentation for the pre-decoded RISC-V bytecode, used to
//! guide JIT performance work.
//!
//! * [`analyze_static_bytecode`] inspects a `&[Instruction]` (the output of
//!   `ir::simple_instruction_set::preprocess_bytecode`) and reports register usage,
//!   the distribution of straight-line (control-flow-free) run lengths, and the
//!   number of adjacent instruction pairs that match common macro-fusion patterns.
//! * [`analyze_dynamic_execution`] runs the program through the reference VM and
//!   reports the same register-usage and run-length statistics weighted by actual
//!   execution frequency.

use std::fmt;

use crate::ir::simple_instruction_set::{Instruction, InstructionName};

/// Standard RISC-V ABI register names, indexed by register number.
pub const ABI_NAMES: [&str; 32] = [
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0/fp", "s1", "a0", "a1", "a2", "a3", "a4",
    "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4",
    "t5", "t6",
];

/// Registers currently mapped to host x86-64 GPRs by the JIT (`rv_to_gpr`): x9..=x15.
/// Everything else lives in XMM lanes and is accessed via `pextrd`/`pinsrd`.
const HOST_GPR_MAPPED: std::ops::RangeInclusive<u8> = 9..=15;

fn is_host_gpr_mapped(reg: u8) -> bool {
    HOST_GPR_MAPPED.contains(&reg)
}

/// True for instructions that terminate a straight-line (fusible) run: control-flow
/// transfers, plus padding (`Illegal`) and heavy delegated calls (`ZicsrDelegation`),
/// which are not straight-line ALU/memory code.
fn breaks_straight_line(name: InstructionName) -> bool {
    use InstructionName::*;
    matches!(name, Jal | Jalr | Branch | Illegal | ZicsrDelegation)
}

/// True for the three genuine control-flow transfer instructions.
fn is_control_flow(name: InstructionName) -> bool {
    use InstructionName::*;
    matches!(name, Jal | Jalr | Branch)
}

/// The GPR operands an instruction actually uses, accounting for the
/// `simple_instruction_set` encoding quirks: `Branch` stores funct3 in `rd` (not a
/// register), stores keep `rd == 0`, immediate ALU forms keep `rs2 == 0`, etc.
#[derive(Clone, Copy, Default)]
struct GprRoles {
    rd_write: Option<u8>,
    rs1_read: Option<u8>,
    rs2_read: Option<u8>,
}

fn gpr_roles(instr: &Instruction) -> GprRoles {
    use InstructionName::*;
    let rd = instr.rd;
    let rs1 = instr.rs1;
    let rs2 = instr.rs2;
    let rw = |w, r1, r2| GprRoles {
        rd_write: w,
        rs1_read: r1,
        rs2_read: r2,
    };
    match instr.name {
        // Register/immediate ALU: rd = f(rs1, rs2|imm). For immediate forms rs2 == x0.
        Add | Sub | Slt | Sltu | And | Or | Xor | Sll | Srl | Sra | Mul | Mulh | Mulhsu | Mulhu
        | Div | Divu | Rem | Remu | Rol | Ror | ZimopAdd | ZimopSub | ZimopMul | ZimopFMA
        | ZimopTriAdd | ZimopIXorRot => rw(Some(rd), Some(rs1), Some(rs2)),
        // Upper-immediate / link: write rd only.
        Auipc | Jal => rw(Some(rd), None, None),
        // Jalr: rd = pc+4; target from rs1.
        Jalr => rw(Some(rd), Some(rs1), None),
        // Branch: compares rs1, rs2; `rd` holds funct3, not a register.
        Branch => rw(None, Some(rs1), Some(rs2)),
        // Loads: rd = mem[rs1 + imm].
        Lw | Lhu | Lbu | Lh | Lb => rw(Some(rd), Some(rs1), None),
        // Stores: mem[rs1 + imm] = rs2; no rd.
        Sw | Sh | Sb => rw(None, Some(rs1), Some(rs2)),
        // Non-determinism CSR read/write.
        ZicsrNonDeterminismRead => rw(Some(rd), None, None),
        ZicsrNonDeterminismWrite => rw(None, Some(rs1), None),
        // No real GPR operands.
        Nop | Illegal | ZicsrDelegation | ZicsrMarkerCsr | FormalEnd => GprRoles::default(),
    }
}

/// True if `instr` reads register `x` (x != 0) as one of its source operands.
fn reads_reg(instr: &Instruction, x: u8) -> bool {
    let r = gpr_roles(instr);
    r.rs1_read == Some(x) || r.rs2_read == Some(x)
}

/// ALU producers whose result is a plausible fusion source (writes `rd`).
fn is_alu_producer(name: InstructionName) -> bool {
    use InstructionName::*;
    matches!(
        name,
        Add | Sub | Slt | Sltu | And | Or | Xor | Sll | Srl | Sra | Auipc | Mul | Mulh | Mulhsu
            | Mulhu | Div | Divu | Rem | Remu
    )
}

// ---------------------------------------------------------------------------
// Shared accumulators
// ---------------------------------------------------------------------------

/// Per-register read/write tallies.
#[derive(Clone)]
struct GprUsage {
    reads: [u64; 32],
    writes: [u64; 32],
}

impl GprUsage {
    fn new() -> Self {
        Self {
            reads: [0; 32],
            writes: [0; 32],
        }
    }

    #[inline]
    fn account(&mut self, instr: &Instruction, weight: u64) {
        let r = gpr_roles(instr);
        // x0 is hardwired-zero and never needs a host register, so it is excluded.
        if let Some(x) = r.rs1_read {
            if x != 0 {
                self.reads[x as usize] += weight;
            }
        }
        if let Some(x) = r.rs2_read {
            if x != 0 {
                self.reads[x as usize] += weight;
            }
        }
        if let Some(x) = r.rd_write {
            if x != 0 {
                self.writes[x as usize] += weight;
            }
        }
    }

    fn total(&self, reg: usize) -> u64 {
        self.reads[reg] + self.writes[reg]
    }

    fn fmt_table(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut order: Vec<usize> = (1..32).collect();
        order.sort_by(|&a, &b| self.total(b).cmp(&self.total(a)));
        let grand: u64 = (1..32).map(|i| self.total(i)).sum();
        writeln!(
            f,
            "  {:>4} {:>6} {:>14} {:>14} {:>14} {:>6} {:>5}",
            "reg", "abi", "reads", "writes", "total", "%", "host?"
        )?;
        for &reg in &order {
            let tot = self.total(reg);
            if tot == 0 {
                continue;
            }
            writeln!(
                f,
                "  x{:<3} {:>6} {:>14} {:>14} {:>14} {:>5.1}% {:>5}",
                reg,
                ABI_NAMES[reg],
                self.reads[reg],
                self.writes[reg],
                tot,
                if grand > 0 {
                    100.0 * tot as f64 / grand as f64
                } else {
                    0.0
                },
                if is_host_gpr_mapped(reg as u8) {
                    "gpr"
                } else {
                    "xmm"
                },
            )?;
        }
        // How much of all register traffic currently lands in host GPRs vs XMM lanes.
        let in_gpr: u64 = (1..32)
            .filter(|&i| is_host_gpr_mapped(i as u8))
            .map(|i| self.total(i))
            .sum();
        if grand > 0 {
            writeln!(
                f,
                "  -> {:.1}% of register accesses hit host GPRs (x9..x15); {:.1}% go through XMM lanes",
                100.0 * in_gpr as f64 / grand as f64,
                100.0 * (grand - in_gpr) as f64 / grand as f64,
            )?;
        }
        Ok(())
    }
}

/// Histogram of straight-line run lengths (index = length, value = count of runs).
#[derive(Clone)]
struct RunHistogram {
    counts: Vec<u64>,
}

impl RunHistogram {
    fn new() -> Self {
        Self { counts: Vec::new() }
    }

    #[inline]
    fn record(&mut self, len: usize) {
        if len == 0 {
            return;
        }
        if len >= self.counts.len() {
            self.counts.resize(len + 1, 0);
        }
        self.counts[len] += 1;
    }

    fn total_runs(&self) -> u64 {
        self.counts.iter().sum()
    }

    fn total_instructions(&self) -> u64 {
        self.counts
            .iter()
            .enumerate()
            .map(|(len, &c)| len as u64 * c)
            .sum()
    }

    fn percentile(&self, p: f64) -> usize {
        let target = (self.total_runs() as f64 * p).ceil() as u64;
        let mut acc = 0u64;
        for (len, &c) in self.counts.iter().enumerate() {
            acc += c;
            if acc >= target {
                return len;
            }
        }
        self.counts.len().saturating_sub(1)
    }

    fn fmt_summary(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let runs = self.total_runs();
        if runs == 0 {
            return writeln!(f, "  (no runs)");
        }
        let instrs = self.total_instructions();
        let max = self.counts.len().saturating_sub(1);
        writeln!(
            f,
            "  runs={} straight-line-instrs={} mean={:.2} p50={} p90={} p99={} max={}",
            runs,
            instrs,
            instrs as f64 / runs as f64,
            self.percentile(0.50),
            self.percentile(0.90),
            self.percentile(0.99),
            max,
        )?;
        // Bucketed histogram: 1..=16 individually, then exponential buckets.
        let buckets: [(usize, usize); 9] = [
            (1, 1),
            (2, 2),
            (3, 3),
            (4, 4),
            (5, 6),
            (7, 8),
            (9, 16),
            (17, 32),
            (33, usize::MAX),
        ];
        writeln!(f, "  {:>10} {:>12} {:>7}  histogram", "len", "runs", "%")?;
        for (lo, hi) in buckets {
            if lo >= self.counts.len() {
                break;
            }
            let hi_c = hi.min(self.counts.len().saturating_sub(1));
            let c: u64 = self.counts[lo..=hi_c].iter().sum();
            if c == 0 {
                continue;
            }
            let pct = 100.0 * c as f64 / runs as f64;
            let bar = "#".repeat(((pct / 2.0) as usize).min(50));
            let label = if lo == hi_c {
                format!("{}", lo)
            } else if hi == usize::MAX {
                format!("{}+", lo)
            } else {
                format!("{}-{}", lo, hi_c)
            };
            writeln!(f, "  {:>10} {:>12} {:>6.1}%  {}", label, c, pct, bar)?;
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Static analysis
// ---------------------------------------------------------------------------

/// Static (per-instruction, unweighted) statistics over the decoded program.
pub struct StaticBytecodeStats {
    total_instructions: usize,
    illegal_instructions: usize,
    control_flow_instructions: usize,
    gpr: GprUsage,
    runs: RunHistogram,
    /// (pattern name, occurrences) for adjacent-pair macro-fusion candidates.
    fusion: Vec<(&'static str, u64)>,
}

/// Analyze the decoded bytecode without executing it.
///
/// Expects the output of `ir::simple_instruction_set::preprocess_bytecode`. Runs are
/// measured in program order (fall-through), so they approximate static basic blocks.
pub fn analyze_static_bytecode(program: &[Instruction]) -> StaticBytecodeStats {
    let mut gpr = GprUsage::new();
    let mut runs = RunHistogram::new();
    let mut cur_run = 0usize;
    let mut control_flow_instructions = 0usize;
    let mut illegal_instructions = 0usize;

    for instr in program {
        gpr.account(instr, 1);
        if instr.name == InstructionName::Illegal {
            illegal_instructions += 1;
        }
        if is_control_flow(instr.name) {
            control_flow_instructions += 1;
        }
        if breaks_straight_line(instr.name) {
            runs.record(cur_run);
            cur_run = 0;
        } else {
            cur_run += 1;
        }
    }
    runs.record(cur_run);

    // Adjacent-pair macro-fusion candidates (static fall-through adjacency).
    let mut lui_addi = 0u64;
    let mut auipc_use = 0u64;
    let mut slli_add = 0u64;
    let mut cmp_branch = 0u64;
    let mut load_use = 0u64;
    let mut dep_alu = 0u64;
    for w in program.windows(2) {
        let (a, b) = (&w[0], &w[1]);
        use InstructionName::*;
        // lui + addi -> 32-bit constant materialization
        if a.name == Add && a.rs1 == 0 && a.rs2 == 0 && a.rd != 0 && b.name == Add && b.rs2 == 0
            && b.rs1 == a.rd
        {
            lui_addi += 1;
        }
        // auipc + (addi | load | store | jalr) using its result -> PC-relative address
        if a.name == Auipc && a.rd != 0 && reads_reg(b, a.rd) {
            auipc_use += 1;
        }
        // slli + add -> shifted-index address computation
        if a.name == Sll && a.rs2 == 0 && a.rd != 0 && b.name == Add && b.rs2 != 0
            && (b.rs1 == a.rd || b.rs2 == a.rd)
        {
            slli_add += 1;
        }
        // slt/sltu + branch on the comparison result
        if matches!(a.name, Slt | Sltu) && a.rd != 0 && b.name == Branch && reads_reg(b, a.rd) {
            cmp_branch += 1;
        }
        // load + immediate use of the loaded value (load-to-use)
        if matches!(a.name, Lw | Lhu | Lbu | Lh | Lb) && a.rd != 0 && reads_reg(b, a.rd) {
            load_use += 1;
        }
        // generic dependent ALU pair (producer immediately consumed)
        if is_alu_producer(a.name) && a.rd != 0 && reads_reg(b, a.rd) {
            dep_alu += 1;
        }
    }

    StaticBytecodeStats {
        total_instructions: program.len(),
        illegal_instructions,
        control_flow_instructions,
        gpr,
        runs,
        fusion: vec![
            ("lui+addi (const materialize)", lui_addi),
            ("auipc+use (pc-relative addr)", auipc_use),
            ("slli+add (shifted index)", slli_add),
            ("slt/sltu+branch", cmp_branch),
            ("load+use (load-to-use)", load_use),
            ("dependent ALU pair (any producer->consumer)", dep_alu),
        ],
    }
}

impl fmt::Display for StaticBytecodeStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== STATIC bytecode analysis ===")?;
        writeln!(
            f,
            "instructions={} (control-flow={}, illegal/padding={})",
            self.total_instructions, self.control_flow_instructions, self.illegal_instructions
        )?;
        writeln!(f, "\n-- most-used GPRs (static, x0 excluded) --")?;
        self.gpr.fmt_table(f)?;
        writeln!(
            f,
            "\n-- straight-line run lengths (between control-flow/delegation/padding) --"
        )?;
        self.runs.fmt_summary(f)?;
        writeln!(f, "\n-- macro-fusion candidate pairs (static adjacency) --")?;
        for (name, count) in &self.fusion {
            writeln!(f, "  {:>10}  {}", count, name)?;
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Dynamic analysis
// ---------------------------------------------------------------------------

/// Dynamic (execution-weighted) statistics gathered by running the program.
pub struct DynamicExecutionStats {
    executed_instructions: u64,
    control_flow_executed: u64,
    gpr: GprUsage,
    runs: RunHistogram,
    halted: bool,
}

impl fmt::Display for DynamicExecutionStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== DYNAMIC execution analysis ===")?;
        writeln!(
            f,
            "executed instructions={} (control-flow={}, halted={})",
            self.executed_instructions, self.control_flow_executed, self.halted
        )?;
        writeln!(f, "\n-- most-used GPRs (execution-weighted, x0 excluded) --")?;
        self.gpr.fmt_table(f)?;
        writeln!(
            f,
            "\n-- executed straight-line run lengths (between executed control-flow) --"
        )?;
        self.runs.fmt_summary(f)?;
        Ok(())
    }
}

/// Run `program` through the reference VM and collect execution-weighted register
/// usage and straight-line run-length statistics.
///
/// `program` must be decoded the same way the replayer decodes it
/// (`preprocess_bytecode::<Config, true>`), `rom_image` is the initial memory image
/// (the binary), and `nd` supplies non-determinism. Execution stops at the program's
/// self-loop halt or when `timestamp_bound` is reached.
pub fn analyze_dynamic_execution<ND>(
    program: &[Instruction],
    rom_image: &[u32],
    nd: &mut ND,
    timestamp_bound: common_constants::TimestampScalar,
) -> DynamicExecutionStats
where
    ND: crate::vm::NonDeterminismCSRSource,
{
    use common_constants::TIMESTAMP_STEP;
    use field::Mersenne31Field;

    use crate::vm::{
        DelegationsAndFamiliesCounters, RamWithRomRegion, SimpleTape, State, VM,
    };

    let tape = SimpleTape::new(program);
    let mut ram = RamWithRomRegion::<{ common_constants::rom::ROM_SECOND_WORD_BITS }>::from_rom_content(
        rom_image,
        1 << 30,
    );
    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());

    let mut gpr = GprUsage::new();
    let mut runs = RunHistogram::new();
    let mut cur_run = 0usize;
    let mut executed_instructions = 0u64;
    let mut control_flow_executed = 0u64;
    let mut halted = false;

    while state.timestamp < timestamp_bound {
        let pc = state.pc;
        // Read the instruction about to execute and account for it before stepping.
        let instr = {
            use crate::vm::InstructionTape;
            tape.read_instruction(pc)
        };
        gpr.account(&instr, 1);
        executed_instructions += 1;
        if is_control_flow(instr.name) {
            control_flow_executed += 1;
        }
        if breaks_straight_line(instr.name) {
            runs.record(cur_run);
            cur_run = 0;
        } else {
            cur_run += 1;
        }

        VM::<DelegationsAndFamiliesCounters>::run_step::<(), _, ND, Mersenne31Field>(
            &mut state, &mut ram, &mut (), &tape, nd,
        );
        state.timestamp += TIMESTAMP_STEP;

        if state.pc == pc {
            halted = true;
            break;
        }
    }
    runs.record(cur_run);

    DynamicExecutionStats {
        executed_instructions,
        control_flow_executed,
        gpr,
        runs,
        halted,
    }
}
