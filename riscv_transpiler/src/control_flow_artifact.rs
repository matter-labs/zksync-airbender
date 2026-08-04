//! Control-flow target artifact for advanced JIT compilation.
//!
//! Collects, for a given program (the pre-decoded `&[Instruction]`):
//!   * static targets of every `JAL` and `BRANCH` (computed from PC + immediate),
//!   * static targets of `JALR` derived from constant-producing fusion candidates
//!     (`LUI`/`AUIPC` [+ `ADDI`] immediately feeding the `JALR` base register), and
//!   * dynamic targets of every executed `JALR`, observed (with hit counts) while
//!     running the program over one or more non-determinism response instances.
//!
//! [`build_control_flow_artifact`] is the harness: it runs the same binary over an
//! arbitrary number of non-determinism sources and accumulates the dynamic targets.
//! The artifact can be serialized to / from disk and will feed a later, more
//! advanced JIT pass (e.g. devirtualizing indirect jumps, building jump tables).

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use common_constants::{TimestampScalar, TIMESTAMP_STEP};
use field::Mersenne31Field;

use crate::ir::simple_instruction_set::{Instruction, InstructionName};
use crate::vm::{
    DelegationsAndFamiliesCounters, InstructionTape, NonDeterminismCSRSource, RamWithRomRegion,
    SimpleTape, State, VM,
};

/// How far back to look for the constant definition of a `JALR` base register, and
/// how deep to follow an `ADDI` chain on top of a `LUI`/`AUIPC`.
const JALR_BACK_WINDOW: usize = 64;
const JALR_FUSION_DEPTH: usize = 6;

fn is_control_flow(name: InstructionName) -> bool {
    use InstructionName::*;
    matches!(name, Jal | Jalr | Branch)
}

/// The register written by `instr`, if it is a register-writing instruction
/// (accounts for the encoding: `Branch` keeps funct3 in `rd`, stores keep rd==0).
fn instruction_writes(instr: &Instruction) -> Option<u8> {
    use InstructionName::*;
    let writes = matches!(
        instr.name,
        Add | Sub
            | Slt
            | Sltu
            | And
            | Or
            | Xor
            | Sll
            | Srl
            | Sra
            | Mul
            | Mulh
            | Mulhsu
            | Mulhu
            | Div
            | Divu
            | Rem
            | Remu
            | Rol
            | Ror
            | ZimopAdd
            | ZimopSub
            | ZimopMul
            | ZimopFMA
            | ZimopTriAdd
            | ZimopIXorRot
            | Auipc
            | Jal
            | Jalr
            | Lw
            | Lhu
            | Lbu
            | Lh
            | Lb
            | ZicsrNonDeterminismRead
    );
    if writes && instr.rd != 0 {
        Some(instr.rd)
    } else {
        None
    }
}

/// Best-effort compile-time value of register `reg` just before `before_idx`,
/// following `LUI`/`AUIPC` and a bounded `ADDI` chain. Returns `None` if the value
/// is not a straight-line constant (e.g. produced by a load or across control flow).
fn const_reg_value(
    program: &[Instruction],
    before_idx: usize,
    reg: u8,
    depth: usize,
) -> Option<u32> {
    if reg == 0 {
        return Some(0); // x0 is hardwired zero
    }
    if depth == 0 {
        return None;
    }
    let lo = before_idx.saturating_sub(JALR_BACK_WINDOW);
    for k in (lo..before_idx).rev() {
        let instr = &program[k];
        if is_control_flow(instr.name) {
            return None; // a transfer between the def and the use; not a safe candidate
        }
        if instruction_writes(instr) == Some(reg) {
            let pc = (k as u32) * 4;
            use InstructionName::*;
            return match instr.name {
                Auipc => Some(pc.wrapping_add(instr.imm)),
                // `LUI rd, imm` and `ADDI rd, x0, imm` are both Add(rs1=0, rs2=0).
                Add if instr.rs1 == 0 && instr.rs2 == 0 => Some(instr.imm),
                // `ADDI rd, rs1, imm` (rs2 == x0) on top of a prior constant.
                Add if instr.rs2 == 0 => {
                    let base = const_reg_value(program, k, instr.rs1, depth - 1)?;
                    Some(base.wrapping_add(instr.imm))
                }
                _ => None, // written by a non-constant producer
            };
        }
    }
    None
}

/// Static `JALR` target from a `LUI`/`AUIPC`(+`ADDI`)+`JALR` fusion candidate, if any.
fn static_jalr_target(program: &[Instruction], i: usize) -> Option<u32> {
    let jalr = &program[i];
    let base = const_reg_value(program, i, jalr.rs1, JALR_FUSION_DEPTH)?;
    // JALR clears the least-significant bit of the computed target.
    Some(base.wrapping_add(jalr.imm) & 0xFFFF_FFFE)
}

/// Control-flow target artifact. PCs are byte addresses (instruction index * 4).
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ControlFlowArtifact {
    /// Number of instructions in the analyzed program.
    pub program_len: usize,
    /// Number of dynamic runs (non-determinism instances) folded in.
    pub runs: usize,
    /// `JAL` site PC -> static target PC.
    pub jal_targets: BTreeMap<u32, u32>,
    /// `BRANCH` site PC -> static taken-target PC (fall-through is site + 4).
    pub branch_targets: BTreeMap<u32, u32>,
    /// `JALR` site PC -> statically derivable targets (LUI/AUIPC[+ADDI] fusion).
    pub jalr_static_targets: BTreeMap<u32, BTreeSet<u32>>,
    /// `JALR` site PC -> observed dynamic target PC -> hit count (summed over runs).
    pub jalr_dynamic_targets: BTreeMap<u32, BTreeMap<u32, u64>>,
}

impl ControlFlowArtifact {
    /// Compute the static parts of the artifact (no execution).
    pub fn from_static(program: &[Instruction]) -> Self {
        let mut art = ControlFlowArtifact {
            program_len: program.len(),
            ..Default::default()
        };
        for (i, instr) in program.iter().enumerate() {
            let pc = (i as u32) * 4;
            match instr.name {
                InstructionName::Jal => {
                    art.jal_targets.insert(pc, pc.wrapping_add(instr.imm));
                }
                InstructionName::Branch => {
                    art.branch_targets.insert(pc, pc.wrapping_add(instr.imm));
                }
                InstructionName::Jalr => {
                    if let Some(t) = static_jalr_target(program, i) {
                        art.jalr_static_targets.entry(pc).or_default().insert(t);
                    }
                }
                _ => {}
            }
        }
        art
    }

    /// Run the program once over `nd` and fold the observed `JALR` targets in.
    pub fn record_run<ND: NonDeterminismCSRSource>(
        &mut self,
        tape: &SimpleTape,
        rom_image: &[u32],
        nd: &mut ND,
        timestamp_bound: TimestampScalar,
    ) {
        let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
        let mut ram =
            RamWithRomRegion::<{ common_constants::rom::ROM_SECOND_WORD_BITS }>::from_rom_content(
                rom_image,
                1 << 30,
            );
        while state.timestamp < timestamp_bound {
            let pc = state.pc;
            let is_jalr = tape.read_instruction(pc).name == InstructionName::Jalr;
            VM::<DelegationsAndFamiliesCounters>::run_step::<(), _, ND, Mersenne31Field>(
                &mut state,
                &mut ram,
                &mut (),
                tape,
                nd,
            );
            state.timestamp += TIMESTAMP_STEP;
            if is_jalr {
                *self
                    .jalr_dynamic_targets
                    .entry(pc)
                    .or_default()
                    .entry(state.pc)
                    .or_default() += 1;
            }
            if state.pc == pc {
                break; // self-loop halt
            }
        }
        self.runs += 1;
    }

    // ---- serialization (compact, dependency-free text format) ----------------

    /// Serialize the artifact to a simple text format (PCs in hex, counts decimal).
    pub fn save_to_file(&self, path: impl AsRef<Path>) -> std::io::Result<()> {
        use std::io::Write;
        let mut f = std::io::BufWriter::new(std::fs::File::create(path)?);
        writeln!(f, "CFG_ARTIFACT v1")?;
        writeln!(f, "program_len={}", self.program_len)?;
        writeln!(f, "runs={}", self.runs)?;
        writeln!(f, "[jal]")?;
        for (s, t) in &self.jal_targets {
            writeln!(f, "{:08x} {:08x}", s, t)?;
        }
        writeln!(f, "[branch]")?;
        for (s, t) in &self.branch_targets {
            writeln!(f, "{:08x} {:08x}", s, t)?;
        }
        writeln!(f, "[jalr_static]")?;
        for (s, ts) in &self.jalr_static_targets {
            write!(f, "{:08x}", s)?;
            for t in ts {
                write!(f, " {:08x}", t)?;
            }
            writeln!(f)?;
        }
        writeln!(f, "[jalr_dynamic]")?;
        for (s, tc) in &self.jalr_dynamic_targets {
            write!(f, "{:08x}", s)?;
            for (t, c) in tc {
                write!(f, " {:08x}:{}", t, c)?;
            }
            writeln!(f)?;
        }
        Ok(())
    }

    /// Parse an artifact previously written by [`Self::save_to_file`].
    pub fn load_from_file(path: impl AsRef<Path>) -> std::io::Result<Self> {
        use std::io::{Error, ErrorKind};
        let text = std::fs::read_to_string(path)?;
        let bad = |m: &str| Error::new(ErrorKind::InvalidData, m.to_string());
        let mut art = ControlFlowArtifact::default();
        let mut section = "";
        let mut lines = text.lines();
        if lines.next() != Some("CFG_ARTIFACT v1") {
            return Err(bad("missing/unknown header"));
        }
        let h32 = |s: &str| u32::from_str_radix(s, 16).map_err(|_| bad("bad hex"));
        for line in lines {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            if let Some(v) = line.strip_prefix("program_len=") {
                art.program_len = v.parse().map_err(|_| bad("bad program_len"))?;
                continue;
            }
            if let Some(v) = line.strip_prefix("runs=") {
                art.runs = v.parse().map_err(|_| bad("bad runs"))?;
                continue;
            }
            if line.starts_with('[') {
                section = match line {
                    "[jal]" => "jal",
                    "[branch]" => "branch",
                    "[jalr_static]" => "jalr_static",
                    "[jalr_dynamic]" => "jalr_dynamic",
                    _ => return Err(bad("unknown section")),
                };
                continue;
            }
            let mut it = line.split_whitespace();
            let site = h32(it.next().ok_or_else(|| bad("missing site"))?)?;
            match section {
                "jal" | "branch" => {
                    let t = h32(it.next().ok_or_else(|| bad("missing target"))?)?;
                    if section == "jal" {
                        art.jal_targets.insert(site, t);
                    } else {
                        art.branch_targets.insert(site, t);
                    }
                }
                "jalr_static" => {
                    let set = art.jalr_static_targets.entry(site).or_default();
                    for tok in it {
                        set.insert(h32(tok)?);
                    }
                }
                "jalr_dynamic" => {
                    let map = art.jalr_dynamic_targets.entry(site).or_default();
                    for tok in it {
                        let (t, c) = tok.split_once(':').ok_or_else(|| bad("bad target:count"))?;
                        map.insert(h32(t)?, c.parse().map_err(|_| bad("bad count"))?);
                    }
                }
                _ => return Err(bad("data before section")),
            }
        }
        Ok(art)
    }
}

impl std::fmt::Display for ControlFlowArtifact {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "=== control-flow artifact ===")?;
        writeln!(f, "program_len={} runs={}", self.program_len, self.runs)?;
        writeln!(
            f,
            "static targets: JAL sites={}, BRANCH sites={}",
            self.jal_targets.len(),
            self.branch_targets.len()
        )?;

        // JALR coverage breakdown.
        let dyn_sites: BTreeSet<u32> = self.jalr_dynamic_targets.keys().copied().collect();
        let stat_sites: BTreeSet<u32> = self.jalr_static_targets.keys().copied().collect();
        let all_sites: BTreeSet<u32> = dyn_sites.union(&stat_sites).copied().collect();
        let dyn_only = dyn_sites.difference(&stat_sites).count();
        let stat_only = stat_sites.difference(&dyn_sites).count();
        let both = stat_sites.intersection(&dyn_sites).count();

        // Indirection degree: how many distinct dynamic targets per executed JALR.
        let mut monomorphic = 0usize; // exactly 1 observed target
        let mut polymorphic = 0usize; // >1 observed target
        let mut total_dyn_targets = 0u64;
        let mut max_targets = 0usize;
        for tc in self.jalr_dynamic_targets.values() {
            match tc.len() {
                1 => monomorphic += 1,
                _ => polymorphic += 1,
            }
            total_dyn_targets += tc.values().sum::<u64>();
            max_targets = max_targets.max(tc.len());
        }

        // How often the static fusion target matched an observed dynamic target.
        let mut static_confirmed = 0usize;
        for (site, targets) in &self.jalr_static_targets {
            if let Some(dyn_t) = self.jalr_dynamic_targets.get(site) {
                if targets.iter().any(|t| dyn_t.contains_key(t)) {
                    static_confirmed += 1;
                }
            }
        }

        writeln!(
            f,
            "JALR sites: total={} (static-only={}, dynamic-only={}, both={})",
            all_sites.len(),
            stat_only,
            dyn_only,
            both
        )?;
        writeln!(
            f,
            "  executed JALR sites: {} (monomorphic={}, polymorphic={}, max_targets={})",
            self.jalr_dynamic_targets.len(),
            monomorphic,
            polymorphic,
            max_targets
        )?;
        writeln!(f, "  total dynamic JALR transfers: {}", total_dyn_targets)?;
        writeln!(
            f,
            "  static fusion targets confirmed by execution: {}/{}",
            static_confirmed,
            stat_sites.len()
        )?;
        Ok(())
    }
}

/// Harness: run `instructions` over every supplied non-determinism source, building
/// a [`ControlFlowArtifact`] (static targets computed once; dynamic `JALR` targets
/// accumulated across all runs). Supplying more, diverse non-determinism instances
/// improves dynamic `JALR` target coverage.
///
/// `instructions` should be decoded the way the replayer decodes
/// (`preprocess_bytecode::<Config, true>`); `rom_image` is the initial memory image.
pub fn build_control_flow_artifact<ND, I>(
    instructions: &[Instruction],
    rom_image: &[u32],
    nd_sources: I,
    timestamp_bound: TimestampScalar,
) -> ControlFlowArtifact
where
    ND: NonDeterminismCSRSource,
    I: IntoIterator<Item = ND>,
{
    let mut artifact = ControlFlowArtifact::from_static(instructions);
    let tape = SimpleTape::new(instructions);
    for mut nd in nd_sources {
        artifact.record_run(&tape, rom_image, &mut nd, timestamp_bound);
    }
    artifact
}
