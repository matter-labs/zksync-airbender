//! Lazy (batched) timestamp & counter JIT path.
//!
//! The eager JIT (`JittedCode::preprocess_bytecode` in `impls.rs`) materializes,
//! on EVERY emulated instruction, the register-timestamp stores, the running
//! timestamp advance (`r8`), and the circuit-family counter increment. Those
//! values are only ever *observed* at memory accesses, delegations, and
//! non-determinism reads (snapshots fire only inside those). Between a basic-block
//! entry and the next such "branching point" we can defer all of that bookkeeping
//! into an accumulator and flush it ONCE.
//!
//! This module is compiled as a child of `impls` (see the `mod` declaration at the
//! bottom of `impls.rs`) so it can reuse the eager module's `macro_rules!` (textual
//! scope) and its private helper functions (`load`, `store_result`,
//! `record_circuit_type`, …) via `super`.
//!
//! Implementation (both stages complete; see `plans/radiant-singing-duckling.md`):
//!   * Stage A  — batched emission whose landings are the known region entries.
//!   * Stage B  — a full per-instruction EAGER copy emitted into the same buffer plus a
//!     dual JALR dispatch table: a target that is a known region entry resolves into the
//!     batched copy, any other target resolves into the eager copy (the fallback), which
//!     runs per-instruction and re-enters batched code at its next JAL/Branch. This makes
//!     the path correct for dynamic JALR targets the artifact never observed.

use super::*;

use dynasmrt::{dynasm, x64, DynasmApi, DynasmLabelApi};

use std::collections::HashSet;

use crate::control_flow_artifact::ControlFlowArtifact;
use crate::ir::simple_instruction_set::{Instruction, InstructionName};

// ---------------------------------------------------------------------------
// Region analysis
// ---------------------------------------------------------------------------

/// An instruction ends a region (forces a flush) if it transfers control or
/// observes timestamps/counters. Pure ALU instructions never end a region.
#[allow(dead_code)]
pub(crate) fn is_boundary(name: InstructionName) -> bool {
    use InstructionName::*;
    matches!(
        name,
        // control flow
        Jal | Jalr | Branch
        // memory observations
        | Lb | Lbu | Lh | Lhu | Lw | Sb | Sh | Sw
        // non-determinism / delegations
        | ZicsrNonDeterminismRead | ZicsrNonDeterminismWrite | ZicsrDelegation
    )
}

#[inline]
fn mark_entry(known: &mut [bool], pc: u32) {
    let idx = (pc / 4) as usize;
    if (pc % 4) == 0 && idx < known.len() {
        known[idx] = true;
    }
}

/// PCs that are valid *entries* into the batched code: a transfer can land there,
/// so the deferred state must be fully materialized at that point. Returns a
/// per-instruction boolean (indexed by instruction index = pc/4).
///
/// = {pc 0} ∪ JAL targets ∪ BRANCH targets ∪ BRANCH fall-through (site+4) ∪
///   static JALR targets ∪ observed dynamic JALR targets ∪ **return sites**.
///
/// Return sites (the ABI heuristic): a standard procedure return is
/// `jalr x0, 0(x1)`, which lands at the instruction right after some call. A call
/// writes the return address into `ra`/`x1` (`jal ra, …` / `jalr ra, …`), so
/// `call_site + 4` for every `rd == x1` JAL/JALR is a guaranteed return target.
/// Marking these statically captures *all* returns without needing the dynamic
/// artifact, leaving only true indirect jumps (`rd == x0`, `rs1 != x1`) and
/// indirect calls (`rd == x1`, no static fusion) reliant on observed targets.
#[allow(dead_code)]
pub(crate) fn compute_known_entries(
    program: &[Instruction],
    artifact: &ControlFlowArtifact,
) -> Vec<bool> {
    let n = program.len();
    let mut known = vec![false; n];
    if n > 0 {
        known[0] = true;
    }
    for t in artifact.jal_targets.values() {
        mark_entry(&mut known, *t);
    }
    for (site, t) in &artifact.branch_targets {
        mark_entry(&mut known, *t);
        mark_entry(&mut known, site.wrapping_add(4)); // not-taken fall-through
    }
    for targets in artifact.jalr_static_targets.values() {
        for t in targets {
            mark_entry(&mut known, *t);
        }
    }
    for targets in artifact.jalr_dynamic_targets.values() {
        for t in targets.keys() {
            mark_entry(&mut known, *t);
        }
    }
    // ABI heuristic: every call site (`rd == x1` JAL/JALR) has its return address
    // `pc + 4` reached by the matching `ret`, so it is a known entry.
    for (i, instr) in program.iter().enumerate() {
        if instr.rd == 1 && matches!(instr.name, InstructionName::Jal | InstructionName::Jalr) {
            let pc = (i as u32) * 4;
            mark_entry(&mut known, pc.wrapping_add(4));
        }
    }
    known
}

// ---------------------------------------------------------------------------
// Deferred timestamp / counter accumulator
// ---------------------------------------------------------------------------

const REG_UNTOUCHED: i32 = -1;

/// Accumulates the deferred per-instruction bookkeeping across a region of pure
/// ALU instructions. `r8` is held FROZEN at the region's base timestamp while a
/// region is in flight; `pending` is how far it should advance, and
/// `last_touch[r]` is the offset (relative to that frozen base) of register `r`'s
/// most recent timestamp touch.
///
/// The `touch_*` / `bump` / `count` methods mirror the eager `macro_rules!`
/// (`touch_register_and_increment_timestamp!`, `touch_register_and_bump_timestamp!`,
/// `pre_bump_timestamp_and_touch!`, `bump_timestamp!`) one-for-one, so feeding the
/// exact same call sequence an arm uses eagerly reproduces identical timestamps —
/// the per-opcode sub-slot offsets are correct by construction, not by a table.
#[allow(dead_code)]
pub(crate) struct Deferred {
    pending: i32,
    last_touch: [i32; 32],
    counts: [u64; MAX_NUM_COUNTERS],
    dirty: bool,
}

#[allow(dead_code)]
impl Deferred {
    pub(crate) fn new() -> Self {
        Self {
            pending: 0,
            last_touch: [REG_UNTOUCHED; 32],
            counts: [0; MAX_NUM_COUNTERS],
            dirty: false,
        }
    }

    #[inline]
    pub(crate) fn is_dirty(&self) -> bool {
        self.dirty
    }

    /// Mirror of `touch_register_and_increment_timestamp!`: `ts[r] = r8; r8 += 1`.
    #[inline]
    pub(crate) fn touch_inc(&mut self, r: u32) {
        self.last_touch[r as usize] = self.pending;
        self.pending += 1;
        self.dirty = true;
    }

    /// Mirror of `touch_register_and_bump_timestamp!`: `ts[r] = r8; r8 += d`.
    #[inline]
    pub(crate) fn touch_bump(&mut self, r: u32, d: i32) {
        self.last_touch[r as usize] = self.pending;
        self.pending += d;
        self.dirty = true;
    }

    /// Mirror of `pre_bump_timestamp_and_touch!`: `r8 += d; ts[r] = r8`.
    #[inline]
    pub(crate) fn pre_bump_touch(&mut self, d: i32, r: u32) {
        self.pending += d;
        self.last_touch[r as usize] = self.pending;
        self.dirty = true;
    }

    /// Mirror of `bump_timestamp!`: `r8 += d`.
    #[inline]
    pub(crate) fn bump(&mut self, d: i32) {
        self.pending += d;
        self.dirty = true;
    }

    /// Current deferred offset from the frozen `r8` (used to compute live memory
    /// timestamps in a merged run: the stamp value is `r8 + pending`).
    #[inline]
    pub(crate) fn pending(&self) -> i32 {
        self.pending
    }

    /// Mirror of `record_circuit_type(family, by)`.
    #[inline]
    pub(crate) fn count(&mut self, family: CounterType, by: u64) {
        self.counts[family as u8 as usize] += by;
        self.dirty = true;
    }

    /// Materialize everything accumulated since the last flush, in the order:
    /// (1) register timestamps (using the still-frozen `r8`), (2) `add r8, pending`,
    /// (3) counter increments. Then reset. Uses RAX as scratch — the caller must
    /// ensure RAX is dead at the flush point.
    pub(crate) fn flush(&mut self, ops: &mut x64::Assembler) {
        if !self.dirty {
            return;
        }
        for r in 0..32usize {
            let k = self.last_touch[r];
            if k == REG_UNTOUCHED {
                continue;
            }
            // The mapped value-registers keep their timestamp off-memory (in a host GPR
            // or an XMM lane, depending on the `ts_in_gpr` experiment); everything else
            // writes the register_timestamps[] slot. RAX is dead here (scratch for k!=0).
            flush_reg_timestamp(ops, r as u32, k);
        }
        if self.pending != 0 {
            dynasm!(ops
                ; add r8, self.pending
            );
        }
        for f in 0..MAX_NUM_COUNTERS {
            let mut by = self.counts[f];
            if by == 0 {
                continue;
            }
            let family = counter_type_from_index(f);
            // record_circuit_type takes a u16; chunk for safety (region counts are
            // tiny in practice).
            while by > 0 {
                let step = core::cmp::min(by, u16::MAX as u64);
                record_circuit_type(ops, family, step as u16);
                by -= step;
            }
        }
        *self = Self::new();
    }
}

// Cap on a fused word-mem run. A run writes its L trace entries before the single
// chunk-full check, so r9 transiently reaches up to (TRACE_CHUNK_LEN-1)+L; this must
// stay under MAX_TRACE_CHUNK_LEN (margin = MAX-TRACE_CHUNK_LEN). 32 is well under
// that margin and above essentially all observed runs (max ~36 splits into 32+4).
const MAX_MERGE_RUN: usize = 32;

/// Length of the maximal fusable run of consecutive word loads/stores starting at
/// `i`: same opcode (Lw or Sw), same base register, immediate stride ±4, and no
/// known region entry landing inside the run. For loads, the run cannot continue
/// past an element that overwrites the base register (its address would change).
/// Returns 1 when there is nothing to merge.
fn word_mem_run_len(program: &[Instruction], i: usize, known: &[bool]) -> usize {
    use InstructionName as Op;
    let a = &program[i];
    if !matches!(a.name, Op::Lw | Op::Sw) || i + 1 >= program.len() {
        return 1;
    }
    let opcode = a.name;
    let base = a.rs1;
    let is_load = matches!(opcode, Op::Lw);
    let stride = program[i + 1].imm.wrapping_sub(a.imm) as i32;
    if stride != 4 && stride != -4 {
        return 1;
    }
    let mut l = 1usize;
    while l < MAX_MERGE_RUN && i + l < program.len() {
        // A load that writes the base reg must be the last element (it changes the
        // address seen by the next access).
        if is_load && program[i + l - 1].rd == base {
            break;
        }
        if known[i + l] {
            break; // a transfer could land here; cannot fold across it
        }
        let cur = &program[i + l - 1];
        let nxt = &program[i + l];
        if nxt.name != opcode || nxt.rs1 != base {
            break;
        }
        if (nxt.imm.wrapping_sub(cur.imm) as i32) != stride {
            break;
        }
        l += 1;
    }
    l
}

/// Emit a fused run of `l` consecutive word loads/stores (see `word_mem_run_len`).
/// The base register is loaded once and the address incremented by the stride; the
/// per-word memory access + 2 trace writes are emitted eagerly (inherent), but the
/// register timestamps / counter / r8 advance are folded into `accum` and flushed
/// once, and a single trace-chunk-full check is done for the whole run.
fn emit_word_mem_run(
    ops: &mut x64::Assembler,
    accum: &mut Deferred,
    program: &[Instruction],
    start: usize,
    l: usize,
) {
    use InstructionName as Op;
    let first = &program[start];
    let is_load = matches!(first.name, Op::Lw);
    let base = first.rs1 as u32;
    let imm0 = first.imm as i32;
    let stride = program[start + 1].imm.wrapping_sub(first.imm) as i32;
    let tso = MemoryHolder::TIMESTAMPS_OFFSET as i32;
    let trtso = TraceChunk::TIMESTAMPS_OFFSET as i32;

    // Compute the first byte address into the scratch register (32-bit, wrapping
    // like RISC-V), loading the base register exactly once.
    let base_reg = load(ops, base);
    dynasm!(ops ; lea Rd(SCRATCH_REGISTER), [Rd(base_reg) + imm0]);

    for j in 0..l {
        if j > 0 {
            dynasm!(ops ; add Rd(SCRATCH_REGISTER), stride);
        }
        let instr = &program[start + j];
        let voff = (4 * j) as i32;
        let toff = trtso + (8 * j) as i32;
        if is_load {
            let rd = instr.rd as u32;
            let out = destination_gpr(rd);
            accum.touch_inc(base);
            let mem_off = accum.pending();
            dynasm!(ops
                ; mov Rd(out), DWORD [rsi + Rq(SCRATCH_REGISTER)]
                ; mov rdx, [rsi + tso + 2 * Rq(SCRATCH_REGISTER)] // old ts
                ; mov [rdi + r9 * 8 + toff], rdx // old ts -> trace
                ; lea rdx, [r8 + mem_off] // new ts (reuse rdx; frees RBP)
                ; mov [rsi + tso + 2 * Rq(SCRATCH_REGISTER)], rdx
                ; mov [rdi + r9 * 4 + voff], Rd(out)
            );
            store_result(ops, rd);
            accum.bump(1);
            accum.touch_bump(rd, 2);
            accum.count(CounterType::MemWord, 1);
        } else {
            let rs2 = instr.rs2 as u32;
            let value = load(ops, rs2);
            accum.touch_inc(base);
            accum.touch_inc(rs2);
            let mem_off = accum.pending();
            dynasm!(ops
                ; mov eax, DWORD [rsi + Rq(SCRATCH_REGISTER)]
                ; mov DWORD [rsi + Rq(SCRATCH_REGISTER)], Rd(value) // store new value (frees its reg)
                ; mov [rdi + r9 * 4 + voff], eax // old value -> trace (eax free)
                ; mov rax, [rsi + tso + 2 * Rq(SCRATCH_REGISTER)] // old ts (reuse rax)
                ; mov [rdi + r9 * 8 + toff], rax // old ts -> trace
                ; lea rdx, [r8 + mem_off] // new ts (rdx free after value stored)
                ; mov [rsi + tso + 2 * Rq(SCRATCH_REGISTER)], rdx
            );
            accum.bump(2);
            accum.count(CounterType::MemWord, 1);
        }
    }

    // Materialize the run's deferred register timestamps / counter / r8 advance,
    // then commit r9 and do ONE chunk-full check for the whole run.
    accum.flush(ops);
    let pc_for_trace = ((start + l) as u32) * 4;
    dynasm!(ops
        ; add r9, l as i32
        ;; check_to_save_trace!(ops, pc_for_trace)
    );
}

// === RAW value forwarding (option 2): skip a pextrd when a pure-ALU op's XMM
// result is read by the immediately-following pure-ALU op. The producer mirrors its
// result (already in EAX, and already pinsrd'd into the XMM lane) into RBP; the
// consumer reads RBP instead of re-extracting. The XMM lane stays current (the
// pinsrd is NOT deferred), so no flush discipline is needed. Only valid into the
// next instruction (RBP survives across pure ops; boundaries/known entries reset it).

fn is_pure_alu(n: InstructionName) -> bool {
    use InstructionName::*;
    matches!(
        n,
        Add | Sub
            | Slt
            | Sltu
            | And
            | Or
            | Xor
            | Sll
            | Srl
            | Sra
            | Auipc
            | Mul
            | Mulhu
            | Divu
            | Remu
            | Nop
            | ZimopAdd
            | ZimopSub
            | ZimopMul
    )
}

#[inline]
fn fwd_hit(fwd: Option<u32>, x: u32) -> bool {
    // Only XMM-resident registers are ever forwarded (x0 and host-GPR regs never).
    fwd == Some(x) && x != 0 && rv_to_gpr(x).is_none()
}

/// `load` with RAW forwarding: returns RBP if `x` is the forwarded register.
fn fl_load(ops: &mut x64::Assembler, fwd: Option<u32>, x: u32) -> u8 {
    if fwd_hit(fwd, x) {
        return x64::Rq::RBP as u8;
    }
    load(ops, x)
}

fn fl_load_into(ops: &mut x64::Assembler, fwd: Option<u32>, x: u32, dest: u8) {
    if fwd_hit(fwd, x) {
        if dest != x64::Rq::RBP as u8 {
            dynasm!(ops ; mov Rd(dest), ebp);
        }
        return;
    }
    load_into(ops, x, dest)
}

fn fl_load_abelian(ops: &mut x64::Assembler, fwd: Option<u32>, x: u32, y: u32, dest: u8) -> u8 {
    let a = rv_to_gpr(x);
    let b = rv_to_gpr(y);
    if a == Some(dest) {
        assert!(dest != x64::Rq::RAX as u8);
        fl_load(ops, fwd, y)
    } else if b == Some(dest) {
        assert!(dest != x64::Rq::RAX as u8);
        fl_load(ops, fwd, x)
    } else {
        fl_load_into(ops, fwd, x, dest);
        fl_load(ops, fwd, y)
    }
}

fn fl_load_abelian_into(
    ops: &mut x64::Assembler,
    fwd: Option<u32>,
    x: u32,
    y: u32,
    dest: u8,
    temp: u8,
) {
    let a = rv_to_gpr(x);
    let b = rv_to_gpr(y);
    if a == Some(dest) {
        assert!(dest != x64::Rq::RAX as u8);
        fl_load_into(ops, fwd, y, temp);
    } else if b == Some(dest) {
        assert!(dest != x64::Rq::RAX as u8);
        fl_load_into(ops, fwd, x, temp);
    } else {
        fl_load_into(ops, fwd, x, dest);
        fl_load_into(ops, fwd, y, temp);
    }
}

/// Producer hook: called after a pure-ALU op writes `rd` (value live in EAX). If
/// forwarding is enabled, `rd` is XMM-resident, and the next instruction is a
/// pure-ALU op (fall-through, not a jump target) that reads `rd`, stash EAX into
/// RBP and return `Some(rd)` so the consumer reads it without a pextrd.
fn maybe_forward(
    ops: &mut x64::Assembler,
    program: &[Instruction],
    i: usize,
    rd: u32,
    known: &[bool],
    enabled: bool,
) -> Option<u32> {
    if !enabled || rd == 0 || rv_to_gpr(rd).is_some() {
        return None;
    }
    let j = i + 1;
    if j >= program.len() || known[j] {
        return None;
    }
    let nxt = &program[j];
    if !is_pure_alu(nxt.name) {
        return None;
    }
    let reads = (nxt.rs1 as u32 == rd) || (nxt.rs2 as u32 == rd && nxt.rs2 != 0);
    if !reads {
        return None;
    }
    dynasm!(ops ; mov ebp, eax);
    Some(rd)
}

// Diagnostic port-pressure probe (env-gated): emit N dummy store-port ops or N
// dummy p5-shuffle ops per pure-ALU instruction. Measuring the MHz slope vs N
// reveals which port binds (a binding port drops MHz steeply; a slack one barely).
// The dummy store targets the red zone below RSP (never read); the dummy pextrd
// reads xmm0 into RCX (both dead at the injection point). Production sets N=0.
fn inject_dummy(ops: &mut x64::Assembler, stores: u32, p5: u32, alu: u32) {
    for _ in 0..stores {
        dynasm!(ops ; mov [rsp - 256], r8);
    }
    for _ in 0..p5 {
        dynasm!(ops ; pextrd ecx, xmm0, 0);
    }
    // Independent ALU µops (round-robin 3 regs to limit dependency chains), to probe
    // the p0156/retire throughput that the bookkeeping `add r8`/`paddq` consume.
    for k in 0..alu {
        match k % 3 {
            0 => dynasm!(ops ; add eax, 7),
            1 => dynasm!(ops ; add ecx, 7),
            _ => dynasm!(ops ; add edx, 7),
        }
    }
}

fn counter_type_from_index(i: usize) -> CounterType {
    use CounterType::*;
    match i {
        0 => AddSubLui,
        1 => BranchSlt,
        2 => ShiftBinaryCsr,
        3 => MulDiv,
        4 => MemWord,
        5 => MemSubword,
        6 => BlakeDelegation,
        7 => BigintDelegation,
        8 => KeccakDelegation,
        9 => BlakeGFunctionDelegation,
        _ => panic!("invalid counter index {}", i),
    }
}

// ---------------------------------------------------------------------------
// Constructor: batched (lazy) emission + eager fallback copy (see module docs).
// ---------------------------------------------------------------------------

impl<I: ContextImpl> JittedCode<I> {
    /// Batched (lazy) timestamp emitter with an eager fallback copy. The program is
    /// emitted twice: a batched copy landing at known region entries, and a full
    /// per-instruction eager copy. The `jump_offsets` table routes each dynamic JALR
    /// target to the batched copy if it is a known entry, else to the eager fallback
    /// (which re-enters batched code at its next JAL/Branch). See the module docs.
    pub fn preprocess_bytecode_lazy(
        program: &[Instruction],
        artifact: &ControlFlowArtifact,
        cycles_bound: Option<u32>,
    ) -> Self {
        use InstructionName as Op;

        let mut ops = x64::Assembler::new().unwrap();
        let start = ops.offset();

        let known = compute_known_entries(program, artifact);

        // ---- prologue / init (mirrors the eager constructor) ----
        dynasm!(ops
            ; ->start:
            ;; prologue!(ops)
            ; vzeroall
            // OPTION 1: r10..r13 hold values (a0..a3, init 0); r14/r15/rbx/rbp hold the
            // timestamps of those 4 (init 0 = untouched). All start zeroed.
            ; xor rbx, rbx
            ; xor rbp, rbp
            ; xor r10, r10
            ; xor r11, r11
            ; xor r12, r12
            ; xor r13, r13
            ; xor r14, r14
            ; xor r15, r15
            ; mov r8, INITIAL_TIMESTAMP as i32
            ; xor r9, r9
        );
        dynasm!(ops
            ; sub rsp, (MachineState::SIZE as i32)
        );
        for q in 0..MachineState::ZERO_INIT_QWORDS {
            dynasm!(ops ; mov QWORD [rsp + 8 * q as i32], 0);
        }
        dynasm!(ops
            ; mov [rsp + (MachineState::CONTEXT_PTR_OFFSET as i32)], rdx
        );
        if I::PROVIDES_FLATTENED_NON_DETERMINISM {
            dynasm!(ops
                ; mov rdx, rsp
                ;; before_call!(ops)
                ; push rdx
                ; push r9
                ; mov rax, QWORD (Context::<I>::nondeterminism_as_raw_ptr as *const ()).addr() as usize as isize as i64
                ; mov rdi, [rdx + (MachineState::CONTEXT_PTR_OFFSET as i32)]
                ; call rax
                ; pop r9
                ; pop rdx
                ;; after_call!(ops)
                ; mov [rdx + (MachineState::NON_DETERMINISM_RESPONSES_PTR_OFFSET as i32)], rax
            );
        }

        let instruction_labels = (0..program.len())
            .map(|_| ops.new_dynamic_label())
            .collect::<Vec<_>>();
        // Per-instruction landing offsets for each pass (offset from the buffer start,
        // i.e. from `->start`). `batched_offsets[i]` is set for known region entries
        // (pass 0); `eager_offsets[i]` is set for every instruction in the eager
        // fallback copy (pass 1). `initialized` records which PCs got a batched landing.
        let mut batched_offsets = vec![0usize; program.len()];
        let mut eager_offsets = vec![0usize; program.len()];
        let mut initialized: HashSet<usize> = HashSet::new();

        let ts_bound = cycles_bound.map(|cb| (cb as u64) * TIMESTAMP_STEP + INITIAL_TIMESTAMP);
        if let Some(b) = ts_bound {
            println!("Timestamp limit is 0x{:x}", b);
        }

        // Set RISCV_NO_FUSION to disable word-mem-run fusion (for A/B measurement).
        let fusion_enabled = std::env::var_os("RISCV_NO_FUSION").is_none();
        // RAW XMM-result forwarding is disabled: it measured ~0 (p5 shuffle isn't the
        // binding port) and it used RBP as its value cache, which now holds RV reg a5
        // (x15). Kept gated-off (the helper code is inert when `fwd` stays None).
        let fwd_enabled = false;
        // RAW-forward state (Some(rv) means RBP mirrors rv's value for the NEXT op) is
        // re-initialized per pass below.
        // Diagnostic port-pressure probe (dummy ops per pure-ALU instruction).
        let inj_stores: u32 = std::env::var("RISCV_INJECT_STORES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(0);
        let inj_p5: u32 = std::env::var("RISCV_INJECT_P5")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(0);
        let inj_alu: u32 = std::env::var("RISCV_INJECT_ALU")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(0);

        // Emit the program TWICE into the same buffer (see the jump_offsets table built
        // below): pass 0 = batched (lazy) copy whose landings are the known region
        // entries; pass 1 = a full per-instruction EAGER copy used as the dynamic-JALR
        // fallback (every PC is a valid, fully-materialized landing). A JALR whose target
        // is a known entry resolves into the batched copy; any other target resolves into
        // the eager copy, which re-enters batched code at its next control-flow transfer
        // (JAL/Branch always target known entries).
        for pass in 0..2 {
            let eager_mode = pass == 1;
            if eager_mode {
                // The batched body always terminates each region with a transfer, so it
                // never falls through into the eager copy; guard against it anyway.
                dynasm!(ops ; jmp ->exit_with_error);
            }

            let mut accum = Deferred::new();
            // `true` => the next emitted instruction starts a region and should get an
            // early-exit check (r8 is live there). pc 0 starts a region.
            let mut need_early_exit = true;
            let mut fwd: Option<u32> = None;

            let mut i = 0;
            while i < program.len() {
                let instr = program[i];
                let pc = i as u32 * 4;

                if eager_mode {
                    // Eager fallback copy: every instruction is an independently-
                    // addressable landing (no batching, no fusion; deferred bookkeeping
                    // is flushed right after each instruction below).
                    eager_offsets[i] = ops.offset().0;
                    if let Some(b) = ts_bound {
                        emit_early_exit!(ops, pc, b);
                    }
                } else {
                    // Known entry: a transfer can land here, so the deferred state of any
                    // incoming fall-through region must be materialized, and we bind the
                    // batched landing label.
                    if known[i] {
                        accum.flush(&mut ops);
                        dynasm!(ops ; => instruction_labels[i]);
                        batched_offsets[i] = ops.offset().0;
                        initialized.insert(i);
                        need_early_exit = true;
                        fwd = None; // a transfer can land here; RBP mirror is not valid
                    }
                    if need_early_exit {
                        if let Some(b) = ts_bound {
                            emit_early_exit!(ops, pc, b);
                        }
                        need_early_exit = false;
                    }
                }

                // Fuse a run of consecutive word loads/stores (same base, stride ±4)
                // into one observation: shared base load, deferred register timestamps,
                // single trace-chunk check. Folds the current deferred region in.
                if !eager_mode && fusion_enabled && matches!(instr.name, Op::Lw | Op::Sw) {
                    let run = word_mem_run_len(program, i, &known);
                    if run >= 2 {
                        fwd = None; // the mem-run emitter clobbers RBP
                        emit_word_mem_run(&mut ops, &mut accum, program, i, run);
                        need_early_exit = true;
                        i += run;
                        continue;
                    }
                }

                // RAW forwarding: consumer reads the previous op's mirrored value from
                // RBP. `fwd_in` is the producer's hint; `fwd` is reset and re-set by this
                // op's producer hook for the next instruction. Shadow the read helpers
                // with forwarding-aware closures so the arms need no changes.
                let fwd_in = fwd;
                fwd = None;
                let load = |ops: &mut x64::Assembler, x: u32| -> u8 { fl_load(ops, fwd_in, x) };
                let load_into =
                    |ops: &mut x64::Assembler, x: u32, dest: u8| fl_load_into(ops, fwd_in, x, dest);
                let load_abelian = |ops: &mut x64::Assembler, x: u32, y: u32, dest: u8| -> u8 {
                    fl_load_abelian(ops, fwd_in, x, y, dest)
                };
                let load_abelian_into =
                    |ops: &mut x64::Assembler, x: u32, y: u32, dest: u8, temp: u8| {
                        fl_load_abelian_into(ops, fwd_in, x, y, dest, temp)
                    };

                let rd = instr.rd as u32;
                let rs1 = instr.rs1 as u32;
                let rs2 = instr.rs2 as u32;
                let imm = instr.imm as i32;

                match instr.name {
                    // ---------------- pure ALU: defer all bookkeeping ----------------
                    Op::Add => {
                        let out = destination_gpr(rd);
                        if rs2 == 0 {
                            let source = load(&mut ops, rs1);
                            accum.touch_inc(rs1);
                            accum.touch_inc(0);
                            dynasm!(ops ; lea Rd(out), [Rd(source) + imm]);
                            accum.count(CounterType::AddSubLui, 1);
                        } else {
                            accum.touch_inc(rs1);
                            accum.touch_inc(rs2);
                            let other = load_abelian(&mut ops, rs1, rs2, out);
                            dynasm!(ops ; add Rd(out), Rd(other));
                            accum.count(CounterType::AddSubLui, 1);
                        }
                        accum.touch_bump(rd, 2);
                        store_result(&mut ops, rd);
                        fwd = maybe_forward(&mut ops, program, i, rd, &known, fwd_enabled);
                        inject_dummy(&mut ops, inj_stores, inj_p5, inj_alu);
                        i += 1;
                    }
                    Op::Sub => {
                        let out = destination_gpr(rd);
                        accum.touch_inc(rs1);
                        accum.touch_inc(rs2);
                        load_into(&mut ops, rs2, SCRATCH_REGISTER);
                        load_into(&mut ops, rs1, out);
                        dynasm!(ops ; sub Rd(out), Rd(SCRATCH_REGISTER));
                        accum.count(CounterType::AddSubLui, 1);
                        accum.touch_bump(rd, 2);
                        store_result(&mut ops, rd);
                        fwd = maybe_forward(&mut ops, program, i, rd, &known, fwd_enabled);
                        inject_dummy(&mut ops, inj_stores, inj_p5, inj_alu);
                        i += 1;
                    }
                    Op::Slt => {
                        let out = destination_gpr(rd);
                        if rs2 == 0 {
                            let source = load(&mut ops, rs1);
                            accum.touch_inc(rs1);
                            accum.touch_inc(0);
                            dynasm!(ops ; cmp Rd(source), imm ; setl Rb(out) ; movzx Rd(out), Rb(out));
                        } else {
                            accum.touch_inc(rs1);
                            accum.touch_inc(rs2);
                            load_into(&mut ops, rs2, SCRATCH_REGISTER);
                            load_into(&mut ops, rs1, out);
                            dynasm!(ops ; cmp Rd(out), Rd(SCRATCH_REGISTER) ; setl Rb(out) ; movzx Rd(out), Rb(out));
                        }
                        accum.count(CounterType::BranchSlt, 1);
                        accum.touch_bump(rd, 2);
                        store_result(&mut ops, rd);
                        fwd = maybe_forward(&mut ops, program, i, rd, &known, fwd_enabled);
                        inject_dummy(&mut ops, inj_stores, inj_p5, inj_alu);
                        i += 1;
                    }
                    Op::Sltu => {
                        let out = destination_gpr(rd);
                        if rs2 == 0 {
                            let source = load(&mut ops, rs1);
                            accum.touch_inc(rs1);
                            accum.touch_inc(0);
                            dynasm!(ops ; cmp Rd(source), imm ; setb Rb(out) ; movzx Rd(out), Rb(out));
                        } else {
                            accum.touch_inc(rs1);
                            accum.touch_inc(rs2);
                            load_into(&mut ops, rs2, SCRATCH_REGISTER);
                            load_into(&mut ops, rs1, out);
                            dynasm!(ops ; cmp Rd(out), Rd(SCRATCH_REGISTER) ; setb Rb(out) ; movzx Rd(out), Rb(out));
                        }
                        accum.count(CounterType::BranchSlt, 1);
                        accum.touch_bump(rd, 2);
                        store_result(&mut ops, rd);
                        fwd = maybe_forward(&mut ops, program, i, rd, &known, fwd_enabled);
                        inject_dummy(&mut ops, inj_stores, inj_p5, inj_alu);
                        i += 1;
                    }
                    Op::And => {
                        let out = destination_gpr(rd);
                        if rs2 == 0 {
                            load_into(&mut ops, rs1, out);
                            accum.touch_inc(rs1);
                            accum.touch_inc(0);
                            dynasm!(ops ; and Rd(out), imm);
                        } else {
                            accum.touch_inc(rs1);
                            accum.touch_inc(rs2);
                            let other = load_abelian(&mut ops, rs1, rs2, out);
                            dynasm!(ops ; and Rd(out), Rd(other));
                        }
                        accum.count(CounterType::ShiftBinaryCsr, 1);
                        accum.touch_bump(rd, 2);
                        store_result(&mut ops, rd);
                        fwd = maybe_forward(&mut ops, program, i, rd, &known, fwd_enabled);
                        inject_dummy(&mut ops, inj_stores, inj_p5, inj_alu);
                        i += 1;
                    }
                    Op::Or => {
                        let out = destination_gpr(rd);
                        if rs2 == 0 {
                            load_into(&mut ops, rs1, out);
                            accum.touch_inc(rs1);
                            accum.touch_inc(0);
                            dynasm!(ops ; or Rd(out), imm);
                        } else {
                            accum.touch_inc(rs1);
                            accum.touch_inc(rs2);
                            let other = load_abelian(&mut ops, rs1, rs2, out);
                            dynasm!(ops ; or Rd(out), Rd(other));
                        }
                        accum.count(CounterType::ShiftBinaryCsr, 1);
                        accum.touch_bump(rd, 2);
                        store_result(&mut ops, rd);
                        fwd = maybe_forward(&mut ops, program, i, rd, &known, fwd_enabled);
                        inject_dummy(&mut ops, inj_stores, inj_p5, inj_alu);
                        i += 1;
                    }
                    Op::Xor => {
                        let out = destination_gpr(rd);
                        if rs2 == 0 {
                            load_into(&mut ops, rs1, out);
                            accum.touch_inc(rs1);
                            accum.touch_inc(0);
                            dynasm!(ops ; xor Rd(out), imm);
                        } else {
                            accum.touch_inc(rs1);
                            accum.touch_inc(rs2);
                            let other = load_abelian(&mut ops, rs1, rs2, out);
                            dynasm!(ops ; xor Rd(out), Rd(other));
                        }
                        accum.count(CounterType::ShiftBinaryCsr, 1);
                        accum.touch_bump(rd, 2);
                        store_result(&mut ops, rd);
                        fwd = maybe_forward(&mut ops, program, i, rd, &known, fwd_enabled);
                        inject_dummy(&mut ops, inj_stores, inj_p5, inj_alu);
                        i += 1;
                    }
                    Op::Sll => {
                        let out = destination_gpr(rd);
                        if rs2 == 0 {
                            load_into(&mut ops, rs1, out);
                            accum.touch_inc(rs1);
                            accum.touch_inc(0);
                            dynasm!(ops ; shl Rd(out), imm as i8);
                        } else {
                            accum.touch_inc(rs1);
                            accum.touch_inc(rs2);
                            load_into(&mut ops, rs2, x64::Rq::RCX as u8);
                            load_into(&mut ops, rs1, out);
                            dynasm!(ops ; and rcx, 0x1f ; shl Rd(out), cl);
                        }
                        accum.count(CounterType::ShiftBinaryCsr, 1);
                        accum.touch_bump(rd, 2);
                        store_result(&mut ops, rd);
                        fwd = maybe_forward(&mut ops, program, i, rd, &known, fwd_enabled);
                        inject_dummy(&mut ops, inj_stores, inj_p5, inj_alu);
                        i += 1;
                    }
                    Op::Srl => {
                        let out = destination_gpr(rd);
                        if rs2 == 0 {
                            load_into(&mut ops, rs1, out);
                            accum.touch_inc(rs1);
                            accum.touch_inc(0);
                            dynasm!(ops ; shr Rd(out), imm as i8);
                        } else {
                            accum.touch_inc(rs1);
                            accum.touch_inc(rs2);
                            load_into(&mut ops, rs2, x64::Rq::RCX as u8);
                            load_into(&mut ops, rs1, out);
                            dynasm!(ops ; and rcx, 0x1f ; shr Rd(out), cl);
                        }
                        accum.count(CounterType::ShiftBinaryCsr, 1);
                        accum.touch_bump(rd, 2);
                        store_result(&mut ops, rd);
                        fwd = maybe_forward(&mut ops, program, i, rd, &known, fwd_enabled);
                        inject_dummy(&mut ops, inj_stores, inj_p5, inj_alu);
                        i += 1;
                    }
                    Op::Sra => {
                        let out = destination_gpr(rd);
                        if rs2 == 0 {
                            load_into(&mut ops, rs1, out);
                            accum.touch_inc(rs1);
                            accum.touch_inc(0);
                            dynasm!(ops ; sar Rd(out), imm as i8);
                        } else {
                            accum.touch_inc(rs1);
                            accum.touch_inc(rs2);
                            load_into(&mut ops, rs2, x64::Rq::RCX as u8);
                            load_into(&mut ops, rs1, out);
                            dynasm!(ops ; and rcx, 0x1f ; sar Rd(out), cl);
                        }
                        accum.count(CounterType::ShiftBinaryCsr, 1);
                        accum.touch_bump(rd, 2);
                        store_result(&mut ops, rd);
                        fwd = maybe_forward(&mut ops, program, i, rd, &known, fwd_enabled);
                        inject_dummy(&mut ops, inj_stores, inj_p5, inj_alu);
                        i += 1;
                    }
                    Op::Auipc => {
                        let out = destination_gpr(rd);
                        accum.pre_bump_touch(1, 0);
                        accum.bump(1);
                        dynasm!(ops ; mov Rd(out), (pc.wrapping_add(instr.imm)) as i32);
                        accum.count(CounterType::AddSubLui, 1);
                        accum.touch_bump(rd, 2);
                        store_result(&mut ops, rd);
                        fwd = maybe_forward(&mut ops, program, i, rd, &known, fwd_enabled);
                        inject_dummy(&mut ops, inj_stores, inj_p5, inj_alu);
                        i += 1;
                    }
                    Op::Mul => {
                        let out = destination_gpr(rd);
                        accum.touch_inc(rs1);
                        accum.touch_inc(rs2);
                        let other = load_abelian(&mut ops, rs1, rs2, out);
                        dynasm!(ops ; imul Rd(out), Rd(other));
                        accum.count(CounterType::MulDiv, 1);
                        accum.touch_bump(rd, 2);
                        store_result(&mut ops, rd);
                        fwd = maybe_forward(&mut ops, program, i, rd, &known, fwd_enabled);
                        inject_dummy(&mut ops, inj_stores, inj_p5, inj_alu);
                        i += 1;
                    }
                    Op::Mulhu => {
                        let out = destination_gpr(rd);
                        accum.touch_inc(rs1);
                        accum.touch_inc(rs2);
                        load_into(&mut ops, rs1, x64::Rq::RAX as u8);
                        let other = load(&mut ops, rs2);
                        dynasm!(ops ; mul Rd(other));
                        if out != x64::Rq::RDX as u8 {
                            dynasm!(ops ; mov Rd(out), edx);
                        }
                        accum.count(CounterType::MulDiv, 1);
                        accum.touch_bump(rd, 2);
                        store_result(&mut ops, rd);
                        fwd = maybe_forward(&mut ops, program, i, rd, &known, fwd_enabled);
                        inject_dummy(&mut ops, inj_stores, inj_p5, inj_alu);
                        i += 1;
                    }
                    Op::Divu => {
                        let out = destination_gpr(rd);
                        accum.touch_inc(rs1);
                        accum.touch_inc(rs2);
                        load_into(&mut ops, rs1, x64::Rq::RAX as u8);
                        load_into(&mut ops, rs2, SCRATCH_REGISTER);
                        dynasm!(ops ; xor rdx, rdx ; div Rd(SCRATCH_REGISTER));
                        if out != x64::Rq::RAX as u8 {
                            dynasm!(ops ; mov Rd(out), eax);
                        }
                        accum.count(CounterType::MulDiv, 1);
                        accum.touch_bump(rd, 2);
                        store_result(&mut ops, rd);
                        fwd = maybe_forward(&mut ops, program, i, rd, &known, fwd_enabled);
                        inject_dummy(&mut ops, inj_stores, inj_p5, inj_alu);
                        i += 1;
                    }
                    Op::Remu => {
                        let out = destination_gpr(rd);
                        accum.touch_inc(rs1);
                        accum.touch_inc(rs2);
                        load_into(&mut ops, rs1, x64::Rq::RAX as u8);
                        load_into(&mut ops, rs2, SCRATCH_REGISTER);
                        dynasm!(ops ; xor rdx, rdx ; div Rd(SCRATCH_REGISTER));
                        if out != x64::Rq::RDX as u8 {
                            dynasm!(ops ; mov Rd(out), edx);
                        }
                        accum.count(CounterType::MulDiv, 1);
                        accum.touch_bump(rd, 2);
                        store_result(&mut ops, rd);
                        fwd = maybe_forward(&mut ops, program, i, rd, &known, fwd_enabled);
                        inject_dummy(&mut ops, inj_stores, inj_p5, inj_alu);
                        i += 1;
                    }
                    Op::Nop => {
                        accum.touch_inc(0);
                        accum.touch_inc(0);
                        accum.touch_bump(0, 2);
                        accum.count(CounterType::AddSubLui, 1);
                        i += 1;
                    }
                    Op::ZimopAdd | Op::ZimopSub | Op::ZimopMul => {
                        let out = destination_gpr(rd);
                        assert!(rd != 0);
                        assert!(rs1 != 0);
                        match instr.name {
                            Op::ZimopAdd => {
                                accum.touch_inc(rs1);
                                accum.touch_inc(rs2);
                                if rs2 == 0 {
                                    load_into(&mut ops, rs1, out);
                                    dynasm!(ops
                                        ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                        ; mov edx, Rd(out)
                                        ; sub edx, 0x7fff_ffffu32 as i32
                                        ; cmovnc Rd(out), edx
                                        ; sub Rd(SCRATCH_REGISTER), (0x7fff_ffffu32 * 2) as i32
                                        ; cmovnc Rd(out), Rd(SCRATCH_REGISTER)
                                    );
                                } else {
                                    load_abelian_into(&mut ops, rs1, rs2, out, x64::Rq::RDX as u8);
                                    dynasm!(ops
                                        ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                        ; and Rd(out), 0x7fff_ffffu32 as i32
                                        ; shr Rd(SCRATCH_REGISTER), 31i8
                                        ; add Rd(out), Rd(SCRATCH_REGISTER)
                                        ; mov Rd(SCRATCH_REGISTER), edx
                                        ; and edx, 0x7fff_ffffu32 as i32
                                        ; shr Rd(SCRATCH_REGISTER), 31i8
                                        ; add edx, Rd(SCRATCH_REGISTER)
                                        ; add Rd(out), edx
                                        ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                        ; and Rd(out), 0x7fff_ffffu32 as i32
                                        ; shr Rd(SCRATCH_REGISTER), 31i8
                                        ; add Rd(out), Rd(SCRATCH_REGISTER)
                                        ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                        ; sub Rd(SCRATCH_REGISTER), 0x7fff_ffffu32 as i32
                                        ; cmovnc Rd(out), Rd(SCRATCH_REGISTER)
                                    );
                                }
                                accum.count(CounterType::AddSubLui, 1);
                            }
                            Op::ZimopSub => {
                                accum.touch_inc(rs1);
                                accum.touch_inc(rs2);
                                assert!(rs1 != 0);
                                assert!(rs2 != 0);
                                load_into(&mut ops, rs2, x64::Rq::RDX as u8);
                                load_into(&mut ops, rs1, out);
                                dynasm!(ops
                                    ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                    ; and Rd(out), 0x7fff_ffffu32 as i32
                                    ; shr Rd(SCRATCH_REGISTER), 31i8
                                    ; add Rd(out), Rd(SCRATCH_REGISTER)
                                    ; mov Rd(SCRATCH_REGISTER), edx
                                    ; and edx, 0x7fff_ffffu32 as i32
                                    ; shr Rd(SCRATCH_REGISTER), 31i8
                                    ; add edx, Rd(SCRATCH_REGISTER)
                                    ; sub Rd(out), edx
                                    ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                    ; and Rd(out), 0x7fff_ffffu32 as i32
                                    ; shr Rd(SCRATCH_REGISTER), 31i8
                                    ; sub Rd(out), Rd(SCRATCH_REGISTER)
                                    ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                    ; sub Rd(SCRATCH_REGISTER), 0x7fff_ffffu32 as i32
                                    ; cmovnc Rd(out), Rd(SCRATCH_REGISTER)
                                );
                                accum.count(CounterType::AddSubLui, 1);
                            }
                            Op::ZimopMul => {
                                accum.touch_inc(rs1);
                                accum.touch_inc(rs2);
                                assert!(rs1 != 0);
                                assert!(rs2 != 0);
                                load_abelian_into(&mut ops, rs1, rs2, out, x64::Rq::RDX as u8);
                                dynasm!(ops
                                    ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                    ; and Rd(out), 0x7fff_ffffu32 as i32
                                    ; shr Rd(SCRATCH_REGISTER), 31i8
                                    ; add Rd(out), Rd(SCRATCH_REGISTER)
                                    ; mov Rd(SCRATCH_REGISTER), edx
                                    ; and edx, 0x7fff_ffffu32 as i32
                                    ; shr Rd(SCRATCH_REGISTER), 31i8
                                    ; add edx, Rd(SCRATCH_REGISTER)
                                    ; imul Rq(out), rdx
                                    ; mov rdx, Rq(out)
                                    ; shr rdx, 31i8
                                    ; and Rd(out), 0x7fff_ffffu32 as i32
                                    ; add Rd(out), edx
                                    ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                    ; and Rd(out), 0x7fff_ffffu32 as i32
                                    ; shr Rd(SCRATCH_REGISTER), 31i8
                                    ; add Rd(out), Rd(SCRATCH_REGISTER)
                                    ; mov Rd(SCRATCH_REGISTER), Rd(out)
                                    ; sub Rd(SCRATCH_REGISTER), 0x7fff_ffffu32 as i32
                                    ; cmovnc Rd(out), Rd(SCRATCH_REGISTER)
                                );
                                accum.count(CounterType::AddSubLui, 1);
                            }
                            _ => unreachable!(),
                        }
                        accum.touch_bump(rd, 2);
                        store_result(&mut ops, rd);
                        fwd = maybe_forward(&mut ops, program, i, rd, &known, fwd_enabled);
                        inject_dummy(&mut ops, inj_stores, inj_p5, inj_alu);
                        i += 1;
                    }

                    // ---------------- loads: flush, then eager (live r8) ----------------
                    Op::Lb | Op::Lbu | Op::Lh | Op::Lhu | Op::Lw => {
                        accum.flush(&mut ops);
                        let out = destination_gpr(rd);
                        let address = load(&mut ops, rs1);
                        if matches!(instr.name, Op::Lw) {
                            dynasm!(ops ; lea Rd(SCRATCH_REGISTER), [Rd(address) + imm]);
                            touch_register_and_increment_timestamp!(ops, rs1);
                            dynasm!(ops
                                ; mov Rd(out), DWORD [rsi + Rq(SCRATCH_REGISTER)]
                                ; mov rdx, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 2 * Rq(SCRATCH_REGISTER)]
                                ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 2 * Rq(SCRATCH_REGISTER)], r8
                                ; mov [rdi + r9 * 4], Rd(out)
                                ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rdx
                            );
                            bump_timestamp!(ops, 1);
                            record_circuit_type(&mut ops, CounterType::MemWord, 1);
                        } else {
                            dynasm!(ops
                                ; lea Rd(SCRATCH_REGISTER), [Rd(address) + imm]
                                ; mov rdx, Rq(SCRATCH_REGISTER)
                                ; shr rdx, 2
                            );
                            touch_register_and_increment_timestamp!(ops, rs1);
                            match instr.name {
                                Op::Lb => {
                                    dynasm!(ops ; movsx Rd(out), BYTE [rsi + Rq(SCRATCH_REGISTER)])
                                }
                                Op::Lbu => {
                                    dynasm!(ops ; movzx Rd(out), BYTE [rsi + Rq(SCRATCH_REGISTER)])
                                }
                                Op::Lh => {
                                    dynasm!(ops ; movsx Rd(out), WORD [rsi + Rq(SCRATCH_REGISTER)])
                                }
                                Op::Lhu => {
                                    dynasm!(ops ; movzx Rd(out), WORD [rsi + Rq(SCRATCH_REGISTER)])
                                }
                                _ => unreachable!(),
                            }
                            dynasm!(ops
                                ; mov Rd(SCRATCH_REGISTER), DWORD [rsi + 4 * rdx]
                                ; mov [rdi + r9 * 4], Rd(SCRATCH_REGISTER) // old word value -> trace
                                ; mov Rq(SCRATCH_REGISTER), [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx] // old ts (reuse scratch; frees RBP)
                                ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rdx], r8
                                ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], Rq(SCRATCH_REGISTER)
                            );
                            bump_timestamp!(ops, 1);
                            record_circuit_type(&mut ops, CounterType::MemSubword, 1);
                        }
                        touch_register_and_bump_timestamp!(ops, rd, 2);
                        store_result(&mut ops, rd);
                        let pc_for_trace = pc + 4;
                        increment_trace!(ops, pc_for_trace);
                        need_early_exit = true;
                        i += 1;
                    }

                    // ---------------- stores: flush, then eager ----------------
                    Op::Sb | Op::Sh | Op::Sw => {
                        accum.flush(&mut ops);
                        let address = load(&mut ops, rs1);
                        dynasm!(ops ; lea Rd(SCRATCH_REGISTER), [Rd(address) + imm]);
                        if matches!(instr.name, Op::Sw) {
                            let value = load(&mut ops, rs2);
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, rs2);
                            dynasm!(ops
                                ; mov eax, DWORD [rsi + Rq(SCRATCH_REGISTER)]
                                ; mov DWORD [rsi + Rq(SCRATCH_REGISTER)], Rd(value) // store new value (frees its register)
                                ; mov rdx, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 2 * Rq(SCRATCH_REGISTER)] // RDX free; frees RBP
                                ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 2 * Rq(SCRATCH_REGISTER)], r8
                                ; mov [rdi + r9 * 4], eax
                                ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rdx
                            );
                        } else {
                            // subword store: word index -> rax; read + trace the old word value
                            // BEFORE loading the new value, so {rax,rcx,rdx} suffice (no RBP).
                            dynasm!(ops ; mov rax, Rq(SCRATCH_REGISTER) ; shr rax, 2);
                            touch_register_and_increment_timestamp!(ops, rs1);
                            touch_register_and_increment_timestamp!(ops, rs2);
                            dynasm!(ops
                                ; mov edx, DWORD [rsi + 4 * rax] // old word value
                                ; mov [rdi + r9 * 4], edx // -> trace
                            );
                            let value = load(&mut ops, rs2);
                            match instr.name {
                                Op::Sb => {
                                    dynasm!(ops ; mov BYTE [rsi + Rq(SCRATCH_REGISTER)], Rb(value))
                                }
                                Op::Sh => {
                                    dynasm!(ops ; mov WORD [rsi + Rq(SCRATCH_REGISTER)], Rw(value))
                                }
                                _ => unreachable!(),
                            }
                            dynasm!(ops
                                ; mov rdx, [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rax] // old ts (RDX free)
                                ; mov [rsi + (MemoryHolder::TIMESTAMPS_OFFSET as i32) + 8 * rax], r8
                                ; mov [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], rdx
                            );
                        }
                        bump_timestamp!(ops, 2);
                        record_circuit_type(
                            &mut ops,
                            if matches!(instr.name, Op::Sw) {
                                CounterType::MemWord
                            } else {
                                CounterType::MemSubword
                            },
                            1,
                        );
                        let pc_for_trace = pc + 4;
                        increment_trace!(ops, pc_for_trace);
                        need_early_exit = true;
                        i += 1;
                    }

                    // ---------------- control flow: fold, flush, bare transfer ----------------
                    Op::Jal => {
                        let out = destination_gpr(rd);
                        if rd != 0 {
                            accum.pre_bump_touch(1, 0);
                            dynasm!(ops ; mov Rd(out), (pc + 4) as i32);
                            store_result(&mut ops, rd);
                            accum.pre_bump_touch(1, rd);
                        } else {
                            accum.pre_bump_touch(2, 0);
                        }
                        accum.bump(2);
                        accum.count(CounterType::BranchSlt, 1);
                        accum.flush(&mut ops);

                        let offset = imm;
                        let jump_target = pc as i32 + offset;
                        if offset == 0 {
                            dynasm!(ops
                                ;; machine_state_store_pc!(ops, rsp, pc)
                                ; jmp ->quit_impl
                            );
                        } else if jump_target % 4 != 0 {
                            panic!("Unaligned jump destination");
                        } else {
                            let target_idx = (jump_target / 4) as usize;
                            assert!(
                                known[target_idx],
                                "JAL target pc=0x{:x} is not a known region entry",
                                jump_target
                            );
                            dynasm!(ops ; jmp => instruction_labels[target_idx]);
                        }
                        need_early_exit = true;
                        i += 1;
                    }
                    Op::Jalr => {
                        let out = destination_gpr(rd);
                        let offset = imm;
                        accum.touch_inc(rs1);
                        load_into(&mut ops, rs1, SCRATCH_REGISTER);
                        dynasm!(ops
                            ; add Rd(SCRATCH_REGISTER), offset
                            ; test Rd(SCRATCH_REGISTER), 2
                            ; jnz >misaligned
                            ; shr Rd(SCRATCH_REGISTER), 2
                            ; lea rdx, [->jump_offsets]
                            ; mov rax, [rdx + Rq(SCRATCH_REGISTER) * 8]
                            ; lea rdx, [->start]
                            ; add rdx, rax
                        );
                        if rd != 0 {
                            accum.touch_inc(0);
                            dynasm!(ops ; mov Rd(out), (pc + 4) as i32);
                            accum.touch_bump(rd, 2);
                            store_result(&mut ops, rd);
                        } else {
                            accum.pre_bump_touch(1, 0);
                            accum.bump(2);
                        }
                        accum.count(CounterType::BranchSlt, 1);
                        accum.flush(&mut ops);
                        dynasm!(ops
                            ; jmp rdx
                            ; misaligned:
                            ; mov esi, Rd(SCRATCH_REGISTER)
                            ;; emit_misaligned_runtime_error!(ops)
                        );
                        need_early_exit = true;
                        i += 1;
                    }
                    Op::Branch => {
                        let jump_target = pc as i32 + imm;
                        if jump_target % 4 != 0 {
                            panic!("Unaligned jump destination");
                        }
                        let target_idx = (jump_target / 4) as usize;
                        assert!(
                            known[target_idx],
                            "BRANCH target pc=0x{:x} is not a known region entry",
                            jump_target
                        );
                        let a = load(&mut ops, rs1);
                        load_into(&mut ops, rs2, SCRATCH_REGISTER);
                        accum.touch_inc(rs1);
                        accum.touch_inc(rs2);
                        accum.touch_bump(0, 2);
                        accum.count(CounterType::BranchSlt, 1);
                        accum.flush(&mut ops);
                        dynasm!(ops ; cmp Rd(a), Rd(SCRATCH_REGISTER));
                        match rd {
                            0 => dynasm!(ops ; je => instruction_labels[target_idx]),
                            1 => dynasm!(ops ; jne => instruction_labels[target_idx]),
                            4 => dynasm!(ops ; jl => instruction_labels[target_idx]),
                            5 => dynasm!(ops ; jge => instruction_labels[target_idx]),
                            6 => dynasm!(ops ; jb => instruction_labels[target_idx]),
                            7 => dynasm!(ops ; jae => instruction_labels[target_idx]),
                            _ => panic!("Unknown BRANCH funct3 {}", rd),
                        }
                        need_early_exit = true;
                        i += 1;
                    }

                    // ---------------- non-determinism (observations): flush, then eager ----------------
                    Op::ZicsrNonDeterminismRead => {
                        assert!(rs1 == 0);
                        assert!(rd != 0);
                        accum.flush(&mut ops);
                        let out = destination_gpr(rd);
                        if I::PROVIDES_FLATTENED_NON_DETERMINISM {
                            pre_bump_timestamp_and_touch!(ops, 1, 0);
                            dynasm!(ops
                                ; mov rcx, [rsp + (MachineState::NON_DETERMINISM_RESPONSES_PTR_OFFSET as i32)]
                                ; mov Rd(out), [rcx]
                                ; add rcx, 4
                                ; mov [rsp + (MachineState::NON_DETERMINISM_RESPONSES_PTR_OFFSET as i32)], rcx
                            );
                            store_result(&mut ops, rd);
                            pre_bump_timestamp_and_touch!(ops, 1, rd);
                            bump_timestamp!(ops, 2);
                            record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                        } else {
                            pre_bump_timestamp_and_touch!(ops, 1, 0);
                            dynasm!(ops
                                ; mov rdx, rsp
                                ;; before_call!(ops)
                                ; push rdx
                                ; push r9
                                ; mov rax, QWORD (Context::<I>::read_nondeterminism as *const ()).addr() as usize as isize as i64
                                ; mov rdi, [rdx + (MachineState::CONTEXT_PTR_OFFSET as i32)]
                                ; call rax
                                ; pop r9
                                ; pop rdx
                                ;; after_call!(ops)
                                ; mov Rd(out), eax
                                ; mov [rdi + r9 * 4], eax
                                ; mov QWORD [rdi + r9 * 8 + (TraceChunk::TIMESTAMPS_OFFSET as i32)], 0
                            );
                            store_result(&mut ops, rd);
                            pre_bump_timestamp_and_touch!(ops, 1, rd);
                            bump_timestamp!(ops, 2);
                            record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                        }
                        let pc_for_trace = pc + 4;
                        increment_trace!(ops, pc_for_trace);
                        need_early_exit = true;
                        i += 1;
                    }
                    Op::ZicsrNonDeterminismWrite => {
                        assert!(rs1 != 0);
                        assert!(rd == 0);
                        accum.flush(&mut ops);
                        if I::PROVIDES_FLATTENED_NON_DETERMINISM {
                            touch_register_and_increment_timestamp!(ops, rs1);
                            pre_bump_timestamp_and_touch!(ops, 1, 0);
                            bump_timestamp!(ops, 2);
                            record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                        } else {
                            load_into(&mut ops, rs1, SCRATCH_REGISTER);
                            touch_register_and_increment_timestamp!(ops, rs1);
                            dynasm!(ops
                                ; mov rdx, rsp
                                ;; before_call!(ops)
                                ; push rdx
                                ; push r9
                                ; mov rax, QWORD (Context::<I>::write_nondeterminism as *const ()).addr() as usize as isize as i64
                                ; mov rdi, [rdx + (MachineState::CONTEXT_PTR_OFFSET as i32)]
                                ; mov rdx, rsi
                                ; mov esi, Rd(SCRATCH_REGISTER)
                                ; call rax
                                ; pop r9
                                ; pop rdx
                                ;; after_call!(ops)
                            );
                            pre_bump_timestamp_and_touch!(ops, 1, 0);
                            bump_timestamp!(ops, 2);
                            record_circuit_type(&mut ops, CounterType::AddSubLui, 1);
                        }
                        need_early_exit = true;
                        i += 1;
                    }

                    // ---------------- delegations: flush, then eager (advances i) ----------------
                    Op::ZicsrDelegation => {
                        accum.flush(&mut ops);
                        let mut cycles_taken = 0;
                        let function: *const () = match instr.imm {
                            BLAKE2S_DELEGATION_CSR_REGISTER => {
                                let mut num_calls = 0;
                                for j in 1..=10 {
                                    if program[i + j] == program[i] {
                                        continue;
                                    } else {
                                        num_calls = j;
                                        break;
                                    }
                                }
                                assert!(num_calls == 7 || num_calls == 10);
                                i += num_calls;
                                cycles_taken = num_calls;
                                record_circuit_type(
                                    &mut ops,
                                    CounterType::BlakeDelegation,
                                    num_calls as u16,
                                );
                                process_csr::<BLAKE2S_DELEGATION_CSR_REGISTER> as *const ()
                            }
                            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER => {
                                record_circuit_type(&mut ops, CounterType::BigintDelegation, 1);
                                i += 1;
                                cycles_taken = 1;
                                process_csr::<BIGINT_OPS_WITH_CONTROL_CSR_REGISTER> as *const ()
                            }
                            KECCAK_SPECIAL5_CSR_REGISTER => {
                                let mut num_calls = 0;
                                for j in 1..=NUM_DELEGATION_CALLS_FOR_KECCAK_F1600 {
                                    if program[i + j] == program[i] {
                                        continue;
                                    } else {
                                        num_calls = j;
                                        break;
                                    }
                                }
                                assert_eq!(num_calls, NUM_DELEGATION_CALLS_FOR_KECCAK_F1600);
                                i += num_calls;
                                cycles_taken = num_calls;
                                record_circuit_type(
                                    &mut ops,
                                    CounterType::KeccakDelegation,
                                    num_calls as u16,
                                );
                                process_csr::<KECCAK_SPECIAL5_CSR_REGISTER> as *const ()
                            }
                            other_csrs @ _ => panic!("Unknown CSR {}", other_csrs),
                        };
                        assert!(i <= program.len());
                        assert!(cycles_taken <= u16::MAX as usize);
                        record_circuit_type(&mut ops, CounterType::AddSubLui, cycles_taken as u16);
                        assert_eq!(rs1, 0);
                        assert_eq!(rd, 0);
                        pre_bump_timestamp_and_touch!(ops, 2, 0);
                        bump_timestamp!(ops, 1);
                        let pc_for_trace = pc + ((4 * cycles_taken) as u32);
                        dynasm!(ops
                            ; mov rdx, rsp
                            ;; before_call!(ops)
                            ; push rdx
                            ; mov [rdi + (TraceChunk::LEN_OFFSET as i32)], r9
                            ; sub rsp, 8
                            ; mov rax, QWORD (function as *const ()).addr() as usize as isize as i64
                            ; call rax
                            ; add rsp, 8
                            ; pop rdx
                            ;; after_call!(ops)
                            ; mov r9, [rdi + (TraceChunk::LEN_OFFSET as i32)]
                            ;; check_to_save_trace!(ops, pc_for_trace)
                        );
                        bump_timestamp!(ops, 1);
                        need_early_exit = true;
                    }

                    _ => {
                        accum.flush(&mut ops);
                        emit_execution_panic!(ops, pc);
                        need_early_exit = true;
                        i += 1;
                    }
                }

                if eager_mode {
                    // Materialize this instruction's deferred bookkeeping now, so every PC
                    // in the eager copy is a fully-materialized JALR landing.
                    accum.flush(&mut ops);
                }
            }
            assert_eq!(i, program.len());
        }

        emit_runtime_error!(ops);

        dynasm!(ops
            ; ->exit_with_execution_panic:
            ; mov rdx, rsp
            ; mov [rdx + (MachineState::PC_OFFSET as i32)], r9d
            ;; save_machine_state!(ops)
            ; mov rax, QWORD (print_runtime_panic as *const ()).addr() as usize as isize as i64
            ; mov rdi, r8
            ; mov rsi, rdx
            ; call rax
        );
        dynasm!(ops
            ; ->exit_on_misaligned:
            ; mov rax, QWORD (print_misaligned as *const ()).addr() as usize as isize as i64
            ; mov rdi, r8
            ; call rax
        );
        let exit_with_error_offset = ops.offset().0;
        dynasm!(ops
            ; ->exit_with_error:
            ; mov rax, QWORD (print_complaint as *const ()).addr() as usize as isize as i64
            ; mov rdi, r8
            ; call rax
        );

        // Dynamic JALR dispatch table (STAGE B): a known region entry resolves to its
        // batched landing; every other PC resolves to its eager-copy landing (the
        // fallback). The rare PC with no eager landing — the interior of a collapsed
        // delegation block, which is never a valid jump target — traps.
        let jump_offsets: Vec<usize> = (0..program.len())
            .map(|idx| {
                if initialized.contains(&idx) {
                    batched_offsets[idx]
                } else if eager_offsets[idx] != 0 {
                    eager_offsets[idx]
                } else {
                    exit_with_error_offset
                }
            })
            .collect();

        dynasm!(ops
            ; ->jump_offsets:
            ; .bytes jump_offsets.into_iter().flat_map(|x| x.to_le_bytes())
        );
        dynasm!(ops
            ; .align 16
            ; ->cve_one_q0:
            ; .bytes 1u64.to_le_bytes()
            ; .bytes 0u64.to_le_bytes()
            ; ->cve_one_q1:
            ; .bytes 0u64.to_le_bytes()
            ; .bytes 1u64.to_le_bytes()
        );

        let receive_trace_fn = Context::<I>::receive_trace;
        receive_trace!(ops, receive_trace_fn);
        let quit_trace_fn = Context::<I>::receive_final_trace_piece;
        quit!(ops, quit_trace_fn);

        let code = ops.finalize().unwrap();
        Self {
            code,
            start,
            _marker: core::marker::PhantomData,
        }
    }
}

// ---------------------------------------------------------------------------
// Test/bench run harness for the lazy path (mirrors
// `run_alternative_simulator_with_last_snapshot`, but builds the control-flow
// artifact and constructs via `preprocess_bytecode_lazy`).
// ---------------------------------------------------------------------------

impl<'a> JittedCode<FlattenedContextImpl<'a>> {
    /// Lazy-path analogue of `run_with_flattened_context` (full block, no cycle
    /// bound). Used for performance measurement; prints the simulator MHz.
    pub fn run_with_flattened_context_lazy(
        program: &[u32],
        non_determinism_responses: &'a [u32],
        initial_memory: &[u32],
        cycles_bound: Option<u32>,
        artifact: &ControlFlowArtifact,
    ) -> (MachineState, Box<MemoryHolder>) {
        let mut context = Context::<FlattenedContextImpl<'_>> {
            implementation: FlattenedContextImpl::new(non_determinism_responses),
        };

        let mut memory: Box<MemoryHolder> =
            unsafe { Box::<MemoryHolder>::new_zeroed().assume_init() };
        let mut trace: Box<TraceChunk> = unsafe { Box::<TraceChunk>::new_zeroed().assume_init() };

        let instructions = crate::ir::simple_instruction_set::preprocess_bytecode::<
            crate::ir::FullUnsignedMachineDecoderConfig,
            false,
        >(program);
        let runner = Self::preprocess_bytecode_lazy(&instructions, artifact, cycles_bound);

        runner.run(
            &mut context,
            memory.as_mut(),
            unsafe { NonNull::new_unchecked(trace.as_mut() as *mut _) },
            initial_memory,
        );

        let final_state = context
            .implementation
            .take_final_state()
            .expect("must finish execution");

        (final_state, memory)
    }
}

impl<N: NonDeterminismCSRSource> JittedCode<DefaultContextImpl<'_, N>> {
    pub fn run_alternative_simulator_with_last_snapshot_lazy(
        program: &[u32],
        non_determinism_source: &mut N,
        initial_memory: &[u32],
        cycles_bound: Option<u32>,
        artifact: &ControlFlowArtifact,
    ) -> (MachineState, Box<MemoryHolder>, Box<TraceChunk>) {
        let mut context = Context::<DefaultContextImpl<'_, N>> {
            implementation: DefaultContextImpl::new(non_determinism_source),
        };

        let mut memory: Box<MemoryHolder> =
            unsafe { Box::<MemoryHolder>::new_zeroed().assume_init() };
        let mut trace: Box<TraceChunk> = unsafe { Box::<TraceChunk>::new_zeroed().assume_init() };

        let instructions = crate::ir::simple_instruction_set::preprocess_bytecode::<
            crate::ir::FullUnsignedMachineDecoderConfig,
            false,
        >(program);
        let runner = Self::preprocess_bytecode_lazy(&instructions, artifact, cycles_bound);

        runner.run(
            &mut context,
            memory.as_mut(),
            unsafe { NonNull::new_unchecked(trace.as_mut() as *mut _) },
            initial_memory,
        );

        let final_state = context
            .implementation
            .take_final_state()
            .expect("must finish execution");

        (final_state, memory, trace)
    }
}
