//! Coverage for the 4 Gb JIT configuration.
//!
//! Above 1 Gb the memory-to-timestamps offset no longer fits an x86-64 displacement,
//! so every memory access rebases RSI against an RIP-relative constant instead of
//! folding the offset into the operand. That is a separate instruction sequence from
//! the one every other configuration uses, and these tests are the only thing that
//! executes it.
//!
//! A 4 Gb image needs a 12 Gb holder, which is more than a CI box wants to commit.
//! `MemoryHolder::allocate_zeroed` is generic over the allocator, so the tests hand it
//! anonymous `MAP_NORESERVE` pages: zero-filled, and committed only as they are
//! touched. The programs here touch a handful of pages, so the runs cost megabytes.
//!
//! The shape of each test is differential. The same program runs at 1 Gb, where the
//! displacement path is known good, and at 4 Gb with its base address moved, and the
//! two runs have to agree on the final registers, the register timestamps, the whole
//! trace chunk, and the memory and timestamp words around the base.
//!
//! The short programs pin the addressing, but they execute a couple of dozen
//! instructions against a trace chunk of `TRACE_CHUNK_LEN`, so they never fill one and
//! never reach the flush path. `real_block_full_matches_medium` covers that: it is the
//! only test here that runs the rebase under sustained load.
#![cfg(all(target_arch = "x86_64", target_os = "linux", feature = "jit"))]
#![feature(allocator_api)]

use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::jit::*;
use std::alloc::{AllocError, Allocator, Layout};
use std::path::Path;
use std::ptr::NonNull;

extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
    fn munmap(addr: *mut u8, len: usize) -> i32;
}
const PROT_READ: i32 = 1;
const PROT_WRITE: i32 = 2;
const MAP_PRIVATE: i32 = 2;
const MAP_ANONYMOUS: i32 = 0x20;
const MAP_NORESERVE: i32 = 0x4000;

/// Hands out anonymous pages without reserving backing store, so the 12 Gb holder a
/// 4 Gb configuration needs costs only the pages a test actually writes.
#[derive(Clone, Copy)]
struct LazyMmap;

unsafe impl Allocator for LazyMmap {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        // over-allocate by one alignment unit, then trim both ends back
        let total = layout.size() + layout.align();
        let p = unsafe {
            mmap(
                core::ptr::null_mut(),
                total,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE,
                -1,
                0,
            )
        };
        if p as isize == -1 {
            return Err(AllocError);
        }
        let addr = p as usize;
        let aligned = (addr + layout.align() - 1) & !(layout.align() - 1);
        let end = addr + total;
        let aligned_end = aligned + layout.size();
        unsafe {
            if aligned > addr {
                munmap(p, aligned - addr);
            }
            if end > aligned_end {
                munmap(aligned_end as *mut u8, end - aligned_end);
            }
        }
        Ok(NonNull::slice_from_raw_parts(
            NonNull::new(aligned as *mut u8).unwrap(),
            layout.size(),
        ))
    }

    fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        // anonymous mappings are already zero filled
        self.allocate(layout)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        munmap(ptr.as_ptr(), layout.size());
    }
}

fn lui(rd: u32, imm20: u32) -> u32 {
    (imm20 << 12) | (rd << 7) | 0x37
}
fn addi(rd: u32, rs1: u32, imm: i32) -> u32 {
    (((imm as u32) & 0xfff) << 20) | (rs1 << 15) | (rd << 7) | 0x13
}
fn load(f3: u32, rd: u32, rs1: u32, imm: i32) -> u32 {
    (((imm as u32) & 0xfff) << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | 0x03
}
fn store(f3: u32, rs2: u32, rs1: u32, imm: i32) -> u32 {
    let imm = imm as u32;
    (((imm >> 5) & 0x7f) << 25)
        | (rs2 << 20)
        | (rs1 << 15)
        | (f3 << 12)
        | ((imm & 0x1f) << 7)
        | 0x23
}
fn lb(rd: u32, rs1: u32, imm: i32) -> u32 {
    load(0b000, rd, rs1, imm)
}
fn lh(rd: u32, rs1: u32, imm: i32) -> u32 {
    load(0b001, rd, rs1, imm)
}
fn lw(rd: u32, rs1: u32, imm: i32) -> u32 {
    load(0b010, rd, rs1, imm)
}
fn lbu(rd: u32, rs1: u32, imm: i32) -> u32 {
    load(0b100, rd, rs1, imm)
}
fn lhu(rd: u32, rs1: u32, imm: i32) -> u32 {
    load(0b101, rd, rs1, imm)
}
fn sb(rs2: u32, rs1: u32, imm: i32) -> u32 {
    store(0b000, rs2, rs1, imm)
}
fn sh(rs2: u32, rs1: u32, imm: i32) -> u32 {
    store(0b001, rs2, rs1, imm)
}
fn sw(rs2: u32, rs1: u32, imm: i32) -> u32 {
    store(0b010, rs2, rs1, imm)
}

/// `jal x0, 0`. Every program ends by branching to itself and is run under a cycle
/// bound, which is how the simulator is meant to be stopped - falling off the end of
/// the program reaches the runtime-error handler, which aborts the process.
const JAL_SELF: u32 = 0x0000_006f;
const CSRRW_BIGINT: u32 = (0x7ca << 20) | (1 << 12) | 0x73;

struct Run {
    state: MachineState,
    memory: Box<MemoryHolder, LazyMmap>,
    trace: Box<TraceChunk>,
}

fn run(program: &[u32], cfg: JitRunnerRam) -> Run {
    let bound = (program.len() - 1) as u32; // everything up to the trailing self-loop
    let mut nd = ();
    let mut context = Context::new(DefaultContextImpl::new(&mut nd), cfg);
    let mut memory = MemoryHolder::allocate_zeroed(cfg, LazyMmap);
    assert_eq!(memory.ram_size(), cfg.ram_size());
    let mut trace: Box<TraceChunk> = unsafe { Box::new_zeroed().assume_init() };
    let runner =
        JittedCode::<DefaultContextImpl<'_, ()>>::preprocess_bytecode(program, Some(bound), cfg);
    runner.run(&mut context, &mut memory, NonNull::from(&mut *trace), &[]);
    let state = context
        .implementation
        .take_final_state()
        .expect("must finish execution");
    Run {
        state,
        memory,
        trace,
    }
}

/// Puts `base` into x11 and x5 - one GPR-mapped, one XMM-mapped - so the memory ops
/// below are emitted for both register classes.
fn base_setup(hi20: u32, a1: i32, a2: i32) -> [u32; 6] {
    [
        lui(11, hi20),
        addi(11, 11, a1),
        addi(11, 11, a2),
        lui(5, hi20),
        addi(5, 5, a1),
        addi(5, 5, a2),
    ]
}

/// Touches all eight memory ops - Lb, Lbu, Lh, Lhu, Lw, Sb, Sh, Sw - around `base`,
/// with positive and negative offsets. `base` must be 12 mod 16 so the negative
/// offsets stay in the same region.
fn mem_program(base_setup: [u32; 6]) -> Vec<u32> {
    let mut p = base_setup.to_vec();
    p.extend_from_slice(&[
        addi(12, 0, 0x5A5),
        lui(6, 0xABCDE),
        sw(12, 11, 0),
        sw(6, 5, -4),
        lw(13, 11, 0),
        lw(7, 5, -4),
        addi(14, 0, -3),
        sb(14, 11, 3),
        lb(15, 5, 3),
        lbu(8, 11, 3),
        sh(14, 5, 2),
        lh(9, 11, 2),
        lhu(10, 5, 2),
        lw(13, 11, 0),
        lb(7, 5, -3),
        lhu(15, 11, -2),
        sb(12, 5, -9),
        lw(14, 11, -12),
        JAL_SELF,
    ]);
    p
}

/// Hand-computed results for `mem_program`, independent of where it ran.
fn check_absolute(r: &Run, base: u32) {
    let regs = &r.state.registers;
    assert_eq!(regs[11], base);
    assert_eq!(regs[5], base);
    assert_eq!(regs[13], 0xFFFD_05A5, "x13");
    assert_eq!(regs[7], 0xFFFF_FFE0, "x7");
    assert_eq!(regs[8], 0xFD, "x8");
    assert_eq!(regs[9], 0xFFFF_FFFD, "x9");
    assert_eq!(regs[10], 0xFFFD, "x10");
    assert_eq!(regs[15], 0xABCD, "x15");
    assert_eq!(regs[14], 0xA500_0000, "x14");

    let w0 = (base as usize) / 4;
    let mem = r.memory.memory();
    let ts = r.memory.timestamps();
    assert_eq!(mem[w0], 0xFFFD_05A5);
    assert_eq!(mem[w0 - 1], 0xABCD_E000);
    assert_eq!(mem[w0 - 3], 0xA500_0000);
    assert_eq!(mem[w0 - 2], 0);
    assert_ne!(ts[w0], 0);
    assert_ne!(ts[w0 - 1], 0);
    assert_ne!(ts[w0 - 3], 0);
    assert_eq!(ts[w0 - 2], 0, "untouched word must keep a zero timestamp");
    if w0 + 1 < mem.len() {
        assert_eq!(mem[w0 + 1], 0);
        assert_eq!(ts[w0 + 1], 0);
    }
}

/// The two runs differ only in where the program put its base address, so everything
/// except the registers holding that address has to match exactly.
fn compare_runs(reference: &Run, candidate: &Run, ref_base: u32, cand_base: u32) {
    assert_eq!(reference.state.pc, candidate.state.pc);
    assert_eq!(reference.state.timestamp, candidate.state.timestamp);
    for i in 0..32 {
        if i == 11 || i == 5 {
            continue; // hold the base address
        }
        assert_eq!(
            reference.state.registers[i], candidate.state.registers[i],
            "register x{i}"
        );
        assert_eq!(
            reference.state.register_timestamps[i], candidate.state.register_timestamps[i],
            "register timestamp x{i}"
        );
    }

    assert_eq!(reference.trace.len, candidate.trace.len);
    let n = reference.trace.len as usize;
    assert!(n > 0);
    assert_eq!(&reference.trace.values[..n], &candidate.trace.values[..n]);
    assert_eq!(
        &reference.trace.timestamps[..n],
        &candidate.trace.timestamps[..n]
    );

    let rw = (ref_base as usize) / 4;
    let cw = (cand_base as usize) / 4;
    for k in -4isize..=0 {
        let ri = (rw as isize + k) as usize;
        let ci = (cw as isize + k) as usize;
        assert_eq!(
            reference.memory.memory()[ri],
            candidate.memory.memory()[ci],
            "memory at base{k:+}"
        );
        assert_eq!(
            reference.memory.timestamps()[ri],
            candidate.memory.timestamps()[ci],
            "timestamp at base{k:+}"
        );
    }
}

const LOW_BASE: u32 = 0x0100_000C;

fn low_reference() -> Run {
    run(
        &mem_program(base_setup(0x01000, 12, 0)),
        JitRunnerRam::Medium,
    )
}

#[test]
fn medium_reference_is_sane() {
    // guards the reference the other tests compare against
    check_absolute(&low_reference(), LOW_BASE);
}

#[test]
fn full_matches_medium_at_the_same_address() {
    // isolates the codegen change: same program, same addresses, only the RAM
    // configuration and therefore the instruction sequence differ
    let candidate = run(&mem_program(base_setup(0x01000, 12, 0)), JitRunnerRam::Full);
    check_absolute(&candidate, LOW_BASE);
    compare_runs(&low_reference(), &candidate, LOW_BASE, LOW_BASE);
}

#[test]
fn full_at_one_gib() {
    // the first address a 1 Gb image cannot represent
    let base = 0x4000_000C;
    let candidate = run(&mem_program(base_setup(0x40000, 12, 0)), JitRunnerRam::Full);
    check_absolute(&candidate, base);
    compare_runs(&low_reference(), &candidate, LOW_BASE, base);
}

#[test]
fn full_at_two_gib() {
    let base = 0x8000_000C;
    let candidate = run(&mem_program(base_setup(0x80000, 12, 0)), JitRunnerRam::Full);
    check_absolute(&candidate, base);
    compare_runs(&low_reference(), &candidate, LOW_BASE, base);
}

#[test]
fn full_at_top_of_memory() {
    // the last word of the image: its timestamp lands on the final eight bytes of the
    // holder, which is the tightest the addressing ever gets
    let base = 0xFFFF_FFFC;
    let candidate = run(
        &mem_program(base_setup(0xFFFFF, 2047, 2045)),
        JitRunnerRam::Full,
    );
    check_absolute(&candidate, base);
    compare_runs(&low_reference(), &candidate, LOW_BASE, base);
    let last = candidate.memory.timestamps().len() - 1;
    assert_ne!(
        candidate.memory.timestamps()[last],
        0,
        "the last timestamp slot must be reachable"
    );
}

/// Delegations receive the holder as a thin pointer and rebuild it from the RAM
/// configuration recorded on the context, which is a different path from the inline
/// memory accesses above.
fn bigint_program(a_hi20: u32) -> Vec<u32> {
    let mut p = vec![
        lui(10, a_hi20),
        addi(11, 10, 32),
        addi(12, 0, 1), // ADD
        addi(13, 0, -1),
    ];
    for i in 0..8 {
        p.push(sw(13, 10, 4 * i));
    }
    p.push(addi(14, 0, 1));
    p.push(sw(14, 11, 0));
    p.push(CSRRW_BIGINT);
    p.push(lw(15, 10, 0));
    p.push(lw(9, 10, 28));
    p.push(lw(8, 11, 0));
    p.push(JAL_SELF);
    p
}

#[test]
fn full_bigint_delegation_at_two_gib() {
    // 2^256-1 plus 1: wraps to zero and sets the overflow flag
    let reference = run(&bigint_program(0x01000), JitRunnerRam::Medium);
    assert_eq!(reference.state.registers[12], 1, "overflow flag");
    assert_eq!(reference.state.registers[15], 0);
    assert_eq!(reference.state.registers[9], 0);
    assert_eq!(reference.state.registers[8], 1);

    let candidate = run(&bigint_program(0x80000), JitRunnerRam::Full);
    assert_eq!(candidate.state.registers[10], 0x8000_0000);
    assert_eq!(candidate.state.timestamp, reference.state.timestamp);
    for i in 0..32 {
        if i == 10 || i == 11 {
            continue; // hold the operand addresses
        }
        assert_eq!(
            reference.state.registers[i], candidate.state.registers[i],
            "register x{i}"
        );
    }

    assert_eq!(reference.trace.len, candidate.trace.len);
    let n = reference.trace.len as usize;
    assert_eq!(&reference.trace.values[..n], &candidate.trace.values[..n]);
    assert_eq!(
        &reference.trace.timestamps[..n],
        &candidate.trace.timestamps[..n]
    );

    let rw = 0x0100_0000usize / 4;
    let cw = 0x8000_0000usize / 4;
    for k in 0..16 {
        assert_eq!(
            reference.memory.memory()[rw + k],
            candidate.memory.memory()[cw + k],
            "operand word {k}"
        );
        assert_eq!(
            reference.memory.timestamps()[rw + k],
            candidate.memory.timestamps()[cw + k],
            "operand timestamp {k}"
        );
    }
}

fn read_u32s(path: &Path) -> Vec<u32> {
    read_bytes(path)
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect()
}

fn read_bytes(path: &Path) -> Vec<u8> {
    use std::io::Read;
    let mut file = std::fs::File::open(path).expect("must open provided file");
    let mut buffer = vec![];
    file.read_to_end(&mut buffer).expect("must read the file");
    buffer
}

fn run_zksync_os(cfg: JitRunnerRam) -> (MachineState, Box<MemoryHolder, LazyMmap>) {
    let binary = read_u32s(Path::new("examples/zksync_os/app.bin"));
    let text = read_u32s(Path::new("examples/zksync_os/app.text"));
    let witness = read_bytes(Path::new("examples/zksync_os/23620012_witness"));
    let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
    let witness: Vec<_> = witness
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_be_bytes(*el))
        .collect();
    let mut source = QuasiUARTSource::new_with_reads(witness);

    let mut context = Context::new(DefaultContextImpl::new(&mut source), cfg);
    let mut memory = MemoryHolder::allocate_zeroed(cfg, LazyMmap);
    let mut trace: Box<TraceChunk> = unsafe { Box::new_zeroed().assume_init() };
    let runner = JittedCode::<DefaultContextImpl<'_, QuasiUARTSource>>::preprocess_bytecode(
        &text, None, cfg,
    );
    runner.run(
        &mut context,
        &mut memory,
        NonNull::from(&mut *trace),
        &binary,
    );
    let state = context
        .implementation
        .take_final_state()
        .expect("must finish execution");
    (state, memory)
}

/// A real block, both ways.
///
/// At 4 Gb every memory access rebases RSI, so this puts the rebase through a few
/// hundred million executions with trace chunks filling and flushing, delegations
/// firing, and the image being read back as well as written - none of which the short
/// programs above reach. The two runs have to agree on everything.
#[test]
fn real_block_full_matches_medium() {
    let (medium, medium_memory) = run_zksync_os(JitRunnerRam::Medium);
    let (full, full_memory) = run_zksync_os(JitRunnerRam::Full);

    assert_eq!(medium.pc, full.pc, "final pc");
    assert_eq!(medium.timestamp, full.timestamp, "final timestamp");
    assert_eq!(medium.counters, full.counters, "circuit counters");
    for i in 0..32 {
        assert_eq!(medium.registers[i], full.registers[i], "register x{i}");
        assert_eq!(
            medium.register_timestamps[i], full.register_timestamps[i],
            "register timestamp x{i}"
        );
    }

    // the whole 1 Gb the block can address, values and timestamps alike
    let words = medium_memory.memory().len();
    assert_eq!(
        (0..words)
            .filter(|&i| medium_memory.memory()[i] != full_memory.memory()[i])
            .count(),
        0,
        "memory image differs"
    );
    assert_eq!(
        (0..words)
            .filter(|&i| medium_memory.timestamps()[i] != full_memory.timestamps()[i])
            .count(),
        0,
        "timestamp image differs"
    );
}
