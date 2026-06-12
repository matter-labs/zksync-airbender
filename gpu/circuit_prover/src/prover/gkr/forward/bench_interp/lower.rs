//! CPU→GPU lowering of a `gkr_eval_isa` compiled forward program into the
//! `interp_desc` ABI (`native/bench/gkr_fwd_interp.cu`). Test/bench-only code
//! (the module is `cfg(all(test, feature = "bench"))`), so `gkr_eval_isa` is
//! a dev-dependency and upstream-import rules don't apply.

use gkr_eval_isa::compiler::fwd::CompiledForward;
use gkr_eval_isa::isa::{encode, Dst, Program};

use crate::primitives::field::BF;
use field::PrimeField;

/// Host-side image of the kernel's `interp_desc` payload. The caller uploads
/// `lanes`, `source_ptrs`, `output_ptrs`, `output_e4` and `consts` to device
/// buffers and assembles an `InterpDesc` from them.
pub(crate) struct LoweredProgram {
    /// `gkr_eval_isa::isa::encode(&cf.program)` verbatim.
    pub lanes: Vec<u16>,
    pub n_instr: u32,
    /// ONE pointer table matching the kernel ABI: bf source columns at
    /// `[0, n_sources_bf)` followed by e4 source columns. The encoded
    /// `Operand::Source { id, e4 }` banks are separate id spaces
    /// (interp.rs `read`); the kernel indexes e4 ids at `n_sources_bf + id`.
    pub source_ptrs: Vec<*const u8>,
    pub n_sources_bf: u32,
    /// Per ORIGINAL output slot j (len = `program.n_outputs`); null for slots
    /// the program never writes (native-stored outputs).
    pub output_ptrs: Vec<*mut u8>,
    /// Bitset over output slots: 1 = the slot buffer holds e4 elements.
    pub output_e4: Vec<u32>,
    /// Constant table converted to device-ready Montgomery form. The CPU
    /// interpreter stores canonical u32 and converts on read
    /// (`Bf::from_u32_with_reduction`, interp.rs); the kernel reads raw bf.
    pub consts: Vec<BF>,
    /// Cell-file size = `program.n_slot_cells` (the compiler's address-based
    /// high water; every encoded cell index is below it).
    pub budget_cells: u32,
}

/// Per-output-slot write width from the program's own `Dst::Output`
/// instructions (mirrors the CPU write path: interp.rs stores whatever
/// `e4_result` says, so the GPU buffer width must match it).
/// `None` = slot never written.
pub(crate) fn output_widths(p: &Program) -> Vec<Option<bool>> {
    let mut widths = vec![None::<bool>; p.n_outputs as usize];
    for ins in &p.instrs {
        if let Dst::Output(j) = ins.dst {
            let w = &mut widths[j as usize];
            assert!(
                w.is_none() || *w == Some(ins.e4_result),
                "output slot {j} written with two widths"
            );
            *w = Some(ins.e4_result);
        }
    }
    widths
}

/// Lower a compiled forward program to the kernel ABI.
///
/// Resolver contract:
/// - `resolve_src_bf(i)` / `resolve_src_e4(i)` take the SOURCE-BANK INDEX
///   (the operand-lane id, i.e. an index into `cf.source_map.bf` /
///   `cf.source_map.e4`) — NOT the arena node id. Callers needing the node
///   can map via `cf.source_map.bf[i]` / `cf.source_map.e4[i]`. They return
///   the device column base pointer (element stride 4B bf / 16B e4).
/// - `resolve_out(j)` takes the ORIGINAL output slot index (the `j` of
///   `cf.outputs`) and returns the device column base + whether the column
///   holds e4 elements; the width is cross-checked against the program.
pub(crate) fn lower_program(
    cf: &CompiledForward,
    resolve_src_bf: impl Fn(usize) -> *const u8,
    resolve_src_e4: impl Fn(usize) -> *const u8,
    resolve_out: impl Fn(u16) -> (*mut u8, bool),
) -> LoweredProgram {
    let p = &cf.program;
    assert_eq!(
        p.n_fixed_cells, 0,
        "forward programs have no fixed-reg file"
    );
    assert_eq!(p.n_gate_ins, 0, "forward programs have no gate-in staging");
    // The kernel writes a zero sentinel for ANY NativeK with a Slot dst (it
    // has no payload table until Task 4); the CPU writes sentinels only for
    // cache payloads. Pin the equivalence here so a non-cache Slot-dst
    // NativeK cannot silently diverge.
    for ins in &p.instrs {
        if ins.op == gkr_eval_isa::isa::Op::NativeK {
            let is_cache = p.payloads[ins.payload.unwrap() as usize].cache.is_some();
            let has_slot_dst = matches!(ins.dst, Dst::Slot(_));
            assert_eq!(
                is_cache, has_slot_dst,
                "NativeK Slot-dst <=> cache payload violated"
            );
        }
    }
    let lanes = encode(p);

    let n_bf = p.n_sources_bf as usize;
    let n_e4 = p.n_sources_e4 as usize;
    assert_eq!(cf.source_map.bf.len(), n_bf);
    assert_eq!(cf.source_map.e4.len(), n_e4);
    let mut source_ptrs = Vec::with_capacity(n_bf + n_e4);
    source_ptrs.extend((0..n_bf).map(&resolve_src_bf));
    source_ptrs.extend((0..n_e4).map(&resolve_src_e4));

    let widths = output_widths(p);
    // Every slot the program writes must be in cf.outputs (so the test can
    // hand it a buffer), and vice versa every cf.outputs entry is written.
    let n_out = p.n_outputs as usize;
    let mut output_ptrs: Vec<*mut u8> = vec![std::ptr::null_mut(); n_out];
    let mut output_e4 = vec![0u32; n_out.div_ceil(32).max(1)];
    for &(j, _node) in &cf.outputs {
        let e4 = widths[j as usize]
            .unwrap_or_else(|| panic!("cf.outputs slot {j} never written by the program"));
        let (ptr, slot_e4) = resolve_out(j);
        assert!(
            !ptr.is_null(),
            "resolver returned null for written output slot {j}"
        );
        assert_eq!(
            slot_e4, e4,
            "output slot {j}: resolver width disagrees with the program"
        );
        output_ptrs[j as usize] = ptr;
        if e4 {
            output_e4[j as usize / 32] |= 1 << (j as usize % 32);
        }
    }
    for (j, w) in widths.iter().enumerate() {
        if w.is_some() {
            assert!(
                cf.outputs.iter().any(|&(jj, _)| jj as usize == j),
                "program writes output slot {j} absent from cf.outputs"
            );
        }
    }

    let consts: Vec<BF> = p
        .consts
        .iter()
        .map(|&c| BF::from_u32_with_reduction(c))
        .collect();

    LoweredProgram {
        lanes,
        n_instr: p.instrs.len() as u32,
        source_ptrs,
        n_sources_bf: p.n_sources_bf as u32,
        output_ptrs,
        output_e4,
        consts,
        budget_cells: p.n_slot_cells as u32,
    }
}
