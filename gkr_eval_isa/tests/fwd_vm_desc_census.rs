//! fwd-VM v2 descriptor-ABI census (Task 7): compile every committed layer
//! program (the 11 with-caches `_layout_gkr.json` fixtures at their committed
//! b16 schedules) and report the corpus maxima of the five budgeted
//! `fwd_vm_desc` quantities:
//!
//!   program_lanes     — encoded 16-bit wire lanes (inline `program[PROGRAM_CAP]`)
//!   n_consts          — interned bf constants (inline `consts[CONST_CAP]`)
//!   n_arg_derived_e4   — schedule-time-known derived E4 (inline `arg_derived_e4[..]`)
//!   n_const_derived_e4 — runtime derived_e4 (Task-8 `__constant__` bank)
//!   n_descs           — special descriptors (inline `descs[DESC_CAP]`)
//!
//! The asserted bounds are the caps in
//! `gpu/circuit_prover/src/prover/gkr/forward/vm/desc.rs` (mirrored in
//! `gpu/circuit_prover/native/prover/gkr/forward/fwd_vm.cuh`) — duplicated as
//! literals here because `gkr_eval_isa` cannot depend on `circuit_prover`.
//! If this census starts failing, the corpus outgrew a cap: re-run with
//! `--nocapture`, pick new caps (~25% margin), and update BOTH ABI sides plus
//! the literals below in lockstep.
//!
//! Run: RUSTFLAGS="-Awarnings" cargo test -p gkr_eval_isa --test fwd_vm_desc_census -- --nocapture

mod common;
use common::load_dag_sched;

use gkr_eval_isa::fwd::compile::compile_circuit;
use gkr_eval_isa::fwd::encode::encode;
use gkr_eval_isa::fwd::isa::LdcSub;

/// The committed-schedule corpus: the 11 with-caches fixtures (the
/// `_no_caches` variants have no committed schedules and are not GPU-proven
/// via this path).
const FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "inits_and_teardowns_preprocessed_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
];

// Caps pinned against circuit_prover's fwd_vm_desc / FwdVmDesc (see module doc).
const PROGRAM_CAP: usize = 12288; // lanes; overflow falls back to program_ldg (corpus max 6574)
const CONST_CAP: usize = 40; // hard lowering error on overflow (corpus max 27)
const ARG_DERIVED_E4_CAP: usize = 12; // hard lowering error on overflow (corpus max 7)
const CONST_DERIVED_E4_CAP: usize = 8; // Task-8 __constant__ bank; hard error on overflow (corpus max 1)
const DESC_CAP: usize = 370; // hard lowering error on overflow (corpus max 296, blake2 L0)

#[derive(Default)]
struct Maxima {
    program_lanes: usize,
    n_consts: usize,
    n_arg_derived_e4: usize,
    n_const_derived_e4: usize,
    n_descs: usize,
    where_lanes: String,
}

fn derived_e4_bank_len(ctx: &gkr_eval_isa::fwd::context::DagForwardContext, sub: LdcSub) -> usize {
    let mut idx = 0u16;
    while ctx.derived_e4.get(sub, idx).is_some() {
        idx += 1;
    }
    idx as usize
}

#[test]
fn fwd_vm_desc_corpus_census() {
    let mut m = Maxima::default();
    println!(
        "{:<52} {:>5} {:>6} {:>7} {:>7} {:>7} {:>6}",
        "fixture/layer", "layer", "lanes", "consts", "argch", "constch", "descs"
    );
    for name in FIXTURES {
        let (dag, sched, artifact) = load_dag_sched(name);
        let compiled = compile_circuit(&dag, &sched, &artifact)
            .unwrap_or_else(|e| panic!("compile_circuit({name}): {e:?}"));
        for (li, layer) in compiled.layers.iter().enumerate() {
            let lanes = encode(&layer.program)
                .unwrap_or_else(|e| panic!("{name} L{li}: encode: {e:?}"))
                .len();
            let n_consts = layer.ctx.consts.values().len();
            let n_arg = derived_e4_bank_len(&layer.ctx, LdcSub::ArgDerivedE4);
            let n_cch = derived_e4_bank_len(&layer.ctx, LdcSub::ConstDerivedE4);
            let n_descs = layer.ctx.specials.len();
            println!(
                "{:<52} {:>5} {:>6} {:>7} {:>7} {:>7} {:>6}",
                name, li, lanes, n_consts, n_arg, n_cch, n_descs
            );
            if lanes > m.program_lanes {
                m.program_lanes = lanes;
                m.where_lanes = format!("{name} L{li}");
            }
            m.n_consts = m.n_consts.max(n_consts);
            m.n_arg_derived_e4 = m.n_arg_derived_e4.max(n_arg);
            m.n_const_derived_e4 = m.n_const_derived_e4.max(n_cch);
            m.n_descs = m.n_descs.max(n_descs);
        }
    }
    println!("\n=== corpus maxima ===");
    println!(
        "program_lanes     max = {:>6}  (cap {PROGRAM_CAP}, at {})",
        m.program_lanes, m.where_lanes
    );
    println!(
        "n_consts          max = {:>6}  (cap {CONST_CAP})",
        m.n_consts
    );
    println!(
        "n_arg_derived_e4   max = {:>6}  (cap {ARG_DERIVED_E4_CAP})",
        m.n_arg_derived_e4
    );
    println!(
        "n_const_derived_e4 max = {:>6}  (cap {CONST_DERIVED_E4_CAP})",
        m.n_const_derived_e4
    );
    println!("n_descs           max = {:>6}  (cap {DESC_CAP})", m.n_descs);

    // program overflow has the program_ldg fallback, but the committed corpus is
    // expected to fit inline — flag loudly if that stops being true.
    assert!(
        m.program_lanes <= PROGRAM_CAP,
        "program_lanes {} > PROGRAM_CAP",
        m.program_lanes
    );
    // the remaining caps are hard lowering errors — no fallback.
    assert!(
        m.n_consts <= CONST_CAP,
        "n_consts {} > CONST_CAP",
        m.n_consts
    );
    assert!(
        m.n_arg_derived_e4 <= ARG_DERIVED_E4_CAP,
        "n_arg_derived_e4 {} > cap",
        m.n_arg_derived_e4
    );
    assert!(
        m.n_const_derived_e4 <= CONST_DERIVED_E4_CAP,
        "n_const_derived_e4 {} > cap",
        m.n_const_derived_e4
    );
    assert!(m.n_descs <= DESC_CAP, "n_descs {} > DESC_CAP", m.n_descs);
}
