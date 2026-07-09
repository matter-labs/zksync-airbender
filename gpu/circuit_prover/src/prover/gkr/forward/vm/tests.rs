//! Task 9 CPU-only lowering tests: pure descriptor assembly against a MOCK
//! storage resolver (synthetic device pointers, never dereferenced), so no
//! GPU/context is needed. Pointer-level asserts against REAL prover storage +
//! kernel launches are Task 10's parity binary.
//!
//! Tests are exempt from the `crate::upstream` import rule (AGENTS.md).

use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};

use cs::definitions::GKRAddress;
use cs::gkr_compiler::dag_ir::{
    lower_dag, validate, validate_circuit_schedule, ChallengeRef, RangeWidth,
};
use field::{FieldExtension, PrimeField};

use gkr_eval_isa::fwd::binding::{read_place_to_backing, BackingKey};
use gkr_eval_isa::fwd::compile::{compile_circuit, load_committed_schedule, CompiledCircuit};
use gkr_eval_isa::fwd::context::{CompiledLayer, DagForwardContext};
use gkr_eval_isa::fwd::encode::decode;
use gkr_eval_isa::fwd::isa::{DstLine, Instr, LdcSub, MovDir, OperandField, OperandLine, Program};
use gkr_eval_isa::fwd::source::{virtual_setup_kind_code, SpecialStrategy};

use super::desc::{
    unpack_desc, ARENA_GENERIC_FAMILY, ARENA_RANGE_CHECK_16, ARENA_TIMESTAMP, ARG_CHALLENGE_CAP,
    CONST_CAP, CONST_CHALLENGE_CAP, DESC_CAP, PROGRAM_CAP, SD_AGGREGATE, SD_DECODER, SD_SETUP,
    SD_SINGLE_COLUMN, SD_VIRTUAL, SLOT_COUNT,
};
use super::lower::{
    lower_layer_desc, read_place_to_gkr_address, FwdVmHeaderInputs, FwdVmLowerError, ResolvedColumn,
};
use crate::primitives::field::{BF, E4};

const STEM: &str = "add_sub_lui_auipc_mop";
const COUNT: u32 = 1 << 12;

// ── fixture compile chain (mirrors bench_interp::fwd_vm::compile) ────────────

fn load_compiled_circuit(stem: &str) -> CompiledCircuit {
    let artifact: cs::gkr_compiler::GKRCircuitArtifact<BF> =
        crate::prover::tests::deserialize_json_for_test(&format!(
            "cs/compiled_circuits/{stem}_layout_gkr.json"
        ));
    let dag = lower_dag(&artifact).unwrap();
    validate(&dag).unwrap();
    let schedule_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../cs/compiled_circuits")
        .join(format!("{stem}_schedule_b16_gkr.json"));
    let sched = load_committed_schedule(&schedule_path).unwrap();
    validate_circuit_schedule(&dag, &sched).unwrap();
    compile_circuit(&dag, &sched, &artifact).unwrap()
}

// ── mock storage model ────────────────────────────────────────────────────────
// One fake consolidated matrix per field-qualified `BackingKey`; poly indices
// are assigned in DESCENDING address order — deliberately NEITHER the dense
// interning order NOR the original-offset order, so the tests fail if the
// lowering skips the dense-col → matrix-col rewrite.

struct MockStorage {
    columns: BTreeMap<GKRAddress, ResolvedColumn>,
}

impl MockStorage {
    fn build(compiled: &CompiledCircuit) -> Self {
        // Pass 1: every address each matrix must contain.
        let mut per_matrix: BTreeMap<String, (bool, BTreeSet<GKRAddress>)> = BTreeMap::new();
        let mut note = |key: &BackingKey, addr: GKRAddress| {
            let is_e4 = key.field() == OperandField::Ext;
            per_matrix
                .entry(format!("{key:?}"))
                .or_insert_with(|| (is_e4, BTreeSet::new()))
                .1
                .insert(addr);
        };
        for cl in &compiled.layers {
            let backings = &cl.ctx.backings;
            for slot in 0..SLOT_COUNT as u8 {
                let Some(key) = backings.backing(slot) else {
                    continue;
                };
                for col in 0..backings.slot_columns(slot).len() as u16 {
                    let place = backings.slot_col_to_read_place(slot, col).unwrap();
                    note(key, read_place_to_gkr_address(&place));
                }
            }
            for sd in cl.ctx.specials.iter() {
                if let SpecialStrategy::PeekDecoder { predicate, .. } = &sd.strategy {
                    let (key, _) = read_place_to_backing(predicate, OperandField::Base);
                    note(&key, read_place_to_gkr_address(predicate));
                }
            }
        }
        // Pass 2: fake matrix geometry + scrambled poly indices.
        let mut columns = BTreeMap::new();
        for (mid, (_, (is_e4, addrs))) in per_matrix.into_iter().enumerate() {
            let elem = if is_e4 { 16usize } else { 4 };
            let base = 0x1000_0000usize + mid * 0x0400_0000;
            let stride = (COUNT as usize * elem) as u32;
            for (i, addr) in addrs.iter().rev().enumerate() {
                columns.insert(
                    *addr,
                    ResolvedColumn {
                        is_e4,
                        ptr: (base + i * stride as usize) as *const u8,
                        matrix_base: base as *mut u8,
                        stride_bytes: stride,
                    },
                );
            }
        }
        Self { columns }
    }

    fn resolver(&self) -> impl Fn(GKRAddress) -> Option<ResolvedColumn> + '_ {
        move |addr| self.columns.get(&addr).copied()
    }
}

fn mock_challenge(r: &ChallengeRef) -> E4 {
    let mut h = DefaultHasher::new();
    format!("{r:?}").hash(&mut h);
    <E4 as FieldExtension<BF>>::from_base(BF::from_u32_with_reduction(h.finish() as u32))
}

fn mock_header() -> FwdVmHeaderInputs {
    FwdVmHeaderInputs {
        mapping_arena: [
            0x9000_0000usize as *const u32,
            0x9100_0000usize as *const u32,
            0x9200_0000usize as *const u32,
        ],
        decoder_mapping_col: Some(37),
        table: 0x9300_0000usize as *const E4,
        table_len: 4242,
        fill: 0x9400_0000usize as *const E4,
        count: COUNT,
    }
}

fn challenge_bank_len(cl: &CompiledLayer, sub: LdcSub) -> usize {
    let mut n = 0usize;
    while cl.ctx.challenges.get(sub, n as u16).is_some() {
        n += 1;
    }
    n
}

/// Every operand a decoded instruction reads, paired with the pre-rewrite
/// original operand at the same position (structure is preserved).
fn zip_operands<'a>(orig: &'a Instr, low: &'a Instr) -> Vec<(OperandLine, OperandLine)> {
    match (orig, low) {
        (Instr::Add { operands: a, .. }, Instr::Add { operands: b, .. })
        | (Instr::Mul { operands: a, .. }, Instr::Mul { operands: b, .. }) => {
            a.iter().copied().zip(b.iter().copied()).collect()
        }
        (Instr::Fma { pairs: a, .. }, Instr::Fma { pairs: b, .. }) => a
            .iter()
            .flat_map(|(l, r)| [*l, *r])
            .zip(b.iter().flat_map(|(l, r)| [*l, *r]))
            .collect(),
        (Instr::Mov { src: a, .. }, Instr::Mov { src: b, .. }) => {
            a.iter().copied().zip(b.iter().copied()).collect()
        }
        _ => panic!("instruction shape changed by lowering: {orig:?} vs {low:?}"),
    }
}

fn mov_dsts(orig: &Instr, low: &Instr) -> Option<(DstLine, DstLine)> {
    match (orig, low) {
        (Instr::Mov { dst: Some(a), .. }, Instr::Mov { dst: Some(b), .. }) => Some((*a, *b)),
        (Instr::Mov { dst: None, .. }, Instr::Mov { dst: None, .. }) => None,
        (Instr::Mov { .. }, Instr::Mov { .. }) => panic!("dst presence changed"),
        _ => None,
    }
}

// ── the main fixture invariants test ─────────────────────────────────────────

#[test]
fn fixture_lowering_struct_invariants() {
    let compiled = load_compiled_circuit(STEM);
    let mock = MockStorage::build(&compiled);
    let header = mock_header();
    let mut total_descs = 0usize;
    let mut saw_decoder = false;

    for (layer_idx, cl) in compiled.layers.iter().enumerate() {
        let setup = lower_layer_desc(cl, &header, &mock.resolver(), &mock_challenge, None)
            .unwrap_or_else(|e| panic!("L{layer_idx}: lower_layer_desc failed: {e:?}"));
        let d = &setup.desc;

        // -- program: inline (fits the cap), null LDG pointer, exact lanes. --
        assert!(
            d.program_ldg.is_null(),
            "L{layer_idx}: program_ldg not null"
        );
        assert!(d.program_lanes as usize <= PROGRAM_CAP);
        assert_eq!(d.n_instr as usize, cl.program.instrs.len());
        let lowered = decode(&d.program[..d.program_lanes as usize])
            .unwrap_or_else(|e| panic!("L{layer_idx}: inline program does not decode: {e:?}"));
        assert_eq!(lowered.instrs.len(), cl.program.instrs.len());

        // -- Global col rewrite: for every Global operand/dst, the kernel's
        //    base[slot] + col*stride addresses the SAME mock storage column
        //    the original dense (slot, col) resolves to via the reverse map. --
        let check_global = |slot: u8, orig_col: u16, lowered_col: u16| {
            let place = cl
                .ctx
                .backings
                .slot_col_to_read_place(slot, orig_col)
                .unwrap();
            let addr = read_place_to_gkr_address(&place);
            let want = mock.columns[&addr].ptr as usize;
            let got = d.base[slot as usize] as usize
                + lowered_col as usize * d.stride_bytes[slot as usize] as usize;
            assert_eq!(
                got, want,
                "L{layer_idx}: (slot {slot}, dense col {orig_col}) rewritten to matrix col \
                 {lowered_col} addresses {got:#x}, storage column is at {want:#x} ({addr:?})"
            );
        };
        for (orig, low) in cl.program.instrs.iter().zip(lowered.instrs.iter()) {
            for (o, l) in zip_operands(orig, low) {
                match (o, l) {
                    (
                        OperandLine::Global { slot, col },
                        OperandLine::Global { slot: ls, col: lc },
                    ) => {
                        assert_eq!(slot, ls);
                        check_global(slot, col, lc);
                    }
                    (a, b) => assert_eq!(a, b, "L{layer_idx}: non-Global operand changed"),
                }
            }
            if let Some((od, ld)) = mov_dsts(orig, low) {
                match (od, ld) {
                    (
                        DstLine::GlobalMaterialize { slot, col },
                        DstLine::GlobalMaterialize { slot: ls, col: lc },
                    ) => {
                        assert_eq!(slot, ls);
                        check_global(slot, col, lc);
                    }
                    (a, b) => assert_eq!(a, b, "L{layer_idx}: non-Global dst changed"),
                }
            }
        }

        // -- slot geometry: base/stride match the mock consolidated matrix of
        //    every slot in slot_columns; unused slots stay null. --
        for slot in 0..SLOT_COUNT as u8 {
            let s = slot as usize;
            let n_cols = cl.ctx.backings.slot_columns(slot).len();
            if n_cols == 0 {
                assert!(
                    d.base[s].is_null(),
                    "L{layer_idx}: empty slot {slot} has a base"
                );
                assert_eq!(d.stride_bytes[s], 0);
                continue;
            }
            for col in 0..n_cols as u16 {
                let place = cl.ctx.backings.slot_col_to_read_place(slot, col).unwrap();
                let rc = mock.columns[&read_place_to_gkr_address(&place)];
                assert_eq!(d.base[s], rc.matrix_base, "L{layer_idx}: slot {slot} base");
                assert_eq!(
                    d.stride_bytes[s], rc.stride_bytes,
                    "L{layer_idx}: slot {slot} stride"
                );
                let off = rc.ptr as usize - rc.matrix_base as usize;
                assert_eq!(off % rc.stride_bytes as usize, 0);
            }
        }

        // -- banks: consts + the arg/const challenge split. --
        let consts = cl.ctx.consts.values();
        assert!(consts.len() <= CONST_CAP);
        assert_eq!(d.n_consts as usize, consts.len());
        for (i, &v) in consts.iter().enumerate() {
            assert_eq!(
                d.consts[i],
                BF::from_u32_with_reduction(v),
                "L{layer_idx}: const {i}"
            );
        }
        let n_arg = challenge_bank_len(cl, LdcSub::ArgChallenge);
        let n_const_ch = challenge_bank_len(cl, LdcSub::ConstChallenge);
        assert!(n_arg <= ARG_CHALLENGE_CAP && n_const_ch <= CONST_CHALLENGE_CAP);
        assert_eq!(
            d.n_arg_challenge as usize, n_arg,
            "L{layer_idx}: arg-challenge split"
        );
        assert_eq!(
            d.n_const_challenge as usize, n_const_ch,
            "L{layer_idx}: const-challenge split"
        );
        for i in 0..n_arg {
            let r = cl
                .ctx
                .challenges
                .get(LdcSub::ArgChallenge, i as u16)
                .unwrap();
            assert_eq!(
                d.arg_challenge[i],
                mock_challenge(r),
                "L{layer_idx}: arg challenge {i}"
            );
        }

        // -- specials: packed descs decode back to the layer's strategies with
        //    NATIVE vkind values (2..=5). --
        let n_descs = cl.ctx.specials.len();
        assert!(n_descs <= DESC_CAP);
        assert_eq!(d.n_descs as usize, n_descs);
        total_descs += n_descs;
        let mut uses_table = false;
        let mut uses_decoder = false;
        for (i, sd) in cl.ctx.specials.iter().enumerate() {
            let (kind, arena, set_index, vkind) = unpack_desc(d.descs[i]);
            match &sd.strategy {
                SpecialStrategy::PeekSingleColumn {
                    set_index: si,
                    width,
                } => {
                    assert_eq!(kind, SD_SINGLE_COLUMN);
                    let want_arena = match width {
                        RangeWidth::Bits16 => ARENA_RANGE_CHECK_16,
                        RangeWidth::Timestamp => ARENA_TIMESTAMP,
                    };
                    assert_eq!((arena, set_index as usize, vkind), (want_arena, *si, 0));
                }
                SpecialStrategy::PeekAggregate { set_index: si } => {
                    uses_table = true;
                    assert_eq!(kind, SD_AGGREGATE);
                    assert_eq!(
                        (arena, set_index as usize, vkind),
                        (ARENA_GENERIC_FAMILY, *si, 0)
                    );
                }
                SpecialStrategy::PeekSetup => {
                    uses_table = true;
                    assert_eq!((kind, arena, set_index, vkind), (SD_SETUP, 0, 0, 0));
                }
                SpecialStrategy::PeekDecoder { predicate, .. } => {
                    uses_table = true;
                    uses_decoder = true;
                    assert_eq!(kind, SD_DECODER);
                    assert_eq!(arena, ARENA_GENERIC_FAMILY);
                    assert_eq!(set_index, header.decoder_mapping_col.unwrap());
                    // Mask = the resolved execute-predicate column.
                    let pred = mock.columns[&read_place_to_gkr_address(predicate)];
                    assert!(!pred.is_e4);
                    assert_eq!(d.mask as usize, pred.ptr as usize, "L{layer_idx}: mask ptr");
                }
                SpecialStrategy::VirtualSetup { kind: vk } => {
                    assert_eq!(kind, SD_VIRTUAL);
                    let want = virtual_setup_kind_code(vk) + 2;
                    assert!((2..=5).contains(&want));
                    assert_eq!(vkind, want, "L{layer_idx}: desc {i} native vkind");
                }
            }
        }
        saw_decoder |= uses_decoder;

        // -- header pointers: non-null exactly when the specials need them. --
        assert_eq!(
            !d.table.is_null(),
            uses_table,
            "L{layer_idx}: table iff aggregate/setup/decoder"
        );
        assert_eq!(d.table_len, if uses_table { header.table_len } else { 0 });
        assert_eq!(
            !d.fill.is_null(),
            uses_decoder,
            "L{layer_idx}: fill iff decoder"
        );
        assert_eq!(
            !d.mask.is_null(),
            uses_decoder,
            "L{layer_idx}: mask iff decoder"
        );
        assert_eq!(d.mapping_arena, header.mapping_arena);

        // -- geometry. --
        assert_eq!(d.count, COUNT);
    }

    // The fixture must actually exercise the special paths (add_sub L0 has
    // aggregate + single-column + setup + decoder + virtual specials).
    assert!(total_descs > 0, "fixture exercised no special descriptors");
    assert!(
        saw_decoder,
        "fixture exercised no PeekDecoder (mask/fill iff-check vacuous)"
    );
}

// ── synthetic error paths ─────────────────────────────────────────────────────

fn synthetic_layer(program: Program, ctx: DagForwardContext) -> CompiledLayer {
    CompiledLayer {
        program,
        ctx,
        root_outputs: vec![],
        skipped: vec![],
        trace: Default::default(),
        budget: 16,
        stats: Default::default(),
        resident_realized: vec![],
    }
}

fn no_columns(_: GKRAddress) -> Option<ResolvedColumn> {
    None
}

#[test]
fn const_bank_overflow_is_a_hard_error() {
    let mut ctx = DagForwardContext::default();
    for v in 2..(2 + CONST_CAP as u32 + 1) {
        ctx.consts.intern(v);
    }
    let cl = synthetic_layer(Program::default(), ctx);
    let err = lower_layer_desc(&cl, &mock_header(), &no_columns, &mock_challenge, None)
        .expect_err("41 consts must overflow CONST_CAP");
    assert!(matches!(err, FwdVmLowerError::ConstBankOverflow { n } if n == CONST_CAP + 1));
}

#[test]
fn desc_overflow_is_a_hard_error() {
    use gkr_eval_isa::fwd::source::SpecialDescriptor;
    let mut ctx = DagForwardContext::default();
    for i in 0..(DESC_CAP + 1) {
        ctx.specials.push(SpecialDescriptor {
            strategy: SpecialStrategy::PeekSetup,
            origin_expr: cs::gkr_compiler::dag_ir::ExprId(i as u32),
        });
    }
    let cl = synthetic_layer(Program::default(), ctx);
    let err = lower_layer_desc(&cl, &mock_header(), &no_columns, &mock_challenge, None)
        .expect_err("DESC_CAP+1 specials must overflow");
    assert!(matches!(err, FwdVmLowerError::DescOverflow { n } if n == DESC_CAP + 1));
}

#[test]
fn program_overflow_without_fallback_context_is_an_error() {
    // Each `Mov AccFromSrc` is 2 lanes; PROGRAM_CAP/2 + 1 of them overflow.
    let instrs = vec![
        Instr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Base,
            dst: None,
            src: Some(OperandLine::Ldc {
                sub: LdcSub::Special,
                idx: 1
            }),
        };
        PROGRAM_CAP / 2 + 1
    ];
    let cl = synthetic_layer(Program { instrs }, DagForwardContext::default());
    let err = lower_layer_desc(&cl, &mock_header(), &no_columns, &mock_challenge, None)
        .expect_err("oversize program with no fallback context must error");
    assert!(matches!(err, FwdVmLowerError::ProgramOverflow { lanes } if lanes == PROGRAM_CAP + 2));
}

#[test]
fn unresolved_column_is_an_error() {
    use cs::gkr_compiler::dag_ir::ReadPlace;
    let mut ctx = DagForwardContext::default();
    ctx.backings
        .read_slot_col(&ReadPlace::Setup { column: 3 }, OperandField::Base)
        .unwrap();
    let cl = synthetic_layer(Program::default(), ctx);
    let err = lower_layer_desc(&cl, &mock_header(), &no_columns, &mock_challenge, None)
        .expect_err("unresolvable slot column must error");
    assert!(matches!(
        err,
        FwdVmLowerError::UnresolvedColumn {
            slot: 0,
            col: 0,
            addr: GKRAddress::Setup(3)
        }
    ));
}

#[test]
fn split_matrix_slot_is_a_geometry_error() {
    use cs::gkr_compiler::dag_ir::ReadPlace;
    let mut ctx = DagForwardContext::default();
    ctx.backings
        .read_slot_col(&ReadPlace::Setup { column: 0 }, OperandField::Base)
        .unwrap();
    ctx.backings
        .read_slot_col(&ReadPlace::Setup { column: 1 }, OperandField::Base)
        .unwrap();
    let cl = synthetic_layer(Program::default(), ctx);
    // Two columns of ONE slot resolving into DIFFERENT matrices.
    let resolve = |addr: GKRAddress| -> Option<ResolvedColumn> {
        let base = match addr {
            GKRAddress::Setup(0) => 0x1000_0000usize,
            GKRAddress::Setup(1) => 0x2000_0000usize,
            _ => return None,
        };
        Some(ResolvedColumn {
            is_e4: false,
            ptr: base as *const u8,
            matrix_base: base as *mut u8,
            stride_bytes: COUNT * 4,
        })
    };
    let err = lower_layer_desc(&cl, &mock_header(), &resolve, &mock_challenge, None)
        .expect_err("split-matrix slot must be rejected");
    assert!(matches!(
        err,
        FwdVmLowerError::SlotGeometryMismatch { slot: 0, col: 1 }
    ));
}

#[test]
fn col_remap_collision_is_a_hard_error() {
    use cs::gkr_compiler::dag_ir::ReadPlace;
    let mut ctx = DagForwardContext::default();
    ctx.backings
        .read_slot_col(&ReadPlace::Setup { column: 0 }, OperandField::Base)
        .unwrap();
    ctx.backings
        .read_slot_col(&ReadPlace::Setup { column: 1 }, OperandField::Base)
        .unwrap();
    let cl = synthetic_layer(Program::default(), ctx);
    // Two DISTINCT dense columns of ONE slot resolving to the SAME matrix
    // column (same base + same offset) — a resolver bug that must fail
    // closed rather than silently alias one wire `col` to two dense columns.
    let resolve = |addr: GKRAddress| -> Option<ResolvedColumn> {
        match addr {
            GKRAddress::Setup(0) | GKRAddress::Setup(1) => Some(ResolvedColumn {
                is_e4: false,
                ptr: 0x1000_0000usize as *const u8,
                matrix_base: 0x1000_0000usize as *mut u8,
                stride_bytes: COUNT * 4,
            }),
            _ => None,
        }
    };
    let err = lower_layer_desc(&cl, &mock_header(), &resolve, &mock_challenge, None)
        .expect_err("col-remap collision must be rejected");
    assert!(matches!(
        err,
        FwdVmLowerError::ColRemapCollision {
            slot: 0,
            matrix_col: 0
        }
    ));
}

#[test]
fn arg_challenge_overflow_is_a_hard_error_and_terminates() {
    use cs::gkr_compiler::dag_ir::{ChallengeKey, ChallengePower};
    let mut ctx = DagForwardContext::default();
    for i in 0..(ARG_CHALLENGE_CAP as u32 + 1) {
        ctx.challenges.intern(&ChallengeRef {
            key: ChallengeKey::PermutationAdditive,
            power: ChallengePower::Static(i),
        });
    }
    let cl = synthetic_layer(Program::default(), ctx);
    // The probe loop must terminate (bounded at cap + 1) rather than wrap
    // `n as u16` and spin forever on an oversized bank.
    let err = lower_layer_desc(&cl, &mock_header(), &no_columns, &mock_challenge, None)
        .expect_err("ARG_CHALLENGE_CAP+1 challenges must overflow");
    assert!(matches!(
        err,
        FwdVmLowerError::ArgChallengeOverflow { n } if n == ARG_CHALLENGE_CAP + 1
    ));
}

#[test]
fn ldg_fallback_pointer_math_is_unreachable_without_context() {
    // Belt-and-braces around the inline/fallback boundary: exactly at the cap
    // the program stays inline (null LDG) — PROGRAM_CAP/2 Movs = PROGRAM_CAP
    // lanes.
    let instrs = vec![
        Instr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Base,
            dst: None,
            src: Some(OperandLine::Ldc {
                sub: LdcSub::Special,
                idx: 1
            }),
        };
        PROGRAM_CAP / 2
    ];
    let cl = synthetic_layer(Program { instrs }, DagForwardContext::default());
    let setup = lower_layer_desc(&cl, &mock_header(), &no_columns, &mock_challenge, None).unwrap();
    assert!(setup.desc.program_ldg.is_null());
    assert_eq!(setup.desc.program_lanes as usize, PROGRAM_CAP);
}
