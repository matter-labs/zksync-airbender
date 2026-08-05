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
use field::{FieldExtension, PrimeField};
use gkr_eval_ir::{lower_dag, validate, ChallengeRef, RangeWidth};
use gpu_gkr_compiler::validate_forward_artifact;

use gpu_gkr_compiler::forward::binding::{
    bind_final_sources, read_place_to_backing, BackingKey, SourceMarkerMode,
};
use gpu_gkr_compiler::forward::compile::{compile_circuit, load_committed_schedule, CompiledCircuit};
use gpu_gkr_compiler::forward::context::{CompiledLayer, DagForwardContext};
use gpu_gkr_compiler::forward::encode::decode;
use gpu_gkr_compiler::forward::isa::{DstLine, Instr, LdcSub, MovDir, OperandField, OperandLine, Program};
use gpu_gkr_compiler::forward::source::{virtual_setup_kind_code, SpecialStrategy};

use super::desc::{
    unpack_desc, ARENA_GENERIC_FAMILY, ARENA_RANGE_CHECK_16, ARENA_TIMESTAMP, ARG_DERIVED_E4_CAP,
    CONST_CAP, CONST_DERIVED_E4_CAP, DESC_CAP, DST_SLOT_COUNT, FILL_BANK_NONE, PROGRAM_CAP,
    SD_AGGREGATE, SD_DECODER, SD_SETUP, SD_SINGLE_COLUMN, SD_VIRTUAL, SOURCE_WINDOW_COUNT,
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
    validate_forward_artifact(&dag, &sched).unwrap();
    compile_circuit(&dag, &sched).unwrap()
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
            for slot in 0..DST_SLOT_COUNT as u8 {
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
        count: COUNT,
    }
}

fn derived_e4_bank_len(cl: &CompiledLayer, sub: LdcSub) -> usize {
    let mut n = 0usize;
    while cl.ctx.derived_e4.get(sub, n as u16).is_some() {
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

        let mut check_source = |window: u8, column: u8, wire: u8, wire_column: u8| {
            let place = cl
                .ctx
                .source_windows
                .resolve_read_place(window, column)
                .unwrap();
            let addr = read_place_to_gkr_address(&place);
            let want = mock.columns[&addr].ptr as usize;
            let got = d.source_base[wire as usize] as usize
                + wire_column as usize * d.source_stride_bytes[wire as usize] as usize;
            assert_eq!(got, want, "L{layer_idx}: source {window}:{column} remap");
        };
        let mut check_dst = |slot: u8, orig_col: u16, wire_slot: u8, wire_col: u16| {
            let place = cl
                .ctx
                .backings
                .slot_col_to_read_place(slot, orig_col)
                .unwrap();
            let addr = read_place_to_gkr_address(&place);
            let want = mock.columns[&addr].ptr as usize;
            let got = d.dst_base[wire_slot as usize] as usize
                + wire_col as usize * d.dst_stride_bytes[wire_slot as usize] as usize;
            assert_eq!(
                got, want,
                "L{layer_idx}: (slot {slot}, dense col {orig_col}) rewritten to wire \
                 (slot {wire_slot}, col {wire_col}) addresses {got:#x}, storage column \
                 is at {want:#x} ({addr:?})"
            );
        };
        for (orig, low) in cl.program.instrs.iter().zip(lowered.instrs.iter()) {
            for (o, l) in zip_operands(orig, low) {
                match (o, l) {
                    (
                        OperandLine::Source {
                            window,
                            column,
                            first_access,
                        },
                        OperandLine::Source {
                            window: low_window,
                            column: low_column,
                            first_access: low_first,
                        },
                    ) => {
                        assert_eq!(first_access, low_first);
                        check_source(window, column, low_window, low_column);
                    }
                    (a, b) => assert_eq!(a, b, "L{layer_idx}: non-source operand changed"),
                }
            }
            if let Some((od, ld)) = mov_dsts(orig, low) {
                match (od, ld) {
                    (
                        DstLine::GlobalMaterialize { slot, col },
                        DstLine::GlobalMaterialize { slot: ls, col: lc },
                    ) => check_dst(slot, col, ls, lc),
                    (a, b) => assert_eq!(a, b, "L{layer_idx}: non-Global dst changed"),
                }
            }
        }
        assert!(d.source_base.iter().filter(|base| !base.is_null()).count() <= SOURCE_WINDOW_COUNT);
        assert!(d.dst_base.iter().filter(|base| !base.is_null()).count() <= DST_SLOT_COUNT);

        // -- banks: consts + the argument/constant derived-E4 split. --
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
        let has_decoder = cl
            .ctx
            .specials
            .iter()
            .any(|sd| matches!(sd.strategy, SpecialStrategy::PeekDecoder { .. }));
        let n_arg = derived_e4_bank_len(cl, LdcSub::ArgDerivedE4);
        let n_const_ch = derived_e4_bank_len(cl, LdcSub::ConstDerivedE4);
        assert!(n_arg <= ARG_DERIVED_E4_CAP && n_const_ch <= CONST_DERIVED_E4_CAP);
        assert_eq!(
            d.n_arg_derived_e4 as usize, n_arg,
            "L{layer_idx}: arg-derived-e4 split"
        );
        // A decoder layer appends ONE bank slot for the fill value at
        // fill_bank_idx = the pre-append bank length (mechanism (a)).
        assert_eq!(
            d.n_const_derived_e4 as usize,
            n_const_ch + has_decoder as usize,
            "L{layer_idx}: const-derived-e4 split (+ appended fill slot)"
        );
        if has_decoder {
            assert_eq!(
                d.fill_bank_idx as usize, n_const_ch,
                "L{layer_idx}: fill_bank_idx must be the pre-append bank length"
            );
        } else {
            assert_eq!(
                d.fill_bank_idx, FILL_BANK_NONE,
                "L{layer_idx}: decoder-free layer must carry the sentinel"
            );
        }
        for i in 0..n_arg {
            let r = cl
                .ctx
                .derived_e4
                .get(LdcSub::ArgDerivedE4, i as u16)
                .unwrap();
            assert_eq!(
                d.arg_derived_e4[i],
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
            uses_decoder, has_decoder,
            "L{layer_idx}: specials-loop decoder census disagrees with the strategy scan"
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
        "fixture exercised no PeekDecoder (mask/fill_bank_idx checks vacuous)"
    );
}

// ── synthetic error paths ─────────────────────────────────────────────────────

fn synthetic_layer(mut program: Program, mut ctx: DagForwardContext) -> CompiledLayer {
    ctx.source_windows =
        bind_final_sources(&mut program, &ctx.backings, SourceMarkerMode::Forward).unwrap();
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
    use gpu_gkr_compiler::forward::source::SpecialDescriptor;
    let mut ctx = DagForwardContext::default();
    for i in 0..(DESC_CAP + 1) {
        ctx.specials.push(SpecialDescriptor {
            strategy: SpecialStrategy::PeekSetup,
            origin_expr: gkr_eval_ir::ExprId(i as u32),
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
    use gkr_eval_ir::ReadPlace;
    let mut ctx = DagForwardContext::default();
    ctx.backings
        .read_slot_col(&ReadPlace::Setup { column: 3 }, OperandField::Base)
        .unwrap();
    let cl = synthetic_layer(
        Program {
            instrs: vec![Instr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Base,
                dst: None,
                src: Some(OperandLine::LogicalGlobal { slot: 0, col: 0 }),
            }],
        },
        ctx,
    );
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
fn split_matrix_slot_produces_per_matrix_wire_slots() {
    use gkr_eval_ir::ReadPlace;
    let mut ctx = DagForwardContext::default();
    // THREE dense columns of ONE compile slot: cols 0 and 2 live in matrix A
    // (at matrix cols 1 and 0 — also exercises the col renumber within a
    // split slot), col 1 is a CopyAlias-style view into matrix B.
    for column in 0..3 {
        ctx.backings
            .read_slot_col(&ReadPlace::Setup { column }, OperandField::Base)
            .unwrap();
    }
    let program = Program {
        instrs: vec![Instr::Add {
            field: OperandField::Base,
            sign: gpu_gkr_compiler::forward::isa::Sign::Plus,
            promote: false,
            operands: vec![
                OperandLine::LogicalGlobal { slot: 0, col: 0 },
                OperandLine::LogicalGlobal { slot: 0, col: 1 },
                OperandLine::LogicalGlobal { slot: 0, col: 2 },
            ],
        }],
    };
    let cl = synthetic_layer(program, ctx);
    const BASE_A: usize = 0x1000_0000;
    const BASE_B: usize = 0x2000_0000;
    let stride = COUNT * 4;
    let resolve = move |addr: GKRAddress| -> Option<ResolvedColumn> {
        let (base, ptr) = match addr {
            GKRAddress::Setup(0) => (BASE_A, BASE_A + stride as usize), // matrix col 1
            GKRAddress::Setup(1) => (BASE_B, BASE_B),                   // matrix col 0
            GKRAddress::Setup(2) => (BASE_A, BASE_A),                   // matrix col 0
            _ => return None,
        };
        Some(ResolvedColumn {
            is_e4: false,
            ptr: ptr as *const u8,
            matrix_base: base as *mut u8,
            stride_bytes: stride,
        })
    };
    let setup = lower_layer_desc(&cl, &mock_header(), &resolve, &mock_challenge, None)
        .expect("split-matrix slot must lower via wire-slot splitting");
    let d = &setup.desc;

    // Wire slot 0 = matrix A (first appearance, dense col 0), wire slot 1 =
    // matrix B; nothing else allocated.
    assert_eq!(d.source_base[0] as usize, BASE_A);
    assert_eq!(d.source_base[1] as usize, BASE_B);
    assert_eq!(
        (d.source_stride_bytes[0], d.source_stride_bytes[1]),
        (stride, stride)
    );
    assert!(d.source_base[2].is_null());
    assert_eq!(d.source_stride_bytes[2], 0);

    // The program's slot AND col fields are rewritten to the wire encoding.
    let lowered = decode(&d.program[..d.program_lanes as usize]).unwrap();
    assert_eq!(
        lowered.instrs,
        vec![Instr::Add {
            field: OperandField::Base,
            sign: gpu_gkr_compiler::forward::isa::Sign::Plus,
            promote: false,
            operands: vec![
                OperandLine::Source {
                    window: 0,
                    column: 1,
                    first_access: false
                },
                OperandLine::Source {
                    window: 1,
                    column: 0,
                    first_access: false
                },
                OperandLine::Source {
                    window: 0,
                    column: 0,
                    first_access: false
                },
            ],
        }]
    );
}

#[test]
fn source_window_overflow_is_a_hard_error() {
    use gkr_eval_ir::ReadPlace;
    let mut ctx = DagForwardContext::default();
    // Each source resolves into its own matrix. The 65th physical group
    // cannot get a source window.
    for column in 0..(SOURCE_WINDOW_COUNT + 1) {
        ctx.backings
            .read_slot_col(&ReadPlace::Setup { column }, OperandField::Base)
            .unwrap();
    }
    let cl = synthetic_layer(
        Program {
            instrs: vec![Instr::Add {
                field: OperandField::Base,
                sign: gpu_gkr_compiler::forward::isa::Sign::Plus,
                promote: false,
                operands: (0..=SOURCE_WINDOW_COUNT as u16)
                    .map(|col| OperandLine::LogicalGlobal { slot: 0, col })
                    .collect(),
            }],
        },
        ctx,
    );
    let resolve = |addr: GKRAddress| -> Option<ResolvedColumn> {
        let GKRAddress::Setup(column) = addr else {
            return None;
        };
        let base = 0x1000_0000usize + column as usize * 0x0100_0000;
        Some(ResolvedColumn {
            is_e4: false,
            ptr: base as *const u8,
            matrix_base: base as *mut u8,
            stride_bytes: COUNT * 4,
        })
    };
    let err = lower_layer_desc(&cl, &mock_header(), &resolve, &mock_challenge, None)
        .expect_err("65th per-matrix group must overflow the source windows");
    assert!(matches!(
        err,
        FwdVmLowerError::SourceWindowOverflow {
            window: 0,
            column: 64
        }
    ));
}

#[test]
fn col_remap_collision_is_a_hard_error() {
    use gkr_eval_ir::ReadPlace;
    let mut ctx = DagForwardContext::default();
    ctx.backings
        .read_slot_col(&ReadPlace::Setup { column: 0 }, OperandField::Base)
        .unwrap();
    ctx.backings
        .read_slot_col(&ReadPlace::Setup { column: 1 }, OperandField::Base)
        .unwrap();
    let cl = synthetic_layer(
        Program {
            instrs: vec![Instr::Add {
                field: OperandField::Base,
                sign: gpu_gkr_compiler::forward::isa::Sign::Plus,
                promote: false,
                operands: vec![
                    OperandLine::LogicalGlobal { slot: 0, col: 0 },
                    OperandLine::LogicalGlobal { slot: 0, col: 1 },
                ],
            }],
        },
        ctx,
    );
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
        FwdVmLowerError::SourceColRemapCollision {
            window: 0,
            matrix_col: 0
        }
    ));
}

#[test]
fn arg_derived_e4_overflow_is_a_hard_error_and_terminates() {
    use gkr_eval_ir::{ChallengeKey, ChallengePower};
    let mut ctx = DagForwardContext::default();
    for i in 0..(ARG_DERIVED_E4_CAP as u32 + 1) {
        ctx.derived_e4.intern(&ChallengeRef {
            key: ChallengeKey::PermutationAdditive,
            power: ChallengePower::Static(i),
        });
    }
    let cl = synthetic_layer(Program::default(), ctx);
    // The probe loop must terminate (bounded at cap + 1) rather than wrap
    // `n as u16` and spin forever on an oversized bank.
    let err = lower_layer_desc(&cl, &mock_header(), &no_columns, &mock_challenge, None)
        .expect_err("ARG_DERIVED_E4_CAP+1 derived E4 values must overflow");
    assert!(matches!(
        err,
        FwdVmLowerError::ArgDerivedE4Overflow { n } if n == ARG_DERIVED_E4_CAP + 1
    ));
}

// ── wire-slot census (Finding-2 gate) ────────────────────────────────────────
// Production flat storage backs CopyAlias cache/output columns as VIEWS into
// OTHER consolidated matrices, so a compile-time slot's columns can span
// several `(matrix_base, stride)` groups. The lowering splits each compile
// slot into one WIRE slot per group; the destination wire format has
// DST_SLOT_COUNT (16)
// slots, so the census below — the CPU model of the exact grouping the
// lowering performs, keyed by the storage matrix identity
// `(canonical_layer, AddressClass, FieldType)` (one consolidated backing per
// key, `storage/views.rs`) — must stay ≤ DST_SLOT_COUNT for EVERY layer of EVERY
// committed fixture. A failure here means SLOT_BITS no longer suffices
// (spec-level decision), not a lowering bug.

const ALL_LAYOUT_FIXTURES: [&str; 11] = [
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "inits_and_teardowns_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
];

/// `_preprocessed` layout variants commit their schedule under the bare stem
/// (same reverse-trim note as `gkr_eval_isa/tests/common/mod.rs`).
fn schedule_stem(name: &str) -> &str {
    name.trim_end_matches("_preprocessed_layout_gkr.json")
        .trim_end_matches("_layout_gkr.json")
}

fn load_compiled_with_artifact(
    name: &str,
) -> (CompiledCircuit, cs::gkr_compiler::GKRCircuitArtifact<BF>) {
    let artifact: cs::gkr_compiler::GKRCircuitArtifact<BF> =
        crate::prover::tests::deserialize_json_for_test(&format!("cs/compiled_circuits/{name}"));
    let dag = lower_dag(&artifact).unwrap();
    validate(&dag).unwrap();
    let schedule_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../cs/compiled_circuits")
        .join(format!("{}_schedule_b16_gkr.json", schedule_stem(name)));
    let sched = load_committed_schedule(&schedule_path).unwrap();
    validate_forward_artifact(&dag, &sched).unwrap();
    (compile_circuit(&dag, &sched).unwrap(), artifact)
}

#[test]
fn wire_slot_census_fits_slot_count_on_all_fixtures() {
    use gpu_gkr_model::storage_layout::{address_storage_layer, GpuGKRStorageLayout};

    let mut max_wire = 0usize;
    let mut max_at = String::new();
    for name in ALL_LAYOUT_FIXTURES {
        let (compiled, artifact) = load_compiled_with_artifact(name);
        let layout = GpuGKRStorageLayout::from_artifact(&artifact);
        for (li, cl) in compiled.layers.iter().enumerate() {
            let backings = &cl.ctx.backings;
            let mut compile_slots = 0usize;
            let mut wire_slots = 0usize;
            for slot in 0..DST_SLOT_COUNT as u8 {
                if backings.slot_field(slot).is_none() {
                    continue;
                }
                compile_slots += 1;
                let mut groups = BTreeSet::new();
                for col in 0..backings.slot_columns(slot).len() as u16 {
                    let place = backings.slot_col_to_read_place(slot, col).unwrap();
                    let addr = read_place_to_gkr_address(&place);
                    let (canonical_layer, class, field, _poly_idx) = layout
                        .lookup(address_storage_layer(addr), &addr)
                        .unwrap_or_else(|| {
                            panic!("{name} L{li}: {addr:?} missing from storage layout")
                        });
                    groups.insert((canonical_layer, class, field));
                }
                wire_slots += groups.len();
            }
            if wire_slots > 0 {
                eprintln!(
                    "[wire-slot census] {name} L{li}: {compile_slots} compile slots -> \
                     {wire_slots} wire slots"
                );
            }
            if wire_slots > max_wire {
                max_wire = wire_slots;
                max_at = format!("{name} L{li}");
            }
            assert!(
                wire_slots <= DST_SLOT_COUNT,
                "{name} L{li}: {wire_slots} wire slots exceed \
                 DST_SLOT_COUNT={DST_SLOT_COUNT} — \
                 SLOT_BITS is no longer sufficient (spec-level decision required)"
            );
        }
    }
    eprintln!("[wire-slot census] max = {max_wire} wire slots at {max_at}");
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
