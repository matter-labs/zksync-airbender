//! Phase-3 Task 3.2: the GATHER INDEX-PATH ORACLE (spec R10).
//!
//! Proves the v2 interpreter resolves each gather descriptor THROUGH its index
//! arithmetic per row. The tables are ROW-VARYING and the mappings are
//! NON-TRIVIAL (non-identity permutations), so a constant fill cannot hide a
//! stride / off-by-one / mapping bug — `resolve_gather` must read the value
//! table via `mapping[gid]` (mapped variants) or `gid` (row-indexed) for the
//! per-row expectation to hold.
//!
//! Decoder reference (CUDA `lookup_helpers.cuh:58-69`, Rust
//! `cache_relation.rs:382-419`): a decoder-mapped gather reads `n[mapping[gid]]`,
//! then applies a per-row base-field PREDICATE mask `decoder_mask[gid]`; on the
//! masked-out branch (`mask.limb == 0`) it substitutes the FILL scalar
//! `α^fill_alpha_power · table_id` (`gkr_forward_setup_generic_lookup:409-413`).
//! The interpreter computes that fill itself from `DecoderSpec` + the α-power
//! bank — it is not handed a pre-resolved value (spec finding 1).

use field::{Field, PrimeField};
use gkr_eval_isa::compiler_v2::gather::{DecoderSpec, GatherDescriptor};
use gkr_eval_isa::eval_ref::{Bf, Ext, lift};
use gkr_eval_isa::interp_v2::*;
use gkr_eval_isa::isa_v2::*;

fn bf(v: u32) -> Bf {
    Bf::from_u32_with_reduction(v)
}

/// Build a descriptor of the given kind. `decoder` is attached only for the
/// decoder variant; the slot/len fields are not read by `resolve_gather`.
fn descriptor(
    kind: IndirectKind,
    field_ext: bool,
    decoder: Option<DecoderSpec>,
) -> GatherDescriptor {
    GatherDescriptor {
        kind,
        field_ext,
        n_slot: None,
        mapping_slot: None,
        n_len: None,
        decoder,
        inits_td_set_idx: None,
    }
}

#[test]
fn gather_tracks_table_mapping_per_row() {
    // ----------------------------------------------------------------------
    // Descriptor 0: MappedVirtualBf (SingleColumnLookup, base).
    // Descriptor 1: MappedGenericE4 (VectorizedLookup plain, ext).
    //   Both read n[mapping[gid]] through a per-row mapping. Use a value table
    //   whose entries differ from their indices (row-varying), and a mapping
    //   that is a NON-IDENTITY permutation so any stride/off-by-one bug in the
    //   index path surfaces.
    //
    //   value table n      = [100, 101, 102, 103, 104]   (n[i] = 100 + i)
    //   mapping            = [4, 2, 0, 3, 1]              (reversed-ish perm)
    //   so resolve(gid) == n[mapping[gid]] == 100 + mapping[gid]:
    //     gid 0 -> n[4] = 104,  gid 1 -> n[2] = 102,  gid 2 -> n[0] = 100,
    //     gid 3 -> n[3] = 103,  gid 4 -> n[1] = 101.
    // ----------------------------------------------------------------------
    let value_table: Vec<Ext> = (0..5).map(|i| lift(bf(100 + i))).collect();
    let mapping: Vec<u32> = vec![4, 2, 0, 3, 1];
    let expected_mapped: Vec<Ext> = mapping.iter().map(|&m| lift(bf(100 + m))).collect();

    // ----------------------------------------------------------------------
    // Descriptor 2: DecoderMappedE4 (VectorizedLookup w/ decoder, ext).
    //   Same mapped read, plus a per-row predicate. decoder_mask[gid] is a
    //   base-field flag: mask != 0 => use n[mapping[gid]]; mask == 0 => fill.
    //   The fill scalar is computed by the interpreter as
    //     α^fill_alpha_power · table_id
    //   from the α-power bank + DecoderSpec (NOT handed in pre-resolved).
    //
    //   mask = [1, 0, 1, 0, 1]: rows 1 and 3 are masked out (use fill).
    //   fill_alpha_power = 3, table_id = 7, α = 2 (lifted):
    //     α^3 = 8, fill = 8 * 7 = 56.
    // ----------------------------------------------------------------------
    let alpha = lift(bf(2));
    // α-power bank: alpha_powers[k] = α^k.
    let mut alpha_powers = vec![Ext::ONE];
    for _ in 1..6 {
        let mut next = *alpha_powers.last().unwrap();
        next.mul_assign(&alpha);
        alpha_powers.push(next);
    }
    let fill_alpha_power: u16 = 3;
    let table_id: u32 = 7;
    // fill = α^3 * table_id = 8 * 7 = 56.
    let mut fill = alpha_powers[fill_alpha_power as usize];
    fill.mul_assign(&lift(bf(table_id)));
    let decoder_mask: Vec<Bf> = vec![bf(1), bf(0), bf(1), bf(0), bf(1)];

    // ----------------------------------------------------------------------
    // Descriptor 3: RowIndexedSetupE4 (VectorizedLookupSetup, ext).
    //   No mapping: read n[gid], zero-padded beyond n_len. Use a DISTINCT
    //   row-varying value table so a wrong-descriptor index would be caught.
    //   n_setup = [200, 201, 202], n_len = 3: gids 0..2 read the table,
    //   gid 3 (out of range) must return Ext::ZERO (length guard).
    // ----------------------------------------------------------------------
    let setup_table: Vec<Ext> = (0..3).map(|i| lift(bf(200 + i))).collect();
    let setup_len = setup_table.len();

    // Assemble the per-descriptor tables. Index by descriptor index.
    let tables = GatherTables {
        n: vec![
            value_table.clone(),
            value_table.clone(),
            value_table.clone(),
            setup_table.clone(),
        ],
        mapping: vec![
            mapping.clone(),
            mapping.clone(),
            mapping.clone(),
            Vec::new(),
        ],
        n_len: vec![None, None, None, Some(setup_len)],
        decoder_mask: vec![None, None, Some(decoder_mask.clone()), None],
        alpha_powers: alpha_powers.clone(),
    };

    let d_mapped_bf = descriptor(IndirectKind::MappedVirtualBf, false, None);
    let d_mapped_e4 = descriptor(IndirectKind::MappedGenericE4, true, None);
    let d_decoder = descriptor(
        IndirectKind::DecoderMappedE4,
        true,
        Some(DecoderSpec {
            fill_alpha_power,
            table_id,
        }),
    );
    let d_setup = descriptor(IndirectKind::RowIndexedSetupE4, true, None);

    // --- MappedVirtualBf (desc 0) and MappedGenericE4 (desc 1): per row ---
    for gid in 0..mapping.len() {
        assert_eq!(
            resolve_gather(&d_mapped_bf, gid, &tables, 0),
            expected_mapped[gid],
            "MappedVirtualBf gid {gid}: expected n[mapping[{gid}]] = n[{}]",
            mapping[gid]
        );
        assert_eq!(
            resolve_gather(&d_mapped_e4, gid, &tables, 1),
            expected_mapped[gid],
            "MappedGenericE4 gid {gid}: expected n[mapping[{gid}]] = n[{}]",
            mapping[gid]
        );
    }
    // Caught-bug witness: a non-identity mapping means resolve(gid) != n[gid]
    // for the permuted rows. gid 0 maps to row 4, so it must NOT equal n[0].
    assert_ne!(
        resolve_gather(&d_mapped_e4, 0, &tables, 1),
        value_table[0],
        "non-identity mapping: resolve(0) must be n[mapping[0]]=n[4], not n[0]"
    );

    // --- DecoderMappedE4 (desc 2): in-range branch AND masked-out branch ---
    for gid in 0..mapping.len() {
        let got = resolve_gather(&d_decoder, gid, &tables, 2);
        if decoder_mask[gid].is_zero() {
            // masked out -> fill scalar α^fill_alpha_power * table_id.
            assert_eq!(
                got, fill,
                "DecoderMappedE4 gid {gid}: masked out, expected fill"
            );
        } else {
            // enabled -> mapped value n[mapping[gid]].
            assert_eq!(
                got, expected_mapped[gid],
                "DecoderMappedE4 gid {gid}: enabled, expected mapped n[{}]",
                mapping[gid]
            );
        }
    }
    // Explicit branch witnesses: gid 0 enabled (mapped), gid 1 masked (fill).
    assert_eq!(
        resolve_gather(&d_decoder, 0, &tables, 2),
        expected_mapped[0]
    );
    assert_eq!(resolve_gather(&d_decoder, 1, &tables, 2), fill);

    // --- RowIndexedSetupE4 (desc 3): n[gid] in range, ZERO out of range ---
    for gid in 0..setup_len {
        assert_eq!(
            resolve_gather(&d_setup, gid, &tables, 3),
            setup_table[gid],
            "RowIndexedSetupE4 gid {gid}: expected n[{gid}] = {}",
            200 + gid
        );
    }
    // Out-of-range row exercises the LOOKUP_SETUP length guard -> Ext::ZERO.
    assert_eq!(
        resolve_gather(&d_setup, setup_len, &tables, 3),
        Ext::ZERO,
        "RowIndexedSetupE4 gid {setup_len} >= n_len {setup_len}: expected ZERO"
    );
}

// ===========================================================================
// Task 3.3: END-TO-END VALUE ORACLE for `execute2`'s macro routines.
//
// Cross-checks the routine arithmetic the interpreter computes against a
// HAND-WRITTEN reference using a DIFFERENT decomposition / summation order
// (catches transcription slips), driven by the REAL fixtures' emitted
// instructions (add_sub / bigint / blake2_g_function — the cached variants).
//
// HONESTY (spec §7 step 2): `cs` has NO numeric relation evaluator, so this
// reference is hand-written and SHARES the .cuh / `bench_interp` host model as
// its source of truth. The achievable independence here is a DIFFERENT
// DECOMPOSITION (e.g. den-then-num, factored cross-products), NOT bug
// independence — a shared transcription error in the .cuh anchor would fool
// both sides. Real independence is the Phase-5 GPU cross-check, not this test.
//
// SCOPE (STEP-0 probe + the `exec_macro` doc): with the finer Task-R1 RoutineId
// set the three fixtures emit a spread of ids (probe: every layer) covering
// `Product` (1), `MaskIdentity` (2), `AggregateLookupPair` (3), the lookup
// num/den pair ids (4..=9), and the cache ids (16..=19). R3 IMPLEMENTS ALL of
// them in the CPU interpreter; the only routines NOT emitted by the corpus are
// ids 14/15 (grand-product-without-caches) and 20 (memory-init/teardown pair),
// which therefore stay `todo!` and are never reached.
//
// This first test (`interpreter_matches_hand_reference`) is the ORIGINAL
// Phase-3 oracle for the two routines whose formula the `Instr2` pins WITHOUT
// any challenge bank — `Product` and `AggregateLookupPair`. It feeds controlled
// random values through `Affine` lanes (the routine arithmetic depends only on
// the operand VALUES, not the lane KIND), exercising the fold + the multi-output
// (num,den → two dsts) footer wiring. The newer
// `interpreter_matches_hand_reference_real_instrs` test below drives `execute2`
// over the REAL emitted instruction lane layouts (every R3 routine) with banks
// staged from a deterministic seed — see its own header for the end-to-end vs
// per-instruction scope decision.
// ===========================================================================

use gkr_eval_isa::compiler_v2::{compile_forward_v2, FwdParams2};
use gkr_eval_isa::test_support::{all_fixtures, fixture_path, rand_ext};
use gkr_design_space::import::load_circuit;
use rand::{rngs::StdRng, SeedableRng};
use std::collections::BTreeSet;

/// One synthetic ext-field matrix slot whose columns are the controlled operand
/// values for a single extracted macro instruction; the instruction's operands
/// are rewritten to `Affine { slot: 0, col: k }` so `execute2` reads value `k`.
fn ext_slot(values: &[Ext]) -> MatrixSlotData {
    MatrixSlotData { field_ext: true, columns: values.to_vec() }
}

fn banks_with(values: &[Ext]) -> SourceBanks {
    SourceBanks {
        matrix: vec![ext_slot(values)],
        consts: vec![],
        const_challenge: vec![],
        arg_challenge: vec![],
        gamma: Ext::ZERO,
        perm_challenges: vec![],
        perm_additive: Ext::ZERO,
        gather_tables: GatherTables::default(),
        gid: 0,
    }
}

/// Build a single-instruction `Program2` that runs `routine` over `n_operands`
/// controlled values (read as `Affine { slot:0, col:k }`) and materializes its
/// `output_count` outputs into a fresh ext slot (slot 0, cols starting past the
/// operand columns so a store never clobbers an operand read).
fn one_macro_program(routine: RoutineId, n_operands: usize, output_count: usize) -> Program2 {
    let operands: Vec<Operand> =
        (0..n_operands).map(|k| Operand::Affine { slot: 0, col: k as u16 }).collect();
    // Materialize cols sit AFTER the operand cols (distinct columns; the slot
    // vector is sized to cover both in the harness below).
    let dsts: Vec<Dst> = (0..output_count)
        .map(|j| Dst::Materialize { slot: 0, col: (n_operands + j) as u16 })
        .collect();
    Program2 {
        instrs: vec![Instr2 {
            header: Header::Macro { routine: routine as u8, n_operands: n_operands as u8 },
            operands,
            dsts,
            memtup: None,
            memtup2: None,
        }],
        consts: vec![],
        n_slot_cells: 0,
        n_matrix_slots: 1,
    }
}

/// Run `routine` over `inputs` via `execute2` and return the materialized
/// outputs in dst (num-then-den) order.
fn run_macro(routine: RoutineId, inputs: &[Ext], output_count: usize) -> Vec<Ext> {
    // Slot columns: the operand values, then `output_count` zero placeholders
    // the Materialize footers will read their store FIELD from (not the value).
    let mut cols = inputs.to_vec();
    cols.extend(std::iter::repeat(Ext::ZERO).take(output_count));
    let p = one_macro_program(routine, inputs.len(), output_count);
    let src = banks_with(&cols);
    let got = execute2(&p, &[], &src);
    got.materialized.iter().map(|(_, v)| *v).collect()
}

/// HAND reference for `Product` (id 1, `out = a·b`). DIFFERENT decomposition: the
/// interpreter computes `a·b` directly; here we route through a one-element
/// running accumulator (`acc *= a; acc *= b`) so the multiply order/assoc is
/// re-expressed rather than copied.
fn ref_grand_product(a: Ext, b: Ext) -> Ext {
    let mut acc = Ext::ONE;
    acc.mul_assign(&a);
    acc.mul_assign(&b);
    acc
}

/// HAND reference for `AggregateLookupPair` (id 3): combine `(a,b)`,`(c,d)`.
/// Reference formula `num = a·d + c·b`, `den = b·d`. DIFFERENT decomposition:
/// compute den FIRST, and form the numerator as `c·b + d·a` (operands swapped
/// within each product and the two products added in the reverse order) so a
/// mis-bound operand or a swapped cross-term in the impl would diverge.
fn ref_aggregate_pair(a: Ext, b: Ext, c: Ext, d: Ext) -> (Ext, Ext) {
    let mut den = d;
    den.mul_assign(&b); // den = d·b  (== b·d, commuted)
    let mut t0 = c;
    t0.mul_assign(&b); // c·b
    let mut t1 = d;
    t1.mul_assign(&a); // d·a  (== a·d, commuted)
    let mut num = t0;
    num.add_assign(&t1); // num = c·b + d·a  (reverse add order)
    (num, den)
}

#[test]
fn interpreter_matches_hand_reference() {
    // The three target fixtures (cached variants).
    let targets = [
        "add_sub_lui_auipc_mop_codegen_ir_gkr.json",
        "bigint_with_extended_control_codegen_ir_gkr.json",
        "blake2_g_function_codegen_ir_gkr.json",
    ];

    // Non-vacuity + scope accounting across the corpus.
    let mut total_grand_product = 0usize;
    let mut total_aggregate = 0usize;
    // The emitted-but-intentionally-todo routine ids, to document the gap.
    let mut emitted_unpinned: BTreeSet<u8> = BTreeSet::new();

    for name in targets {
        let p = fixture_path(name);
        // `fixture_path` resolves under cs/compiled_circuits; assert the helper
        // and the curated 22-fixture corpus still see the target.
        assert!(p.exists(), "target fixture {name} missing");
        assert!(
            all_fixtures().iter().any(|f| f == &p),
            "{name} not in the curated codegen_ir corpus"
        );
        let c = load_circuit(&p).unwrap_or_else(|e| panic!("load {name}: {e:?}"));

        for (li, layer) in c.circuit.layers.iter().enumerate() {
            let Some(g) = c.graphs.get(li) else { continue };
            let cf = compile_forward_v2(layer, g, FwdParams2::default());

            // Deterministic per-(fixture,layer) RNG (no Date.now / time seed).
            let seed = 0xA11C_E5_u64 ^ ((name.len() as u64) << 40) ^ ((li as u64) << 8);
            let mut rng = StdRng::seed_from_u64(seed);

            for ins in &cf.program.instrs {
                let Header::Macro { routine, n_operands } = ins.header else { continue };
                match routine {
                    // id 1 — Product: a·b. Two ext operands, 1 output.
                    x if x == RoutineId::Product as u8 => {
                        assert_eq!(n_operands, 2, "{name} L{li}: Product arity != 2");
                        assert_eq!(ins.dsts.len(), 1, "{name} L{li}: Product 1 dst");
                        let a = rand_ext(&mut rng, true);
                        let b = rand_ext(&mut rng, true);
                        let got = run_macro(RoutineId::Product, &[a, b], 1);
                        assert_eq!(got.len(), 1);
                        assert_eq!(
                            got[0],
                            ref_grand_product(a, b),
                            "{name} L{li}: Product value mismatch"
                        );
                        total_grand_product += 1;
                    }
                    // id 3 — AggregateLookupPair: (num,den). Four ext operands,
                    // 2 outputs (num then den).
                    x if x == RoutineId::AggregateLookupPair as u8 => {
                        assert_eq!(n_operands, 4, "{name} L{li}: AggregateLookupPair arity != 4");
                        assert_eq!(
                            ins.dsts.len(),
                            2,
                            "{name} L{li}: AggregateLookupPair must emit num+den dsts"
                        );
                        let a = rand_ext(&mut rng, true);
                        let b = rand_ext(&mut rng, true);
                        let cc = rand_ext(&mut rng, true);
                        let d = rand_ext(&mut rng, true);
                        let got = run_macro(RoutineId::AggregateLookupPair, &[a, b, cc, d], 2);
                        assert_eq!(got.len(), 2, "two materialized outputs (num, den)");
                        let (rnum, rden) = ref_aggregate_pair(a, b, cc, d);
                        assert_eq!(got[0], rnum, "{name} L{li}: AggregateLookupPair num mismatch");
                        assert_eq!(got[1], rden, "{name} L{li}: AggregateLookupPair den mismatch");
                        // Multi-output wiring: num and den must be DISTINCT values
                        // (a single-value broadcast bug would make them equal for
                        // generic random inputs).
                        assert_ne!(
                            got[0], got[1],
                            "{name} L{li}: num == den for random inputs — multi-output footer \
                             collapsed to a broadcast?"
                        );
                        total_aggregate += 1;
                    }
                    // Other emitted routines: record the id (this test only
                    // covers the two challenge-free routines; the comprehensive
                    // `..._real_instrs` test below exercises the rest).
                    other => {
                        emitted_unpinned.insert(other);
                    }
                }
            }
        }
    }

    // Non-vacuity: both routines must actually appear in the corpus.
    assert!(
        total_grand_product > 0,
        "no Product instrs across the target fixtures (oracle vacuous)"
    );
    assert!(
        total_aggregate > 0,
        "no AggregateLookupPair instrs across the target fixtures (oracle vacuous)"
    );

    // The corpus DOES emit the other R3 routines (covered by the
    // `..._real_instrs` test below). Each appears across the target fixtures.
    for expected in [
        RoutineId::MaskIdentity as u8,
        RoutineId::LookupBasePair as u8,
        RoutineId::LookupBaseMinusMult as u8,
        RoutineId::LookupUnbalancedBase as u8,
        RoutineId::SingleColumnLookup as u8,
        RoutineId::MemoryTuple as u8,
        RoutineId::VectorizedLookup as u8,
        RoutineId::VectorizedLookupSetup as u8,
    ] {
        assert!(
            emitted_unpinned.contains(&expected),
            "expected the corpus to emit routine id {expected} (probe STEP 0)"
        );
    }
}

// ===========================================================================
// R3 Stage 2: REAL-INSTRUCTION end-to-end value oracle.
//
// For each target fixture × layer × emitted macro instruction, this runs the
// ACTUAL emitted `Instr2` (its real Affine/Ldc/Indirect lane layout, real dst
// count, real memtup role/const block) through `execute2`, with a `SourceBanks`
// staged from a DETERMINISTIC seeded random row (no time source) — random matrix
// columns, γ, per-role perm challenges, perm_additive, an α-power bank, and the
// program's real `consts`. It then asserts every materialized output equals an
// INDEPENDENT reference that decodes the SAME instruction lanes with a DIFFERENT
// decomposition (re-ordered products/sums, commuted cross-terms, the lincomb /
// vector-lookup / memory-tuple folds re-expanded outside-in).
//
// SCOPE — PER REAL INSTRUCTION, not a chained whole-program run. A chained
// whole-program `execute2` would additionally need each gather descriptor's
// table (`n`/`mapping`/`n_len`/`decoder_mask`/α-bank) staged to the reference
// CACHE value at the resolved row — but the descriptor→cache-address mapping is
// internal to the gather builder and NOT exposed on `CompiledForward2`, and the
// decoder fill α-power / table-id are left `None` by `build_descriptor` for the
// Phase-3 launcher to resolve. So a faithful whole-program SourceBanks cannot be
// assembled from the public compile output today. Driving each REAL instruction
// in isolation over staged banks is the sound, non-faking subset: it validates
// the FULL lane DECODE of every emitted shape (constant/coeff/term-count
// positions, γ-shift placement, memtup roles + folded-const roles, multi-output
// num/den footer) for every R3 routine the corpus emits — which is the routine
// arithmetic this task implements.
//
// HONESTY: the reference shares the .cuh / `bench_interp` host model as its
// source of truth (`cs` has no numeric relation evaluator), so the independence
// is DECOMPOSITION-only, NOT bug-independence — a shared .cuh transcription error
// would fool both sides. The Phase-5 GPU cross-check is the real bug-independent
// oracle. The `read` of a banked value is shared with `execute2` on purpose (it
// is not the thing under test); the LANE INTERPRETATION (which lane is which
// operand + the per-routine formula) is what is re-derived independently here.
// ===========================================================================

use field::FieldExtension;
use gkr_eval_isa::isa_v2::{LdcSub, SPECIAL_NEG_ONE, SPECIAL_ONE, SPECIAL_ZERO};

// Memory-tuple folded-constant role tags (isa_v2) + the special-indirect dyn
// term slot — mirrored here for the independent memtup reference decode.
use gkr_eval_isa::isa_v2::{
    MT_CONST_ADDR_HIGH, MT_CONST_ADDR_LOW, MT_CONST_ADDR_LOW_DYN_COEFF, MT_CONST_ADDR_LOW_OFFSET,
    MT_CONST_TS_LOW_OFFSET,
};
const REF_MEMTUP_VALUE_HIGH_EXTRA_TERM: u8 = 7;
// perm-challenge role indices (independent restatement of interp_v2's R_PERM_*).
const REF_R_ADDR_LOW: usize = 0;
const REF_R_ADDR_HIGH: usize = 1;
const REF_R_TS_LOW: usize = 2;
const REF_R_TS_HIGH: usize = 3;
const REF_R_VAL_LOW: usize = 4;
const REF_R_VAL_HIGH: usize = 5;

fn ref_perm_role_for_term(term: u8) -> usize {
    match term {
        0 => REF_R_ADDR_LOW,
        1 => REF_R_ADDR_HIGH,
        2 => REF_R_TS_LOW,
        3 => REF_R_TS_HIGH,
        4 => REF_R_VAL_LOW,
        6 => REF_R_VAL_HIGH,
        other => panic!("ref: memtup term {other} has no direct perm role"),
    }
}

/// Number of matrix slots / max column the staged banks must cover, scanned off
/// one instruction's lanes (operands, memtup roles/payload/consts).
fn slot_col_extent(ins: &Instr2) -> (usize, Vec<usize>) {
    let mut max_col_per_slot: Vec<usize> = Vec::new();
    let bump = |slot: u8, col: u16, m: &mut Vec<usize>| {
        let s = slot as usize;
        if m.len() <= s {
            m.resize(s + 1, 0);
        }
        m[s] = m[s].max(col as usize);
    };
    let scan = |op: &Operand, m: &mut Vec<usize>| {
        if let Operand::Affine { slot, col } = op {
            bump(*slot, *col, m);
        }
    };
    for o in &ins.operands {
        scan(o, &mut max_col_per_slot);
    }
    // Both tuples (memtup2 is Some for the id-14/20 products).
    for mt in [ins.memtup.as_ref(), ins.memtup2.as_ref()].into_iter().flatten() {
        for (_r, o) in &mt.roles {
            scan(o, &mut max_col_per_slot);
        }
        if let Some(p) = &mt.as_payload {
            scan(p, &mut max_col_per_slot);
        }
        for (_r, o) in &mt.consts {
            scan(o, &mut max_col_per_slot);
        }
    }
    (max_col_per_slot.len(), max_col_per_slot)
}

/// Collect the distinct `Indirect` descriptor indices referenced by an
/// instruction's lanes (operands + memtup payload/roles/consts — the corpus only
/// puts Indirect in plain operands, but scanning all is safe).
fn indirect_descs(ins: &Instr2) -> Vec<u16> {
    let mut descs: Vec<u16> = Vec::new();
    let note = |op: &Operand, d: &mut Vec<u16>| {
        if let Operand::Indirect { desc, .. } = op {
            if !d.contains(desc) {
                d.push(*desc);
            }
        }
    };
    for o in &ins.operands {
        note(o, &mut descs);
    }
    for mt in [ins.memtup.as_ref(), ins.memtup2.as_ref()].into_iter().flatten() {
        for (_r, o) in &mt.roles {
            note(o, &mut descs);
        }
        if let Some(p) = &mt.as_payload {
            note(p, &mut descs);
        }
        for (_r, o) in &mt.consts {
            note(o, &mut descs);
        }
    }
    descs
}

/// Build deterministic-random staged banks covering one instruction's slots,
/// the program's `consts`, and random γ / 6 perm challenges / perm_additive /
/// an α-power bank wide enough for any VectorizedLookup column count. Also stages
/// a gather table + descriptor array so EVERY `Indirect` operand the instruction
/// references (a cached-value lane) resolves to a known random value at gid 0:
/// each referenced descriptor is a `RowIndexedSetupE4` with `n[desc] = [value]`,
/// `n_len = Some(1)`, gid 0. The cache VALUES the forward path would gather are
/// not recoverable from the public compile output (see the test header), so they
/// are modeled here as fresh staged values — `execute2` and the reference both
/// read THE SAME value through `resolve_gather`, exercising the routine fold over
/// a faithfully-shaped (cached + committed + const) operand mix.
fn staged_banks(ins: &Instr2, consts: &[u32], rng: &mut StdRng) -> (SourceBanks, Vec<GatherDescriptor>) {
    let (n_slots, max_col) = slot_col_extent(ins);
    let matrix: Vec<MatrixSlotData> = (0..n_slots.max(1))
        .map(|s| {
            let width = max_col.get(s).copied().unwrap_or(0) + 1;
            MatrixSlotData {
                field_ext: true,
                columns: (0..width).map(|_| rand_ext(rng, true)).collect(),
            }
        })
        .collect();
    // α-power bank: const_challenge[k] = α^k (entry 0 unused — α^0 is a free lift).
    let alpha = rand_ext(rng, true);
    let mut const_challenge = vec![Ext::ZERO];
    let mut p = Ext::ONE;
    for _ in 1..32 {
        p.mul_assign(&alpha);
        const_challenge.push(p);
    }
    let perm_challenges: Vec<Ext> = (0..6).map(|_| rand_ext(rng, true)).collect();

    // Gather tables: one entry per descriptor index up to the max referenced.
    let referenced = indirect_descs(ins);
    let max_desc = referenced.iter().copied().max().map(|m| m as usize + 1).unwrap_or(0);
    let mut n: Vec<Vec<Ext>> = vec![Vec::new(); max_desc];
    let mut n_len: Vec<Option<usize>> = vec![None; max_desc];
    let mut descriptors: Vec<GatherDescriptor> = (0..max_desc)
        .map(|_| GatherDescriptor {
            // A placeholder kind for unreferenced gaps; referenced ones are set below.
            kind: IndirectKind::RowIndexedSetupE4,
            field_ext: true,
            n_slot: None,
            mapping_slot: None,
            n_len: None,
            decoder: None,
            inits_td_set_idx: None,
        })
        .collect();
    for d in referenced {
        let di = d as usize;
        n[di] = vec![rand_ext(rng, true)];
        n_len[di] = Some(1);
        descriptors[di].kind = IndirectKind::RowIndexedSetupE4;
    }
    // R4: an id-20 MT_CONST_ADDR_HIGH lane is a launcher-deferred
    // `InitsTeardownsHighAddr` gather. Tag those descriptors with that kind so the
    // staged read exercises `resolve_gather`'s actual arm (a row-independent
    // scalar at n[desc][0], identical in value to RowIndexedSetupE4 at gid 0).
    for mt in [ins.memtup.as_ref(), ins.memtup2.as_ref()].into_iter().flatten() {
        for (role, op) in &mt.consts {
            if *role == MT_CONST_ADDR_HIGH {
                if let Operand::Indirect { desc, .. } = op {
                    let di = *desc as usize;
                    descriptors[di].kind = IndirectKind::InitsTeardownsHighAddr;
                    descriptors[di].inits_td_set_idx = Some(0);
                }
            }
        }
    }
    let gather_tables = GatherTables {
        n,
        mapping: vec![Vec::new(); max_desc],
        n_len,
        decoder_mask: vec![None; max_desc],
        alpha_powers: vec![],
    };

    let src = SourceBanks {
        matrix,
        consts: consts.to_vec(),
        const_challenge,
        arg_challenge: vec![],
        gamma: rand_ext(rng, true),
        perm_challenges,
        perm_additive: rand_ext(rng, true),
        gather_tables,
        gid: 0,
    };
    (src, descriptors)
}

/// Resolve one operand against the staged banks — SHARED with `execute2`'s read
/// (the bank read is NOT the thing under test; the LANE INTERPRETATION is).
/// Indirect resolves via the public `resolve_gather` against the staged
/// descriptor array, exactly as `execute2` does.
fn ref_read(op: &Operand, src: &SourceBanks, descs: &[GatherDescriptor]) -> Ext {
    match *op {
        Operand::Affine { slot, col } => src.matrix[slot as usize].columns[col as usize],
        Operand::Ldc { sub, idx } => match sub {
            LdcSub::Special => match idx {
                SPECIAL_ZERO => Ext::ZERO,
                SPECIAL_ONE => Ext::ONE,
                SPECIAL_NEG_ONE => {
                    let mut v = Ext::ONE;
                    v.negate();
                    v
                }
                other => panic!("ref: bad Special idx {other}"),
            },
            LdcSub::Const => lift(Bf::from_u32_with_reduction(src.consts[idx as usize])),
            LdcSub::ConstChallenge => src.const_challenge[idx as usize],
            LdcSub::ArgChallenge => src.arg_challenge[idx as usize],
        },
        Operand::Indirect { desc, .. } => {
            resolve_gather(&descs[desc as usize], src.gid, &src.gather_tables, desc as usize)
        }
        Operand::Slot { .. } => panic!("ref_read: macro operands are never smem Slot in the corpus"),
    }
}

fn ref_sh(v: Ext, src: &SourceBanks) -> Ext {
    let mut r = v;
    r.add_assign(&src.gamma);
    r
}

/// Independent per-tuple fold (address-space arm, then role terms in REVERSE,
/// then folded consts) — the shared reference for the four memory-tuple routines
/// (id-15/19 materialize ONE tuple; id-14/20 multiply TWO). Mirrors
/// `interp_v2::tuple_value` with a different summation order. `descs` resolves any
/// Indirect lane (e.g. the id-20 launcher-deferred MT_CONST_ADDR_HIGH high bits).
fn ref_tuple(mt: &MemTup, src: &SourceBanks, descs: &[GatherDescriptor]) -> Ext {
    let mut acc = src.perm_additive;
    // address-space arm.
    match mt.as_arm {
        1 => {
            acc.add_assign(&ref_read(mt.as_payload.as_ref().unwrap(), src, descs));
        }
        2 => {
            let col = ref_read(mt.as_payload.as_ref().unwrap(), src, descs);
            let mut one_minus = Ext::ONE;
            one_minus.sub_assign(&col);
            acc.add_assign(&one_minus);
        }
        3 => {
            acc.add_assign(&ref_read(mt.as_payload.as_ref().unwrap(), src, descs));
        }
        0 => {}
        other => panic!("ref: as_arm {other}"),
    }
    // dyn-coeff (scales term-7 column).
    let mut dyn_coeff: Option<Ext> = None;
    for (role, op) in &mt.consts {
        if *role == MT_CONST_ADDR_LOW_DYN_COEFF {
            dyn_coeff = Some(ref_read(op, src, descs));
        }
    }
    // role terms, reverse order.
    for (term, op) in mt.roles.iter().rev() {
        let col = ref_read(op, src, descs);
        let chal = if *term == REF_MEMTUP_VALUE_HIGH_EXTRA_TERM {
            let mut c = src.perm_challenges[REF_R_ADDR_LOW];
            c.mul_assign(&dyn_coeff.expect("term-7 needs dyn coeff"));
            c
        } else {
            src.perm_challenges[ref_perm_role_for_term(*term)]
        };
        let mut t = col;
        t.mul_assign(&chal); // col·chal (commuted vs impl's chal·col).
        acc.add_assign(&t);
    }
    // folded consts last.
    for (role, op) in &mt.consts {
        let val = ref_read(op, src, descs);
        let role_idx = match *role {
            MT_CONST_ADDR_LOW | MT_CONST_ADDR_LOW_OFFSET => REF_R_ADDR_LOW,
            MT_CONST_ADDR_HIGH => REF_R_ADDR_HIGH,
            MT_CONST_TS_LOW_OFFSET => REF_R_TS_LOW,
            MT_CONST_ADDR_LOW_DYN_COEFF => continue,
            other => panic!("ref: const role {other}"),
        };
        let mut t = val;
        t.mul_assign(&src.perm_challenges[role_idx]);
        acc.add_assign(&t);
    }
    acc
}

/// Independent reference for one emitted macro instruction. Returns the expected
/// materialized outputs in dst order, computed with a DIFFERENT decomposition
/// than `exec_macro`. `None` for routines with no reference arm here.
fn ref_outputs(ins: &Instr2, src: &SourceBanks, descs: &[GatherDescriptor]) -> Option<Vec<Ext>> {
    let Header::Macro { routine, .. } = ins.header else {
        return None;
    };
    let ops = &ins.operands;
    let r = |k: usize| ref_read(&ops[k], src, descs);
    let out = match routine {
        // 1 Product: b·a (commuted).
        x if x == RoutineId::Product as u8 => {
            let mut v = r(1);
            v.mul_assign(&r(0));
            vec![v]
        }
        // 2 MaskIdentity: v·m − m + 1 (expanded).
        x if x == RoutineId::MaskIdentity as u8 => {
            let (v, m) = (r(0), r(1));
            let mut acc = v;
            acc.mul_assign(&m);
            acc.sub_assign(&m);
            acc.add_assign(&Ext::ONE);
            vec![acc]
        }
        // 3 AggregateLookupPair: den=d·b, num=c·b + d·a.
        x if x == RoutineId::AggregateLookupPair as u8 => {
            let (a, b, c, d) = (r(0), r(1), r(2), r(3));
            let mut den = d;
            den.mul_assign(&b);
            let mut t0 = c;
            t0.mul_assign(&b);
            let mut t1 = d;
            t1.mul_assign(&a);
            let mut num = t0;
            num.add_assign(&t1);
            vec![num, den]
        }
        // 4/5 lookup pair: num=sh(d)+sh(b), den=sh(d)·sh(b); lanes [b,d].
        x if x == RoutineId::LookupBasePair as u8 || x == RoutineId::LookupExtPair as u8 => {
            let b = ref_sh(r(0), src);
            let d = ref_sh(r(1), src);
            let mut num = d;
            num.add_assign(&b);
            let mut den = d;
            den.mul_assign(&b);
            vec![num, den]
        }
        // 6/7 minus-mult: num = −c·sh(b) + sh(d), den = sh(b)·sh(d); [b,c,d].
        x if x == RoutineId::LookupBaseMinusMult as u8
            || x == RoutineId::LookupExtMinusMult as u8 =>
        {
            let b = ref_sh(r(0), src);
            let c = r(1);
            let d = ref_sh(r(2), src);
            let mut ncb = c;
            ncb.mul_assign(&b);
            ncb.negate();
            let mut num = ncb;
            num.add_assign(&d);
            let mut den = b;
            den.mul_assign(&d);
            vec![num, den]
        }
        // 8/13 cached-dens: num = a·sh(d) + (−c·sh(b)), den = sh(b)·sh(d); [a,b,c,d].
        x if x == RoutineId::LookupCachedDens as u8
            || x == RoutineId::LookupDecoderDensSetup as u8 =>
        {
            let a = r(0);
            let b = ref_sh(r(1), src);
            let c = r(2);
            let d = ref_sh(r(3), src);
            let mut ad = a;
            ad.mul_assign(&d);
            let mut ncb = c;
            ncb.mul_assign(&b);
            ncb.negate();
            let mut num = ad;
            num.add_assign(&ncb);
            let mut den = b;
            den.mul_assign(&d);
            vec![num, den]
        }
        // 9/10 unbalanced: num = b + sh(d)·a, den = b·sh(d); [a,b,d].
        x if x == RoutineId::LookupUnbalancedBase as u8
            || x == RoutineId::LookupUnbalancedExt as u8 =>
        {
            let a = r(0);
            let b = r(1);
            let d = ref_sh(r(2), src);
            let mut da = d;
            da.mul_assign(&a);
            let mut num = b;
            num.add_assign(&da);
            let mut den = b;
            den.mul_assign(&d);
            vec![num, den]
        }
        // 12/16 single-column lincomb: const + Σ coeff·col (terms reverse order).
        x if x == RoutineId::SingleColumnLookup as u8
            || x == RoutineId::MaterializeSingleLookup as u8 =>
        {
            // lanes [const, (coeff,col)…]; accumulate terms back-to-front then add const.
            let mut acc = Ext::ZERO;
            let mut i = ops.len();
            while i > 1 {
                // (coeff at i-2, col at i-1)
                let mut t = r(i - 2);
                t.mul_assign(&r(i - 1));
                acc.add_assign(&t);
                i -= 2;
            }
            acc.add_assign(&r(0));
            vec![acc]
        }
        // 11/17 vectorized lookup: Σ_k α^k·(const_k + Σ coeff·col), self-describing.
        x if x == RoutineId::VectorizedLookup as u8 || x == RoutineId::VectorLookupGate as u8 => {
            // First decode the per-column sums, THEN fold by α-powers (outside the
            // per-column loop) — different structure from the impl's interleave.
            let mut col_sums: Vec<Ext> = Vec::new();
            let mut pos = 0usize;
            while pos < ops.len() {
                let tc = {
                    let v = r(pos);
                    let coeffs = <Ext as FieldExtension<Bf>>::into_coeffs(v);
                    coeffs[0].as_u32_reduced() as usize
                };
                pos += 1;
                let mut s = r(pos); // constant_k
                pos += 1;
                for _ in 0..tc {
                    let mut t = r(pos);
                    t.mul_assign(&r(pos + 1));
                    s.add_assign(&t);
                    pos += 2;
                }
                col_sums.push(s);
            }
            let mut acc = Ext::ZERO;
            for (k, s) in col_sums.iter().enumerate() {
                let mut t = *s;
                if k > 0 {
                    t.mul_assign(&src.const_challenge[k]);
                }
                acc.add_assign(&t);
            }
            vec![acc]
        }
        // 15 MaterializeGrandProductTerm + 19 MemoryTuple: ONE tuple value.
        x if x == RoutineId::MemoryTuple as u8
            || x == RoutineId::MaterializeGrandProductTerm as u8 =>
        {
            let mt = ins.memtup.as_ref().expect("single-tuple routine carries a MemTup");
            vec![ref_tuple(mt, src, descs)]
        }
        // 14 GrandProductWithoutCaches + 20 MemoryInitTeardownPair: the PRODUCT of
        // two tuples (id-20's are the inits/teardowns KEYs). The multiply order is
        // a free independence axis (commutative).
        x if x == RoutineId::GrandProductWithoutCaches as u8
            || x == RoutineId::MemoryInitTeardownPair as u8 =>
        {
            let t0 = ins.memtup.as_ref().expect("product routine carries memtup");
            let t1 = ins.memtup2.as_ref().expect("product routine carries memtup2");
            let mut v = ref_tuple(t1, src, descs);
            v.mul_assign(&ref_tuple(t0, src, descs)); // t1·t0 (commuted vs impl's t0·t1)
            vec![v]
        }
        // 18 VectorizedLookupSetup: the single RowIndexedSetupE4 gather value,
        // resolved through the staged descriptor (independent of the impl).
        x if x == RoutineId::VectorizedLookupSetup as u8 => {
            vec![r(0)]
        }
        // No reference arm (would be a genuinely-unhandled emitted routine).
        _ => return None,
    };
    Some(out)
}

#[test]
fn interpreter_matches_hand_reference_real_instrs() {
    // (fixture, products_only). The 3 caches fixtures drive EVERY emitted routine
    // (full R3 coverage). The `no_caches` + inits/teardowns fixtures are added
    // ONLY to reach the grand-product / inits-teardowns routines (id-14 in every
    // no_caches L0, id-15 in keccak_special5 no_caches, id-20 in both
    // inits_and_teardowns variants); for those we drive ONLY id-14/15/20, since
    // the no_caches variants also emit lincomb-form lookup pairs whose distinct
    // operand shape is a SEPARATE (pre-R4) interpreter concern, out of scope here.
    let targets: [(&str, bool); 7] = [
        ("add_sub_lui_auipc_mop_codegen_ir_gkr.json", false),
        ("bigint_with_extended_control_codegen_ir_gkr.json", false),
        ("blake2_g_function_codegen_ir_gkr.json", false),
        ("add_sub_lui_auipc_mop_codegen_ir_no_caches_gkr.json", true),
        ("keccak_special5_codegen_ir_no_caches_gkr.json", true),
        ("inits_and_teardowns_codegen_ir_gkr.json", true),
        ("inits_and_teardowns_codegen_ir_no_caches_gkr.json", true),
    ];
    let is_product_routine = |r: u8| {
        r == RoutineId::GrandProductWithoutCaches as u8
            || r == RoutineId::MaterializeGrandProductTerm as u8
            || r == RoutineId::MemoryInitTeardownPair as u8
    };
    // Per-routine coverage counts (non-vacuity + scope accounting).
    let mut counts: std::collections::BTreeMap<u8, usize> = std::collections::BTreeMap::new();

    for (name, products_only) in targets {
        let p = fixture_path(name);
        assert!(p.exists(), "target fixture {name} missing");
        let c = load_circuit(&p).unwrap_or_else(|e| panic!("load {name}: {e:?}"));
        for (li, layer) in c.circuit.layers.iter().enumerate() {
            let Some(g) = c.graphs.get(li) else { continue };
            let cf = compile_forward_v2(layer, g, FwdParams2::default());
            let consts = cf.program.consts.clone();

            // Deterministic per-(fixture,layer) seed — FIXED, no time source.
            let layer_seed: u64 = 0x9E37_79B9_7F4A_7C15
                ^ ((name.len() as u64) << 40)
                ^ ((li as u64) << 8);

            for (ii, ins) in cf.program.instrs.iter().enumerate() {
                let Header::Macro { routine, .. } = ins.header else { continue };

                // `no_caches` + inits/teardowns fixtures are added ONLY for the
                // product routines; skip their other (lincomb-pair) instrs here.
                if products_only && !is_product_routine(routine) {
                    continue;
                }

                // Per-instruction deterministic draw (distinct + reproducible).
                // `staged_banks` also returns the gather-descriptor array sized to
                // the instruction's Indirect lanes (each a cached-value gather).
                let mut rng = StdRng::seed_from_u64(layer_seed ^ ((ii as u64) << 1));
                let (mut src, descs) = staged_banks(ins, &consts, &mut rng);
                ensure_dst_cols(ins, &mut src);

                // ids 14/15/20 are never emitted (corpus); skip defensively.
                let Some(expect) = ref_outputs(ins, &src, &descs) else { continue };

                // Run the REAL instruction in a one-instruction program over the
                // staged banks + descriptors (the Indirect lanes resolve via the
                // staged gather, identically in `execute2` and the reference).
                let got = execute2(
                    &Program2 {
                        instrs: vec![ins.clone()],
                        consts: consts.clone(),
                        n_slot_cells: 0,
                        n_matrix_slots: src.matrix.len() as u8,
                    },
                    &descs,
                    &src,
                );
                let got_vals: Vec<Ext> = got.materialized.iter().map(|(_, v)| *v).collect();
                assert_eq!(
                    got_vals, expect,
                    "{name} L{li} i{ii}: routine id {routine} value mismatch"
                );
                // num/den routines must produce DISTINCT outputs for random inputs
                // (a broadcast bug would collapse them).
                if got_vals.len() == 2 {
                    assert_ne!(
                        got_vals[0], got_vals[1],
                        "{name} L{li} i{ii}: num == den (multi-output footer collapsed?)"
                    );
                }
                *counts.entry(routine).or_default() += 1;
            }
        }
    }

    // Non-vacuity: every R3-implemented routine the corpus emits must be covered.
    for id in [1u8, 2, 3, 4, 5, 6, 7, 8, 9, 14, 15, 16, 17, 18, 19, 20] {
        assert!(
            counts.get(&id).copied().unwrap_or(0) > 0,
            "real-instr oracle never exercised routine id {id} (probe STEP 0 says it is emitted)"
        );
    }
}

/// Grow `src.matrix` so every Materialize dst column of `ins` is in range (a
/// store reads `src.matrix[slot].field_ext`, and the column index must be a
/// valid slot — though Materialize records rather than writes the column).
fn ensure_dst_cols(ins: &Instr2, src: &mut SourceBanks) {
    for d in &ins.dsts {
        if let Dst::Materialize { slot, col } = d {
            let s = *slot as usize;
            if src.matrix.len() <= s {
                src.matrix.resize(
                    s + 1,
                    MatrixSlotData { field_ext: true, columns: Vec::new() },
                );
            }
            let need = *col as usize + 1;
            if src.matrix[s].columns.len() < need {
                src.matrix[s].columns.resize(need, Ext::ZERO);
            }
            src.matrix[s].field_ext = true;
        }
    }
}

// ===========================================================================
// Task 3.4 — store-width relation oracle (R7 / re-review-4).
//
// The interpreter enforces the §7 store-width relation in its footer: a base-
// field commit must carry zero ext high limbs (write_cells / assert_store_width,
// ported from v1 interp.rs:55). These tests drive it through the PUBLIC
// `execute2`: (a) a base value lifts cleanly to either width; (b) an ext value
// with a non-zero high limb is rejected on a base-width store; (c) an ext value
// round-trips at full e4 width through a Slot read regardless of dst field.
// (The relation is a debug_assert, matching v1 — these run under the default
// debug `cargo test` profile.)
// ===========================================================================

/// Single instruction: Sum over one Affine source (slot 0, col 0) into `dst`.
/// Sum of one operand IS that operand, so `execute2` stores the source verbatim,
/// isolating the footer store-width check.
fn copy_program(dst: Dst) -> Program2 {
    Program2 {
        instrs: vec![Instr2 {
            header: Header::Arith { op: ArithOp::Sum, arity: 1 },
            operands: vec![Operand::Affine { slot: 0, col: 0 }],
            dsts: vec![dst],
            memtup: None,
            memtup2: None,
        }],
        consts: vec![],
        n_slot_cells: 4,
        n_matrix_slots: 2,
    }
}

/// Slot 0 ext-field (source col 0 = `col0`, col 1 spare output); slot 1
/// base-field (a base-width Materialize destination).
fn store_width_banks(col0: Ext) -> SourceBanks {
    SourceBanks {
        matrix: vec![
            MatrixSlotData { field_ext: true, columns: vec![col0, Ext::ZERO] },
            MatrixSlotData { field_ext: false, columns: vec![Ext::ZERO] },
        ],
        consts: vec![],
        const_challenge: vec![],
        arg_challenge: vec![],
        gamma: Ext::ZERO,
        perm_challenges: vec![],
        perm_additive: Ext::ZERO,
        gather_tables: GatherTables::default(),
        gid: 0,
    }
}

#[test]
fn base_to_ext_lift_passes() {
    // (a) A base-domain value (canonical: high limbs zero) is legal at BOTH
    // widths — the relation permits the base->ext lift and the base->base store;
    // it only forbids dropping NON-zero high limbs.
    let base_val = lift(bf(7)); // coeffs [7, 0, 0, 0]

    // base-width Materialize into base-field slot 1: passes (high limbs zero).
    let got_base = execute2(
        &copy_program(Dst::Materialize { slot: 1, col: 0 }),
        &[],
        &store_width_banks(base_val),
    );
    assert_eq!(got_base.materialized, vec![((1, 0), base_val)]);

    // ext-width Materialize into ext slot 0 (col 1): the lift; value stays canonical.
    let got_ext = execute2(
        &copy_program(Dst::Materialize { slot: 0, col: 1 }),
        &[],
        &store_width_banks(base_val),
    );
    assert_eq!(got_ext.materialized, vec![((0, 1), base_val)]);
    let coeffs = <Ext as FieldExtension<Bf>>::into_coeffs(got_ext.materialized[0].1);
    assert!(
        coeffs[1].is_zero() && coeffs[2].is_zero() && coeffs[3].is_zero(),
        "lifted base value must carry canonical zero high limbs"
    );
}

#[test]
#[should_panic(expected = "non-base")]
fn ext_to_base_truncation_fails() {
    // (b) An ext value with a non-zero high limb stored to a base-width dst must
    // be REJECTED (the zero-high-limb relation), never silently truncated.
    let ext_val = <Ext as FieldExtension<Bf>>::from_coeffs([bf(1), bf(2), bf(0), bf(0)]);
    let _ = execute2(
        &copy_program(Dst::Materialize { slot: 1, col: 0 }),
        &[],
        &store_width_banks(ext_val),
    );
}

#[test]
fn slot_read_is_full_e4_width_regardless_of_store() {
    // (c) Reads use the full e4 width: an ext value stashed in an ext Slot
    // round-trips all four limbs (no dst-field-driven truncation on the read
    // path). Stash to Slot{e4:true}, then copy that Slot to an ext Materialize.
    let ext_val = <Ext as FieldExtension<Bf>>::from_coeffs([bf(3), bf(5), bf(7), bf(9)]);
    let p = Program2 {
        instrs: vec![
            Instr2 {
                header: Header::Arith { op: ArithOp::Sum, arity: 1 },
                operands: vec![Operand::Affine { slot: 0, col: 0 }],
                dsts: vec![Dst::Slot { e4: true, cell: 0 }],
                memtup: None,
                memtup2: None,
            },
            Instr2 {
                header: Header::Arith { op: ArithOp::Sum, arity: 1 },
                operands: vec![Operand::Slot { e4: true, cell: 0 }],
                dsts: vec![Dst::Materialize { slot: 0, col: 1 }],
                memtup: None,
                memtup2: None,
            },
        ],
        consts: vec![],
        n_slot_cells: 4,
        n_matrix_slots: 2,
    };
    let got = execute2(&p, &[], &store_width_banks(ext_val));
    assert_eq!(
        got.materialized,
        vec![((0, 1), ext_val)],
        "all four e4 limbs must round-trip through the Slot read"
    );
}

// ===========================================================================
// Task 3.5 — CHALLENGE-BANK ORACLE (spec §5, the "43 KB elimination" win).
//
// The v2 ISA DEFERS the α^k·c fold. v1 baked the host-folded coefficient
// `α^k·c` into an opaque payload; v2 instead carries the RAW const `c` on an
// `Ldc{Const}` lane and reads `α^k` from the COLUMN-INDEXED `ConstChallenge`
// bank, multiplying IN-KERNEL. The two banks are distinct transfer channels
// (`challenges::bank_for_family`): α/γ → `ConstChallenge` (device __constant__),
// perm/additive → `ArgChallenge` (kernel-arg). These tests prove the deferred
// fold is FAITHFUL: (a) each family routes to the channel the model declares;
// the swap test proves the interpreter reads the RIGHT bank (a single synthetic
// challenge set would mask a wrong-bank read); the fold-parity test proves the
// in-kernel `α^k · c` reproduces v1's host-folded coefficient bit-for-bit.
// ===========================================================================

use gkr_eval_isa::compiler_v2::challenges::{
    alpha_power_bank_index, bank_for_family, AlphaSlot, ChallengeFamily,
};

/// A `SourceBanks` carrying explicit `const_challenge` (α/γ channel) and
/// `arg_challenge` (perm/additive channel) banks, plus one ext matrix slot for
/// the operand columns. Everything else is neutral.
fn dual_bank_src(
    cols: Vec<Ext>,
    const_challenge: Vec<Ext>,
    arg_challenge: Vec<Ext>,
) -> SourceBanks {
    SourceBanks {
        matrix: vec![ext_slot(&cols)],
        consts: vec![],
        const_challenge,
        arg_challenge,
        gamma: Ext::ZERO,
        perm_challenges: vec![],
        perm_additive: Ext::ZERO,
        gather_tables: GatherTables::default(),
        gid: 0,
    }
}

#[test]
fn challenge_bank_swap_is_detected() {
    // --- sub-check (a): each FAMILY routes to the channel the model declares ---
    // α/γ ride the device __constant__ ConstChallenge bank; perm/additive ride
    // the kernel-arg ArgChallenge bank (spec §5). This is the routing the swap
    // test relies on (which physical bank each in-kernel read indexes).
    assert_eq!(bank_for_family(ChallengeFamily::Alpha), LdcSub::ConstChallenge);
    assert_eq!(bank_for_family(ChallengeFamily::Gamma), LdcSub::ConstChallenge);
    assert_eq!(
        bank_for_family(ChallengeFamily::PermLinearization),
        LdcSub::ArgChallenge
    );
    assert_eq!(
        bank_for_family(ChallengeFamily::AdditiveSeed),
        LdcSub::ArgChallenge
    );

    // --- the swap: a routine reading BOTH banks must change if they swap ---
    // Two instructions, each reading a DIFFERENT channel:
    //   instr 0: GateOutputFold over [col0, col1] reads α^1 from const_challenge[1]
    //            (the ConstChallenge / α-power bank).            out0 = col0 + α^1·col1
    //   instr 1: Sum over an Ldc{ArgChallenge, idx 1} lane reads arg_challenge[1]
    //            (the ArgChallenge / perm-additive bank).        out1 = arg_challenge[1]
    // FILL THE TWO BANKS WITH DISTINCT VALUES so a wrong-bank read (or a swap) is
    // observable: a single synthetic set shared across both banks would make a
    // const↔arg swap a no-op and hide the channel routing.
    let col0 = lift(bf(3));
    let col1 = lift(bf(5));

    // const_challenge[1] = α^1 = 7 ; arg_challenge[1] = 9 (DISTINCT, and distinct
    // from the column values so the output algebra cannot coincidentally match).
    let alpha1 = lift(bf(7));
    let arg1 = lift(bf(9));
    let const_bank = vec![Ext::ZERO, alpha1]; // entry 0 unused (α^0 free lift)
    let arg_bank = vec![Ext::ZERO, arg1]; // entry 0 unused here

    // The two-instruction program. GateOutputFold materializes to col 2; the
    // arg-bank Sum materializes to col 3.
    let prog = Program2 {
        instrs: vec![
            Instr2 {
                header: Header::Macro {
                    routine: RoutineId::GateOutputFold as u8,
                    n_operands: 2,
                },
                operands: vec![
                    Operand::Affine { slot: 0, col: 0 },
                    Operand::Affine { slot: 0, col: 1 },
                ],
                dsts: vec![Dst::Materialize { slot: 0, col: 2 }],
                memtup: None,
                memtup2: None,
            },
            Instr2 {
                header: Header::Arith { op: ArithOp::Sum, arity: 1 },
                operands: vec![Operand::Ldc { sub: LdcSub::ArgChallenge, idx: 1 }],
                dsts: vec![Dst::Materialize { slot: 0, col: 3 }],
                memtup: None,
                memtup2: None,
            },
        ],
        consts: vec![],
        n_slot_cells: 0,
        n_matrix_slots: 1,
    };

    // Slot 0 columns: the two source cols + two output placeholders.
    let cols = vec![col0, col1, Ext::ZERO, Ext::ZERO];

    // Baseline: banks filled as declared.
    let base = execute2(&prog, &[], &dual_bank_src(cols.clone(), const_bank.clone(), arg_bank.clone()));
    let base_vals: Vec<Ext> = base.materialized.iter().map(|(_, v)| *v).collect();

    // Hand reference confirms each output reads its OWN bank:
    //   out0 = col0 + α^1·col1 = 3 + 7·5 = 38   (ConstChallenge bank)
    //   out1 = arg_challenge[1] = 9             (ArgChallenge bank)
    let mut expect0 = col0;
    let mut a1c1 = alpha1;
    a1c1.mul_assign(&col1);
    expect0.add_assign(&a1c1);
    assert_eq!(base_vals, vec![expect0, arg1], "baseline must read each value from its OWN bank");

    // Swap the two banks' CONTENTS and rerun. Now const_challenge holds the arg
    // values and vice-versa; a faithful interpreter reads through the SAME
    // channel as before, so BOTH outputs must change.
    let swapped = execute2(
        &prog,
        &[],
        // const_challenge <- arg_bank, arg_challenge <- const_bank.
        &dual_bank_src(cols.clone(), arg_bank.clone(), const_bank.clone()),
    );
    let swapped_vals: Vec<Ext> = swapped.materialized.iter().map(|(_, v)| *v).collect();

    // Distinct fills make the swap observable on BOTH outputs.
    assert_ne!(
        base_vals, swapped_vals,
        "swapping the bank contents must change the result — a wrong-bank read is otherwise masked"
    );
    assert_ne!(
        base_vals[0], swapped_vals[0],
        "GateOutputFold α^1 read must come from the ConstChallenge bank (changed on swap)"
    );
    assert_ne!(
        base_vals[1], swapped_vals[1],
        "Ldc{{ArgChallenge}} read must come from the ArgChallenge bank (changed on swap)"
    );
    // And the swapped values are exactly the cross-read references:
    //   out0' = col0 + arg1·col1 = 3 + 9·5 = 48 ; out1' = const1 = α^1 = 7.
    let mut expect0_swapped = col0;
    let mut a1c1_swapped = arg1;
    a1c1_swapped.mul_assign(&col1);
    expect0_swapped.add_assign(&a1c1_swapped);
    assert_eq!(
        swapped_vals,
        vec![expect0_swapped, alpha1],
        "after swap each channel reads the OTHER bank's contents"
    );
}

#[test]
fn in_kernel_fold_matches_v1_host_folded_coeff() {
    // The deferred-fold identity. v1 BAKED `α^k · c` into a payload (the host
    // folded the coefficient). v2 carries the RAW `c` on an `Ldc{Const}` lane (or
    // a column value) and reads `α^k` from the column-indexed ConstChallenge bank
    // (`alpha_power_bank_index`), multiplying IN-KERNEL. Prove the v2 in-kernel
    // fold reproduces the v1 host-folded coefficient bit-for-bit across ≥2 column
    // indices — INCLUDING k=0 (the free α^0=1 lift) and some k≥1 (a real bank read).
    //
    // We do NOT need v1 production code: the "host-folded coeff" is `α^k·lift(c)`
    // computed directly here, and the "v2 in-kernel fold" is a GateOutputFold
    // instruction (`acc = Σ_k α^k·col_k`) reading raw `c` from a column lane and
    // `α^k` from `const_challenge[k]`.

    // Concrete α, and a raw const c PER COLUMN (distinct so a wrong α-power index
    // surfaces as a mismatch). α = 2 (lifted): α^0=1, α^1=2, α^2=4, α^3=8.
    let alpha = lift(bf(2));
    let mut alpha_powers = vec![Ext::ONE]; // alpha_powers[k] = α^k
    for _ in 1..4 {
        let mut next = *alpha_powers.last().unwrap();
        next.mul_assign(&alpha);
        alpha_powers.push(next);
    }
    // const_challenge[k] = α^k for k >= 1; entry 0 is unused (α^0 is a free lift).
    let const_challenge = vec![Ext::ZERO, alpha_powers[1], alpha_powers[2], alpha_powers[3]];

    // Raw consts c_k riding the GateOutputFold column lanes (k = 0..=3). Distinct
    // values; none equal to a power of α so a coincidental match is implausible.
    let raw_c: Vec<u32> = vec![11, 13, 17, 19];
    let cols: Vec<Ext> = raw_c.iter().map(|&c| lift(bf(c))).collect();

    // α-power indexing CONFIRMED against `alpha_power_bank_index`: col 0 is the
    // OneLift (free α^0=1), col k>=1 reads bank entry k.
    assert_eq!(alpha_power_bank_index(0), AlphaSlot::OneLift);
    for k in 1u16..raw_c.len() as u16 {
        assert_eq!(alpha_power_bank_index(k), AlphaSlot::Power(k));
    }

    // For each column index k, run a SINGLE-LANE GateOutputFold that contributes
    // only that one term, so the materialized output is exactly the in-kernel
    // fold of column k. To isolate term k we place c_k at column 0 of a fold when
    // k==0 (free lift), and for k>=1 we run a 2-lane fold [dummy_zero, c_k] so the
    // k=1 bank entry α^1 multiplies c_k — but the bank index is POSITIONAL (the
    // operand position is the α-power index), so to test α^k we must place c_k at
    // operand position k. We therefore build a (k+1)-lane fold whose lanes 0..k-1
    // are zero and lane k carries c_k: out = α^k·c_k (all other terms vanish).
    for k in 0..raw_c.len() {
        // (k+1) operand lanes: zeros for positions 0..k, c_k at position k.
        // Columns: col j (j < k) = 0, col k = c_k, then one output placeholder.
        let mut fold_cols: Vec<Ext> = vec![Ext::ZERO; k];
        fold_cols.push(cols[k]); // position k carries the raw const
        let out_col = (k + 1) as u16;
        fold_cols.push(Ext::ZERO); // output placeholder

        let operands: Vec<Operand> =
            (0..=k).map(|j| Operand::Affine { slot: 0, col: j as u16 }).collect();
        let prog = Program2 {
            instrs: vec![Instr2 {
                header: Header::Macro {
                    routine: RoutineId::GateOutputFold as u8,
                    n_operands: (k + 1) as u8,
                },
                operands,
                dsts: vec![Dst::Materialize { slot: 0, col: out_col }],
                memtup: None,
                memtup2: None,
            }],
            consts: vec![],
            n_slot_cells: 0,
            n_matrix_slots: 1,
        };
        let src = dual_bank_src(fold_cols, const_challenge.clone(), vec![]);
        let got = execute2(&prog, &[], &src);
        let in_kernel = got.materialized[0].1;

        // v1 host-folded reference: α^k · lift(c_k), computed DIRECTLY here.
        let mut host_folded = alpha_powers[k];
        host_folded.mul_assign(&lift(bf(raw_c[k])));

        assert_eq!(
            in_kernel, host_folded,
            "k={k}: v2 in-kernel α^{k}·c MUST equal the v1 host-folded coeff α^{k}·{}",
            raw_c[k]
        );
    }

    // Explicit witnesses at the two ends: k=0 is the FREE lift (α^0=1, so the
    // fold output is just lift(c_0)); k=3 is a real bank read (α^3·c_3).
    // k=0 (free lift): fold of a single lane [c_0] -> lift(c_0).
    let p0 = Program2 {
        instrs: vec![Instr2 {
            header: Header::Macro { routine: RoutineId::GateOutputFold as u8, n_operands: 1 },
            operands: vec![Operand::Affine { slot: 0, col: 0 }],
            dsts: vec![Dst::Materialize { slot: 0, col: 1 }],
            memtup: None,
            memtup2: None,
        }],
        consts: vec![],
        n_slot_cells: 0,
        n_matrix_slots: 1,
    };
    let got0 = execute2(
        &p0,
        &[],
        &dual_bank_src(vec![cols[0], Ext::ZERO], const_challenge.clone(), vec![]),
    );
    assert_eq!(got0.materialized[0].1, lift(bf(raw_c[0])), "k=0 free lift = lift(c_0)");
}
