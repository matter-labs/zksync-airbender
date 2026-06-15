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
// SCOPE (STEP-0 probe + the `exec_macro` doc): the three fixtures emit routine
// ids {1,2,3,4,5,6,7,8} (probe: every layer). Of these, only `GrandProductStep`
// (2) and `AggregateLookupPair` (3) have a per-row formula that the v2 `Instr2`
// determines UNAMBIGUOUSLY — one product / one rational-pair-combine, no lost
// coefficients or const-folding. The other emitted routines (1,4,5,6,7,8) fan a
// single v2 routine id out to several production primitive kinds (`PK_*`,
// `bench_interp/lower.rs:173-187`) whose math differs but which the lowered
// instruction cannot tell apart (see the `exec_macro` doc for the exact gap and
// .cuh/.rs anchors). They are intentionally `todo!`, so this oracle CANNOT run a
// whole fixture program end-to-end (it would hit a `todo!`); it instead drives
// `execute2` per pinnable instruction with fixture-shaped, `eval_ref`-style
// random operand values + a fixed seed.
//
// The routine ARITHMETIC depends only on the operand VALUES, not on the operand
// lane KIND (Affine/Indirect/Ldc all funnel through one `read` closure), so
// feeding controlled values through `Affine` lanes faithfully exercises the
// routine fold AND the multi-output footer wiring (num,den → two dsts).
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

/// HAND reference for `GrandProductStep` (id 2). DIFFERENT decomposition: the
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
                    // id 2 — GrandProductStep: a·b. Two ext operands, 1 output.
                    x if x == RoutineId::GrandProductStep as u8 => {
                        assert_eq!(n_operands, 2, "{name} L{li}: GrandProductStep arity != 2");
                        assert_eq!(ins.dsts.len(), 1, "{name} L{li}: GrandProductStep 1 dst");
                        let a = rand_ext(&mut rng, true);
                        let b = rand_ext(&mut rng, true);
                        let got = run_macro(RoutineId::GrandProductStep, &[a, b], 1);
                        assert_eq!(got.len(), 1);
                        assert_eq!(
                            got[0],
                            ref_grand_product(a, b),
                            "{name} L{li}: GrandProductStep value mismatch"
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
                    // Emitted-but-unpinned routines: record the id (so the gap is
                    // documented + non-vacuous), do not execute (would `todo!`).
                    other => {
                        emitted_unpinned.insert(other);
                    }
                }
            }
        }
    }

    // Non-vacuity: both pinnable routines must actually appear in the corpus.
    assert!(
        total_grand_product > 0,
        "no GrandProductStep instrs across the target fixtures (oracle vacuous)"
    );
    assert!(
        total_aggregate > 0,
        "no AggregateLookupPair instrs across the target fixtures (oracle vacuous)"
    );

    // Document the gap explicitly: the corpus DOES emit the routines we leave
    // `todo!`, so the partial is deliberate, not an accident of fixture choice.
    // (Probe STEP 0 found ids {1,4,5,6,7,8} alongside the two pinned ones.)
    for expected in [
        RoutineId::LookupNumDen as u8,
        RoutineId::SingleColumnLookup as u8,
        RoutineId::MemoryTuple as u8,
        RoutineId::VectorizedLookup as u8,
        RoutineId::VectorizedLookupSetup as u8,
        RoutineId::ProductStep as u8,
    ] {
        assert!(
            emitted_unpinned.contains(&expected),
            "expected the corpus to emit unpinned routine id {expected} (probe STEP 0)"
        );
    }
}
