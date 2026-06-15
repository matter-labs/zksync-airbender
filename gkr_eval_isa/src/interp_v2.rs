//! ISA-v2 CPU reference interpreter (Phase 3, Task 3.1). Executes the fused
//! `Program2` lane stream — the v2 analogue of `interp.rs`'s `execute`. Mirrors
//! v1: per-instruction read-operands → accumulate-by-header → write-footer.
//!
//! This task (3.1) lands the execution framework + the three smoke-test
//! routines (Sum, Dot, GateOutputFold). The remaining macro routines are marked
//! `todo!("Task 3.3")` so the smoke path never panics; gather decoder /
//! row-indexed variants are implemented correct-by-spec (§4) even though only
//! the mapped variants are exercised here.
//!
//! Domain model (spec §5): there is NO `e4_result` bit — store width is a
//! relation enforced at the footer. A base-field store of an Ext value asserts
//! the high limbs are zero (the v1 `write_cells` store-width safety assert,
//! carried here as the Task 3.4 store-width relation seed).

use crate::compiler_v2::gather::{DecoderSpec, GatherDescriptor};
use crate::eval_ref::{lift, Bf, Ext};
use crate::isa_v2::{
    ArithOp, Dst, Header, IndirectKind, LdcSub, Operand, Program2, RoutineId, MT_CONST_ADDR_LOW,
    MT_CONST_ADDR_LOW_DYN_COEFF, MT_CONST_ADDR_LOW_OFFSET, MT_CONST_TS_LOW_OFFSET, SPECIAL_NEG_ONE,
    SPECIAL_ONE, SPECIAL_ZERO,
};

/// Memory-tuple TERM-slot index for the special-indirect dynamic-offset column
/// (`MEMORY_TUPLE_VALUE_HIGH_EXTRA_TERM`, forward/kernels/mod.rs:39). Defined
/// locally so this CPU interpreter does not depend on the GPU crate or widen the
/// private const in `compiler_v2::macros`; the value (7) is the same wire slot.
const MEMORY_TUPLE_VALUE_HIGH_EXTRA_TERM: u8 = 7;
use field::{Field, FieldExtension, PrimeField};

// ---------------------------------------------------------------------------
// Cell helpers — COPIED verbatim from interp.rs (they are private there; per the
// task constraints we copy rather than widen v1 visibility). `read_cells` /
// `write_cells` keep the bf-granular slot model and the store-width assert.
// ---------------------------------------------------------------------------

fn read_cells(cells: &[Bf], cell: u16, e4: bool) -> Ext {
    let c = cell as usize;
    if e4 {
        <Ext as FieldExtension<Bf>>::from_coeffs([
            cells[c],
            cells[c + 1],
            cells[c + 2],
            cells[c + 3],
        ])
    } else {
        lift(cells[c])
    }
}

fn write_cells(cells: &mut [Bf], cell: u16, e4: bool, v: Ext) {
    let c = cell as usize;
    let coeffs = <Ext as FieldExtension<Bf>>::into_coeffs(v);
    if e4 {
        cells[c..c + 4].copy_from_slice(&coeffs);
    } else {
        debug_assert!(
            coeffs[1].is_zero() && coeffs[2].is_zero() && coeffs[3].is_zero(),
            "bf-result instruction produced a non-base value — compiler domain bug"
        );
        cells[c] = coeffs[0];
    }
}

/// The store-width relation (Task 3.4 seed) for a `Materialize` footer into a
/// base-field matrix slot: the Ext value must carry zero high limbs. Mirrors
/// the `write_cells` base-store assert so a base-field commit is rejected the
/// same way regardless of destination kind.
fn assert_store_width(field_ext: bool, v: Ext) {
    if !field_ext {
        let coeffs = <Ext as FieldExtension<Bf>>::into_coeffs(v);
        debug_assert!(
            coeffs[1].is_zero() && coeffs[2].is_zero() && coeffs[3].is_zero(),
            "base-field materialize produced a non-base value — compiler domain bug"
        );
    }
}

// ---------------------------------------------------------------------------
// Source banks + result (spec §5 transfer channels).
// ---------------------------------------------------------------------------

/// One matrix-slot backing: a column vector of post-fold values plus its
/// logical field. The interpreter reads `Affine { slot, col }` from here and
/// takes the store FIELD for a `Materialize { slot, .. }` from `field_ext`.
#[derive(Clone, Debug, PartialEq)]
pub struct MatrixSlotData {
    pub field_ext: bool,
    pub columns: Vec<Ext>,
}

/// The off-instruction gather tables (spec §4). Indexed by descriptor index:
/// `n[desc]` is the value table, `mapping[desc]` the per-row index table, and
/// `n_len[desc]` the optional length guard for the row-indexed setup variant.
///
/// `decoder_mask` / `alpha_powers` back the decoder predicate (spec finding 1):
/// the interpreter resolves the DecoderMappedE4 path itself rather than being
/// handed a pre-resolved value, so it needs the per-row mask AND the α-power
/// bank to RECOMPUTE the fill scalar from `DecoderSpec`. They mirror the CUDA
/// `descriptor.decoder_mask` per-row load (`lookup_helpers.cuh:62`) and the
/// `ab_gkr_lookup_alpha_powers` __constant__ bank used to fold the fill
/// (`gkr_forward_setup_generic_lookup:410`).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GatherTables {
    /// Value table per descriptor (`n` / `virtual_setup`).
    pub n: Vec<Vec<Ext>>,
    /// Per-row index table per descriptor (`mapping`).
    pub mapping: Vec<Vec<u32>>,
    /// Length guard per descriptor (RowIndexedSetupE4 zero-pads beyond this).
    pub n_len: Vec<Option<usize>>,
    /// Per-row decoder predicate mask per descriptor (`Some` only for
    /// DecoderMappedE4; `None` otherwise). A row whose mask is base-zero is
    /// masked out and resolves to the fill scalar instead of the mapped value
    /// (mirrors the CUDA `enabled.limb == 0` branch, `lookup_helpers.cuh:63`).
    pub decoder_mask: Vec<Option<Vec<Bf>>>,
    /// The `ab_gkr_lookup_alpha_powers` bank (`alpha_powers[k] == α^k`). The
    /// decoder fill scalar is `α^fill_alpha_power · table_id`, recomputed here
    /// from `DecoderSpec` so the interpreter — not its caller — resolves it.
    pub alpha_powers: Vec<Ext>,
}

/// Everything `execute2` reads that is not in the program: matrix backings, the
/// const banks (bf consts + the two challenge channels), the gather tables, and
/// the current row id (`gid`) that indexes per-row gather mappings.
///
/// R3 additions (documented): the lookup-family routines need the LOOKUP
/// ADDITIVE CHALLENGE γ (the `sh(x) = x + γ` shift, `bench_interp/tests.rs`
/// `mirror_gate`), and the memory-tuple routine needs `perm_additive` + the
/// six per-ROLE permutation challenges. Both are challenge BANKS (spec §5), not
/// operand lanes:
///   - `gamma` is added as its own field rather than being decoded out of the
///     `[γ,γ²,2γ]` ConstChallenge layout, so the interpreter reads it directly
///     (the spec keeps γ on the ConstChallenge channel; this field is the
///     resolved scalar the routines actually fold).
///   - `perm_challenges` is the ArgChallenge bank read BY ROLE: index `k` is the
///     challenge for permutation role `k` (`R_PERM_ADDR_LOW=0 .. R_PERM_VAL_HIGH=5`,
///     matching `bench_interp/tests.rs::indep_mem_tuple`'s `perm_challenges[role]`).
///     `perm_additive` is the additive seed (`ch.perm_additive`).
///   - `arg_challenge` stays the raw ArgChallenge bank for `Ldc{ArgChallenge}`
///     operand reads (none in the corpus, kept for completeness).
#[derive(Clone, Debug)]
pub struct SourceBanks {
    pub matrix: Vec<MatrixSlotData>,
    /// bf constant table (`LdcSub::Const`), raw u32 coeffs.
    pub consts: Vec<u32>,
    /// device `__constant__` α/γ bank (`LdcSub::ConstChallenge`). For the
    /// GateOutputFold α-power read, entry `k` holds α^k (k > 0; α^0 is a free
    /// lift, never a bank read — see `challenges::alpha_power_bank_index`).
    pub const_challenge: Vec<Ext>,
    /// kernel-arg perm/additive bank (`LdcSub::ArgChallenge`).
    pub arg_challenge: Vec<Ext>,
    /// R3: the lookup additive challenge γ (`sh(x) = x + γ`). A resolved scalar
    /// on the ConstChallenge channel (spec §5), surfaced as its own field so the
    /// lookup routines fold it directly.
    pub gamma: Ext,
    /// R3: the per-ROLE permutation challenges (the ArgChallenge bank, read by
    /// role). Index `k` = role `k` (`R_PERM_*` below). Used by the memory-tuple
    /// routine to fold `Σ_role chal[role]·term` (matches `indep_mem_tuple`).
    pub perm_challenges: Vec<Ext>,
    /// R3: the additive seed challenge (`perm_additive`) the memory-tuple value
    /// is built on top of.
    pub perm_additive: Ext,
    pub gather_tables: GatherTables,
    /// Current row index (the gather mapping `gid`).
    pub gid: usize,
}

// Permutation challenge ROLE indices into `SourceBanks::perm_challenges`
// (cs/src/definitions/constants.rs role convention, mirrored by
// `bench_interp/tests.rs::indep_mem_tuple`'s `R_ADDR_LOW..R_VAL_HIGH`). The
// memory-tuple value folds each linear term by the challenge for its role.
const R_PERM_ADDR_LOW: usize = 0;
const R_PERM_ADDR_HIGH: usize = 1;
const R_PERM_TS_LOW: usize = 2;
const R_PERM_TS_HIGH: usize = 3;
const R_PERM_VAL_LOW: usize = 4;
const R_PERM_VAL_HIGH: usize = 5;

/// Map a memory-tuple TERM-slot index (0..=7, `MEMORY_TUPLE_*_TERM` from
/// `compiler_v2::macros`) to its permutation-challenge ROLE index. The GPU
/// folds `Σ_term linear_challenges[term]·linear_inputs[term]`; on the CPU side
/// the term→role correspondence mirrors `indep_mem_tuple`:
///   addr lo/hi → R_PERM_ADDR_{LOW,HIGH}; ts lo/hi → R_PERM_TS_{LOW,HIGH};
///   value lo/hi → R_PERM_VAL_{LOW,HIGH}.
/// Term 5 (VALUE_LOW_EXTRA, U8Limbs only) and term 7 (the special-indirect
/// dyn-offset column) are handled specially by the caller and never reach here.
fn perm_role_for_memtup_term(term: u8) -> usize {
    match term {
        0 => R_PERM_ADDR_LOW,  // MEMORY_TUPLE_ADDRESS_LOW_TERM
        1 => R_PERM_ADDR_HIGH, // MEMORY_TUPLE_ADDRESS_HIGH_TERM
        2 => R_PERM_TS_LOW,    // MEMORY_TUPLE_TIMESTAMP_LOW_TERM
        3 => R_PERM_TS_HIGH,   // MEMORY_TUPLE_TIMESTAMP_HIGH_TERM
        4 => R_PERM_VAL_LOW,   // MEMORY_TUPLE_VALUE_LOW_TERM
        6 => R_PERM_VAL_HIGH,  // MEMORY_TUPLE_VALUE_HIGH_TERM
        other => panic!(
            "memory-tuple term slot {other} has no direct perm role (term 5/7 are special-cased)"
        ),
    }
}

/// Output of one `execute2` run. `materialized` is the committed-store trace
/// (Materialize footers) in program order; `final_cells` is the slot cell file
/// snapshot for cross-implementation parity (mirrors v1 `ExecResult`).
#[derive(Clone, Debug, PartialEq)]
pub struct ExecResult2 {
    pub materialized: Vec<((u8, u16), Ext)>,
    pub final_cells: Vec<Bf>,
}

// ---------------------------------------------------------------------------
// Gather resolution (spec §4).
// ---------------------------------------------------------------------------

/// Resolve one `Indirect` operand to its gathered value (spec §4). Dispatches on
/// the descriptor's `kind` over the four variants. `desc_idx` indexes the
/// off-instruction `GatherTables`; `gid` is the current row.
///
/// - `MappedVirtualBf` / `MappedGenericE4`: a per-row mapping selects the table
///   row — `n[desc_idx][ mapping[desc_idx][gid] ]`. The mapping is row-varying;
///   we read it through `gid` rather than constant-folding so off-by-one/stride
///   bugs surface (the smoke test exercises both mapped arms).
/// - `DecoderMappedE4`: same mapped read, plus the decoder predicate + fill
///   (`d.decoder`). A per-row base-field mask `decoder_mask[desc_idx][gid]`
///   selects the branch: a non-zero mask keeps the mapped value; a base-zero
///   mask is masked out and substitutes the fill scalar
///   `α^fill_alpha_power · table_id` (recomputed here from `DecoderSpec` + the
///   `alpha_powers` bank — the interpreter resolves it, not its caller). This
///   mirrors `lookup_helpers.cuh:58-69` (the `enabled.limb == 0` branch) and
///   the fill fold in `gkr_forward_setup_generic_lookup:409-413`. The IR carries
///   only `lookup_set_index == DECODER_LOOKUP_FORMAL_SET_INDEX`; the fill
///   α-power / table id come off `DecoderSpec`.
/// - `RowIndexedSetupE4`: no mapping — read `n[desc_idx][gid]`, zero-padded
///   beyond `n_len[desc_idx]` (LOOKUP_SETUP length guard).
pub fn resolve_gather(
    d: &GatherDescriptor,
    gid: usize,
    t: &GatherTables,
    desc_idx: usize,
) -> Ext {
    match d.kind {
        IndirectKind::MappedVirtualBf | IndirectKind::MappedGenericE4 => {
            let row = t.mapping[desc_idx][gid] as usize;
            t.n[desc_idx][row]
        }
        IndirectKind::DecoderMappedE4 => {
            // Decoder lookup (cache_relation.rs:382-419, lookup_helpers.cuh:58-69).
            // First the same mapped read as the plain variant, then the per-row
            // predicate mask. The CUDA path is:
            //   E value = generic_lookup[mapping[gid]];
            //   if (decoder_mask != nullptr) {
            //     bf enabled = decoder_mask[gid];
            //     if (enabled.limb == 0) value = decoder_fill_value[0];
            //   }
            // i.e. a base-zero mask is masked out and substitutes the fill
            // scalar; any non-zero mask keeps the mapped value.
            let row = t.mapping[desc_idx][gid] as usize;
            let mapped = t.n[desc_idx][row];
            match &d.decoder {
                Some(DecoderSpec { fill_alpha_power, table_id }) => {
                    // No mask table => the decoder fill never fires (mirrors the
                    // CUDA `decoder_mask == nullptr` guard): always keep mapped.
                    let enabled = t.decoder_mask[desc_idx]
                        .as_ref()
                        .map(|mask| !mask[gid].is_zero())
                        .unwrap_or(true);
                    if enabled {
                        mapped
                    } else {
                        // Fill scalar = α^fill_alpha_power · table_id, recomputed
                        // here from DecoderSpec + the alpha-power bank — the
                        // single device scalar that
                        // `gkr_forward_setup_generic_lookup:409-413` precomputes:
                        //   E fill = ab_gkr_lookup_alpha_powers[col_count-1]
                        //            * bf(decoder_table_id);
                        // (`fill_alpha_power` is that `col_count-1` index.)
                        let mut fill = t.alpha_powers[*fill_alpha_power as usize];
                        fill.mul_assign(&lift(Bf::from_u32_with_reduction(*table_id)));
                        fill
                    }
                }
                // A DecoderMappedE4 with no DecoderSpec is a malformed descriptor
                // (the decoder fill datum is the one variant-specific field it
                // must carry); fall back to the mapped value.
                None => mapped,
            }
        }
        IndirectKind::RowIndexedSetupE4 => {
            // Row-indexed setup gather (LOOKUP_SETUP): no mapping, indexed
            // directly by the row id, zero-padded beyond the generic-lookup
            // length guard.
            if let Some(len) = t.n_len[desc_idx] {
                if gid >= len {
                    return Ext::ZERO;
                }
            }
            t.n[desc_idx][gid]
        }
    }
}

// ---------------------------------------------------------------------------
// Execution.
// ---------------------------------------------------------------------------

/// Execute a fused `Program2` on one row. Mirrors v1 `execute`: per instruction,
/// resolve operands, accumulate by header (arith op / macro routine), then write
/// the footer dsts. `gathers` is the descriptor array indexed by the `Indirect`
/// operand's `desc` lane.
pub fn execute2(p: &Program2, gathers: &[GatherDescriptor], src: &SourceBanks) -> ExecResult2 {
    let mut cells = vec![Bf::ZERO; p.n_slot_cells as usize];
    let mut materialized: Vec<((u8, u16), Ext)> = Vec::new();

    for ins in &p.instrs {
        let read = |o: &Operand| -> Ext {
            match *o {
                Operand::Affine { slot, col } => {
                    src.matrix[slot as usize].columns[col as usize]
                }
                Operand::Slot { e4, cell } => read_cells(&cells, cell as u16, e4),
                Operand::Ldc { sub, idx } => read_ldc(src, sub, idx),
                Operand::Indirect { e4: _, desc } => resolve_gather(
                    &gathers[desc as usize],
                    src.gid,
                    &src.gather_tables,
                    desc as usize,
                ),
            }
        };

        // Per-dst output values. Arith ops and single-output macros (GateOutputFold,
        // Product) produce ONE value broadcast to every footer dst (in the
        // corpus that is a single dst). Multi-output macros (AggregateLookupPair:
        // num,den) produce one value PER dst, aligned to `ins.dsts` (spec §3 /
        // routine_table output_count). `outputs` is therefore indexed against the
        // footer below.
        let outputs: Vec<Ext> = match ins.header {
            Header::Arith { op, .. } => {
                let a = match op {
                    ArithOp::Sum => {
                        let mut a = Ext::ZERO;
                        for o in &ins.operands {
                            let v = read(o);
                            a.add_assign(&v);
                        }
                        a
                    }
                    ArithOp::Prod => {
                        let mut a = Ext::ONE;
                        for o in &ins.operands {
                            let v = read(o);
                            a.mul_assign(&v);
                        }
                        a
                    }
                    ArithOp::Dot => {
                        // Strength-reduced sum-of-products: arity = number of pairs;
                        // accumulate operands[2k] * operands[2k+1].
                        let mut a = Ext::ZERO;
                        for pair in ins.operands.chunks(2) {
                            let mut x = read(&pair[0]);
                            let y = read(&pair[1]);
                            x.mul_assign(&y);
                            a.add_assign(&x);
                        }
                        a
                    }
                    ArithOp::Fma => {
                        // Fused multiply-add lowering is a Task 3.3 concern (the 3.1
                        // smoke path never emits Fma). Marked, not silently wrong.
                        todo!("Task 3.3: ArithOp::Fma accumulation")
                    }
                };
                vec![a]
            }
            Header::Macro { routine, .. } => exec_macro(routine_from_u8(routine), ins, src, &read),
        };

        // Footer: write each dst its aligned output value. A single-valued result
        // (`outputs.len() == 1`) is broadcast to every dst (matches the arith /
        // single-output-macro contract); a multi-output macro supplies exactly
        // one value per dst (num then den, in dst order — `macro_gate_dsts`).
        debug_assert!(
            outputs.len() == 1 || outputs.len() == ins.dsts.len(),
            "macro output count {} aligns with neither broadcast (1) nor dst count {}",
            outputs.len(),
            ins.dsts.len()
        );
        for (i, dst) in ins.dsts.iter().enumerate() {
            let v = if outputs.len() == 1 { outputs[0] } else { outputs[i] };
            match *dst {
                Dst::Slot { e4, cell } => write_cells(&mut cells, cell as u16, e4, v),
                Dst::Materialize { slot, col } => {
                    let field_ext = src.matrix[slot as usize].field_ext;
                    assert_store_width(field_ext, v);
                    materialized.push(((slot, col), v));
                }
            }
        }
    }

    ExecResult2 { materialized, final_cells: cells }
}

/// Read an `Ldc` operand from the appropriate const bank (spec §5 transfer
/// channels). `Special` resolves 0/1/-1 directly; the three real banks index
/// their respective source vectors.
fn read_ldc(src: &SourceBanks, sub: LdcSub, idx: u16) -> Ext {
    match sub {
        LdcSub::Special => match idx {
            SPECIAL_ZERO => Ext::ZERO,
            SPECIAL_ONE => Ext::ONE,
            SPECIAL_NEG_ONE => {
                let mut v = Ext::ONE;
                v.negate();
                v
            }
            other => panic!("unknown LdcSub::Special index {other}"),
        },
        LdcSub::Const => lift(Bf::from_u32_with_reduction(src.consts[idx as usize])),
        LdcSub::ConstChallenge => src.const_challenge[idx as usize],
        LdcSub::ArgChallenge => src.arg_challenge[idx as usize],
    }
}

/// Dispatch one macro routine, returning one output value PER footer dst (or a
/// single value to broadcast). R3 implements EVERY routine. Each per-row formula
/// is transcribed from `bench_interp/tests.rs` `mirror_gate`/`mirror_cache` (the
/// authoritative .cuh-mirroring reference) using the documented R2 lane contract
/// (`compiler_v2::macros` module doc) to read operands; challenges are banks
/// (`SourceBanks`), never operand lanes (spec §5):
///   - `sh(x) = x + γ` reads `src.gamma` (the lookup additive challenge).
///   - GateOutputFold / VectorLookupGate α-powers are the column-indexed
///     ConstChallenge bank (`src.const_challenge[k] = α^k`, k > 0).
///   - MemoryTuple per-role permutation challenges + `perm_additive` are the
///     ArgChallenge bank read by role (`src.perm_challenges` / `src.perm_additive`).
///
/// Multi-output (num/den) routines return `vec![num, den]` — aligned to the
/// gate's two `Materialize` footer dsts in num-then-den order (`macro_gate_dsts`).
/// Single-value routines return `vec![v]` (broadcast to the one dst).
fn exec_macro(
    routine: RoutineId,
    ins: &crate::isa_v2::Instr2,
    src: &SourceBanks,
    read: &dyn Fn(&Operand) -> Ext,
) -> Vec<Ext> {
    let sh = |v: Ext| {
        // `sh(x) = x + γ` (the lookup routines' additive shift; mirror_gate).
        let mut r = v;
        r.add_assign(&src.gamma);
        r
    };
    match routine {
        RoutineId::GateOutputFold => vec![gate_output_fold(ins, src, read)],
        RoutineId::Product => vec![product(ins, read)],
        RoutineId::AggregateLookupPair => aggregate_lookup_pair(ins, read),
        // (v−1)·m + 1; lanes [input(v), mask(m)] (mirror_gate MaskIntoIdentityProduct).
        RoutineId::MaskIdentity => vec![mask_identity(ins, read)],
        // Symmetric pair, base/ext inputs: num = sh(b)+sh(d), den = sh(b)·sh(d);
        // lanes [b, d] (mirror_gate LookupPairFrom{,Materialized}{Base,Vector}Inputs).
        RoutineId::LookupBasePair | RoutineId::LookupExtPair => lookup_pair(ins, read, &sh),
        // Minus-multiplicity, base/ext: num = sh(d) − c·sh(b), den = sh(b)·sh(d);
        // lanes [b, c, d] (mirror_gate LookupFrom…WithSetup).
        RoutineId::LookupBaseMinusMult | RoutineId::LookupExtMinusMult => {
            lookup_minus_mult(ins, read, &sh)
        }
        // num = a·sh(d) − c·sh(b), den = sh(b)·sh(d); lanes [a, b, c, d]
        // (mirror_gate LookupWithCachedDensAndSetup). `LookupDecoderDensSetup`
        // shares the closed form (distinct operand provenance, same lanes).
        RoutineId::LookupCachedDens | RoutineId::LookupDecoderDensSetup => {
            lookup_cached_dens(ins, read, &sh)
        }
        // Unbalanced, base/ext: num = a·sh(d) + b, den = b·sh(d); lanes [a, b, d]
        // (mirror_gate LookupUnbalancedPairWith…).
        RoutineId::LookupUnbalancedBase | RoutineId::LookupUnbalancedExt => {
            lookup_unbalanced(ins, read, &sh)
        }
        // α-folded vector-lookup value, recomputed from the per-column lincomb
        // groups (id-17 lane layout) — gate form of the vectorized lookup.
        RoutineId::VectorLookupGate | RoutineId::VectorizedLookup => {
            vec![vectorized_lookup(ins, src, read)]
        }
        // A single base lincomb: constant + Σ coeff·col (id-16 lane layout).
        RoutineId::MaterializeSingleLookup | RoutineId::SingleColumnLookup => {
            vec![single_column_lincomb(ins, read)]
        }
        // GrandProductWithoutCaches: tuple(a)·tuple(b) — the product of two inlined
        // memory-tuple combos. MaterializeGrandProductTerm: tuple(input). Both are
        // MemTuple-shaped; the latter has 1 tuple, the former 2 (see fn doc).
        RoutineId::GrandProductWithoutCaches
        | RoutineId::MaterializeGrandProductTerm
        | RoutineId::MemoryTuple => vec![memory_tuple(ins, src, read)],
        // Row-indexed setup gather n[gid]: the single RowIndexedSetupE4 Indirect
        // operand (already resolved by `resolve_gather`).
        RoutineId::VectorizedLookupSetup => {
            debug_assert_eq!(
                ins.operands.len(),
                1,
                "VectorizedLookupSetup is a single RowIndexedSetupE4 gather"
            );
            vec![read(&ins.operands[0])]
        }
        // Inits/teardowns initial (num,den) pair (mirror_cache has no arm — the
        // corpus does not emit this gate; spec/probe STEP 0). The closed form is
        // not pinned from mirror_gate/lookup_helpers.cuh, so it is left here as a
        // precise TODO rather than guessed; no corpus test reaches this arm.
        RoutineId::MemoryInitTeardownPair => {
            // R3 TODO: InitsOrTeardownsInitialPair (id 20) — the inits/teardowns
            // initial (num,den) pair closed form is not present in `mirror_gate`
            // (no arm) nor `lookup_helpers.cuh`; pinning it needs the
            // InitsOrTeardownsInitialPair codegen math (cs codegen_ir.rs). The
            // corpus never emits it (probe STEP 0), so this arm is unreachable in
            // every test; do NOT guess the formula.
            todo!("R3 TODO: MemoryInitTeardownPair formula not pinned (no mirror_gate arm)")
        }
    }
}

/// `MaskIdentity` (routine 2, `gkr_eval_mask_identity`, lookup_helpers.cuh:219-223,
/// PK_MASK_IDENTITY): `out = (v−1)·m + 1`. Lanes `[input(v), mask(m)]`
/// (mirror_gate `MaskIntoIdentityProduct`).
fn mask_identity(ins: &crate::isa_v2::Instr2, read: &dyn Fn(&Operand) -> Ext) -> Ext {
    debug_assert_eq!(ins.operands.len(), 2, "MaskIdentity is [input, mask]");
    let v = read(&ins.operands[0]);
    let m = read(&ins.operands[1]);
    // (v − 1)·m + 1.
    let mut vm1 = v;
    vm1.sub_assign(&Ext::ONE);
    vm1.mul_assign(&m);
    vm1.add_assign(&Ext::ONE);
    vm1
}

/// `LookupBasePair` / `LookupExtPair` (routines 4/5, `gkr_eval_lookup_pair`,
/// lookup_helpers.cuh:242/250): symmetric pair `num = sh(b)+sh(d)`,
/// `den = sh(b)·sh(d)`. Lanes `[b, d]` (mirror_gate
/// `LookupPairFrom{,Materialized}{Base,Vector}Inputs`). Two ext outputs.
fn lookup_pair(
    ins: &crate::isa_v2::Instr2,
    read: &dyn Fn(&Operand) -> Ext,
    sh: &dyn Fn(Ext) -> Ext,
) -> Vec<Ext> {
    debug_assert_eq!(ins.operands.len(), 2, "lookup pair is [b, d]");
    let b = sh(read(&ins.operands[0]));
    let d = sh(read(&ins.operands[1]));
    // num = sh(b) + sh(d).
    let mut num = b;
    num.add_assign(&d);
    // den = sh(b)·sh(d).
    let mut den = b;
    den.mul_assign(&d);
    vec![num, den]
}

/// `LookupBaseMinusMult` / `LookupExtMinusMult` (routines 6/7,
/// lookup_helpers.cuh:268/276): `num = sh(d) − c·sh(b)`, `den = sh(b)·sh(d)`.
/// Lanes `[input(b), setup0(c), setup1(d)]` (mirror_gate `LookupFrom…WithSetup`).
/// `c` is NOT shifted (it is the setup multiplicity). Two ext outputs.
fn lookup_minus_mult(
    ins: &crate::isa_v2::Instr2,
    read: &dyn Fn(&Operand) -> Ext,
    sh: &dyn Fn(Ext) -> Ext,
) -> Vec<Ext> {
    debug_assert_eq!(ins.operands.len(), 3, "lookup minus-mult is [b, c, d]");
    let b = sh(read(&ins.operands[0]));
    let c = read(&ins.operands[1]);
    let d = sh(read(&ins.operands[2]));
    // num = sh(d) − c·sh(b).
    let mut cb = c;
    cb.mul_assign(&b);
    let mut num = d;
    num.sub_assign(&cb);
    // den = sh(b)·sh(d).
    let mut den = b;
    den.mul_assign(&d);
    vec![num, den]
}

/// `LookupCachedDens` / `LookupDecoderDensSetup` (routines 8/13,
/// lookup_helpers.cuh:313): `num = a·sh(d) − c·sh(b)`, `den = sh(b)·sh(d)`.
/// Lanes `[a, b, c, d]` (mirror_gate `LookupWithCachedDensAndSetup`). `a` and `c`
/// are NOT shifted; `b` and `d` are. Two ext outputs. id 13 shares the closed
/// form (decoder-predicate `a`, inline-vector `b`), same lane order.
fn lookup_cached_dens(
    ins: &crate::isa_v2::Instr2,
    read: &dyn Fn(&Operand) -> Ext,
    sh: &dyn Fn(Ext) -> Ext,
) -> Vec<Ext> {
    debug_assert_eq!(ins.operands.len(), 4, "cached-dens is [a, b, c, d]");
    let a = read(&ins.operands[0]);
    let b = sh(read(&ins.operands[1]));
    let c = read(&ins.operands[2]);
    let d = sh(read(&ins.operands[3]));
    // num = a·sh(d) − c·sh(b).
    let mut ad = a;
    ad.mul_assign(&d);
    let mut cb = c;
    cb.mul_assign(&b);
    let mut num = ad;
    num.sub_assign(&cb);
    // den = sh(b)·sh(d).
    let mut den = b;
    den.mul_assign(&d);
    vec![num, den]
}

/// `LookupUnbalancedBase` / `LookupUnbalancedExt` (routines 9/10,
/// lookup_helpers.cuh:300): `num = a·sh(d) + b`, `den = b·sh(d)`. Lanes
/// `[input0(a), input1(b), remainder(d)]` (mirror_gate `LookupUnbalancedPairWith…`).
/// `b` is NOT shifted; `d` is. Two ext outputs.
fn lookup_unbalanced(
    ins: &crate::isa_v2::Instr2,
    read: &dyn Fn(&Operand) -> Ext,
    sh: &dyn Fn(Ext) -> Ext,
) -> Vec<Ext> {
    debug_assert_eq!(ins.operands.len(), 3, "unbalanced is [a, b, d]");
    let a = read(&ins.operands[0]);
    let b = read(&ins.operands[1]);
    let d = sh(read(&ins.operands[2]));
    // num = a·sh(d) + b.
    let mut num = a;
    num.mul_assign(&d);
    num.add_assign(&b);
    // den = b·sh(d).
    let mut den = b;
    den.mul_assign(&d);
    vec![num, den]
}

/// `SingleColumnLookup` (id 16, cache) / `MaterializeSingleLookup` (id 12, gate
/// form): one base linear combination `value = constant + Σ_j coeff_j·col_j`
/// (mirror_cache `SingleColumnLookup` / `indep_lincomb`). R2 lane layout
/// (`macros` doc): `[Ldc(constant), (Ldc(coeff), col)…]`, `n_operands = 1 +
/// 2·terms`. Single output.
fn single_column_lincomb(ins: &crate::isa_v2::Instr2, read: &dyn Fn(&Operand) -> Ext) -> Ext {
    let ops = &ins.operands;
    debug_assert!(!ops.is_empty(), "id16 lincomb has a constant lane");
    debug_assert_eq!(ops.len() % 2, 1, "id16 lincomb is 1 const + 2·terms lanes");
    // lane 0 = constant; thereafter (coeff, col) pairs.
    let mut acc = read(&ops[0]);
    let mut i = 1;
    while i < ops.len() {
        let coeff = read(&ops[i]);
        let col = read(&ops[i + 1]);
        let mut term = coeff;
        term.mul_assign(&col);
        acc.add_assign(&term);
        i += 2;
    }
    acc
}

/// `VectorizedLookup` (id 17, cache) / `VectorLookupGate` (id 11, gate form):
/// the α-folded vector-lookup value `value = Σ_k α^k·(constant_k + Σ_j coeff·col)`
/// (mirror_cache `VectorizedLookup` / `indep_vec_lookup`). α^k is the
/// COLUMN-INDEXED ConstChallenge bank (α^0 = 1 free lift; α^k = `const_challenge[k]`
/// for k > 0). R2 self-describing lane layout (`macros` doc): per column `k` a
/// group `[Ldc(term_count_k), Ldc(constant_k), (Ldc(coeff), col)…]`. Single output.
fn vectorized_lookup(
    ins: &crate::isa_v2::Instr2,
    src: &SourceBanks,
    read: &dyn Fn(&Operand) -> Ext,
) -> Ext {
    let ops = &ins.operands;
    let mut acc = Ext::ZERO;
    let mut pos = 0usize;
    let mut k = 0usize; // column ordinal == α-power index.
    while pos < ops.len() {
        // term_count lane (its VALUE is the count; mirror_cache lane contract).
        let term_count = ext_to_usize(read(&ops[pos]));
        pos += 1;
        // column value = constant_k + Σ_j coeff·col.
        let mut col_val = read(&ops[pos]); // constant_k
        pos += 1;
        for _ in 0..term_count {
            let coeff = read(&ops[pos]);
            let col = read(&ops[pos + 1]);
            let mut term = coeff;
            term.mul_assign(&col);
            col_val.add_assign(&term);
            pos += 2;
        }
        // acc += α^k · col_val (α^0 = 1 is a free lift, no bank read).
        if k == 0 {
            acc.add_assign(&col_val);
        } else {
            let mut t = col_val;
            t.mul_assign(&src.const_challenge[k]);
            acc.add_assign(&t);
        }
        k += 1;
    }
    acc
}

/// `MemoryTuple` (id 19), `GrandProductWithoutCaches` (id 14), and
/// `MaterializeGrandProductTerm` (id 15). Each builds one or more memory-tuple
/// affine combinations `tuple = perm_additive + address_space_term +
/// Σ_role chal[role]·(lane value or constant)` (mirror_cache `MemoryTuple` /
/// `indep_mem_tuple`), reading challenges from the perm/additive bank by role.
///
/// id 19 (cache) materializes ONE tuple (the `MemTup` form: `roles` dynamic
/// terms + `as_arm`/`as_payload` + the R2 `consts` block). id 15 likewise
/// materializes ONE tuple. id 14 is the PRODUCT of TWO tuples — but in the
/// corpus only id 19 carries a `MemTup`; ids 14/15 are not emitted (probe STEP 0
/// — the `compile_forward_v2_runs_on_all_fixtures` test exercises every fixture
/// without panicking on them). They share this arm: a `MemTup` present →
/// single-tuple value; absent → R3 TODO (never reached in tests).
fn memory_tuple(
    ins: &crate::isa_v2::Instr2,
    src: &SourceBanks,
    read: &dyn Fn(&Operand) -> Ext,
) -> Ext {
    let Some(mt) = &ins.memtup else {
        // R3 TODO: GrandProductWithoutCaches (14) / MaterializeGrandProductTerm
        // (15) carry their inlined memory-tuple combos on the forward setup, not a
        // `MemTup` lane block — the corpus never emits them (probe STEP 0), so no
        // test reaches here. Pinning needs the cs codegen for those gates.
        todo!(
            "R3 TODO: grand-product-without-caches tuple combo not on the MemTup lanes \
             (corpus never emits id 14/15; do NOT guess)"
        );
    };
    // tuple = perm_additive + address-space term + Σ_role chal[role]·term.
    let mut acc = src.perm_additive;

    // Address-space arm (mirror cache_relation.rs / indep_mem_tuple): the arm
    // term carries NO permutation challenge.
    //   1 Constant(c) → acc += c        (as_payload is the Ldc value)
    //   2 IsRegister  → acc += 1 − col  (as_payload is the register column)
    //   3 IsRam       → acc += col      (coeff ONE)
    //   0 Empty       → no contribution
    match mt.as_arm {
        1 => {
            // Constant address-space: the Ldc payload added directly.
            let c = read(mt.as_payload.as_ref().expect("Constant arm carries a payload"));
            acc.add_assign(&c);
        }
        2 => {
            // IsRegister: 1 − col.
            let col = read(mt.as_payload.as_ref().expect("IsRegister arm carries a payload"));
            acc.add_assign(&Ext::ONE);
            acc.sub_assign(&col);
        }
        3 => {
            // IsRam: + col (coeff one).
            let col = read(mt.as_payload.as_ref().expect("IsRam arm carries a payload"));
            acc.add_assign(&col);
        }
        0 => {}
        other => panic!("memory-tuple as_arm {other} out of 0..=3"),
    }

    // Pre-scan the folded-constant block for the special-indirect dynamic-offset
    // coefficient: it does NOT contribute on its own; it SCALES the term-7
    // (VALUE_HIGH_EXTRA) column under chal(R_ADDR_LOW) (indep_mem_tuple:291-295).
    let mut dyn_coeff: Option<Ext> = None;
    for (role, op) in &mt.consts {
        if *role == MT_CONST_ADDR_LOW_DYN_COEFF {
            dyn_coeff = Some(read(op));
        }
    }

    // Dynamic role-tagged linear terms: acc += chal(role)·col. Term slot 7
    // (VALUE_HIGH_EXTRA) is the special-indirect dyn-offset column: its challenge
    // is chal(R_ADDR_LOW) further scaled by `dyn_coeff` (folded constant).
    for (term, op) in &mt.roles {
        let col = read(op);
        let mut chal = if *term == MEMORY_TUPLE_VALUE_HIGH_EXTRA_TERM {
            let mut c = src.perm_challenges[R_PERM_ADDR_LOW];
            c.mul_assign(
                &dyn_coeff.expect("term-7 dyn-offset column requires its MT_CONST_ADDR_LOW_DYN_COEFF"),
            );
            c
        } else {
            src.perm_challenges[perm_role_for_memtup_term(*term)]
        };
        chal.mul_assign(&col);
        acc.add_assign(&chal);
    }

    // Folded-constant terms: each `(MT_CONST_* role, Ldc value)` is added as
    // chal(role)·value. The dyn-coeff is consumed above (scales term 7), so it
    // contributes nothing standalone.
    for (role, op) in &mt.consts {
        let val = read(op);
        let chal_role = match *role {
            MT_CONST_ADDR_LOW | MT_CONST_ADDR_LOW_OFFSET => R_PERM_ADDR_LOW,
            MT_CONST_TS_LOW_OFFSET => R_PERM_TS_LOW,
            MT_CONST_ADDR_LOW_DYN_COEFF => continue, // folded into term 7 above
            other => panic!("memory-tuple const role {other} unknown"),
        };
        let mut t = src.perm_challenges[chal_role];
        t.mul_assign(&val);
        acc.add_assign(&t);
    }

    acc
}

/// Decode an `Ext` known to hold a small base-field count (the id-17 `term_count`
/// lane VALUE). The high limbs must be zero; the low limb is the count.
fn ext_to_usize(v: Ext) -> usize {
    let coeffs = <Ext as FieldExtension<Bf>>::into_coeffs(v);
    debug_assert!(
        coeffs[1].is_zero() && coeffs[2].is_zero() && coeffs[3].is_zero(),
        "term_count lane is a base-field scalar"
    );
    coeffs[0].as_u32_reduced() as usize
}

/// `Product` (routine 1, PK_PRODUCT → `gkr_eval_product`, `lookup_helpers.cuh`):
/// `out = a · b` over the two ext factors. One product node folded into the
/// running grand product.
///
/// Operand layout (macros.rs `lower_gate` + `gate_kind_input_nodes`): the gate's
/// two input nodes ride operand lanes 0 and 1 — for `TrivialProduct` /
/// `InitialGrandProductFromCaches` that is `input.to_vec()` (the two factors),
/// for `UnbalancedGrandProductWithCache` it is `[scalar, input]`. No challenge
/// (schema `ChallengeUse::None`). Single ext output → one footer dst.
fn product(ins: &crate::isa_v2::Instr2, read: &dyn Fn(&Operand) -> Ext) -> Ext {
    debug_assert_eq!(
        ins.operands.len(),
        2,
        "Product is a 2-factor product (gkr_eval_product)"
    );
    let mut a = read(&ins.operands[0]);
    let b = read(&ins.operands[1]);
    a.mul_assign(&b);
    a
}

/// `AggregateLookupPair` (routine 3, `lookup_helpers.cuh:229` `gkr_eval_lookup_pair`,
/// via `AggregateLookupRationalPair` — the only id-3 kind the corpus emits):
/// combine two rational `(num,den)` pairs `(a,b)` and `(c,d)` into one:
///   num = a·d + c·b      (cross-multiplied numerator)
///   den = b·d            (product of denominators)
///
/// Operand layout (macros.rs `lower_gate` + `gate_kind_input_nodes`,
/// `codegen_ir.rs:1318` `input.iter().flat_map(|pair| pair.iter())`): the IR
/// input is `[[a,b],[c,d]]`, flattened to operand lanes `[a, b, c, d]` in that
/// order. Two ext outputs → two footer dsts (num then den, `macro_gate_dsts`).
/// No challenge folding in the reference (`mirror_gate`
/// `bench_interp/tests.rs:350-352` applies none, despite the schema tagging
/// `ConstAlphaGamma` for the more general cascade form).
fn aggregate_lookup_pair(ins: &crate::isa_v2::Instr2, read: &dyn Fn(&Operand) -> Ext) -> Vec<Ext> {
    debug_assert_eq!(
        ins.operands.len(),
        4,
        "AggregateLookupPair combines two (num,den) pairs = 4 ext operands"
    );
    let a = read(&ins.operands[0]);
    let b = read(&ins.operands[1]);
    let c = read(&ins.operands[2]);
    let d = read(&ins.operands[3]);
    // num = a·d + c·b.
    let mut num = a;
    num.mul_assign(&d);
    let mut cb = c;
    cb.mul_assign(&b);
    num.add_assign(&cb);
    // den = b·d.
    let mut den = b;
    den.mul_assign(&d);
    vec![num, den]
}

/// `GateOutputFold` (routine 0, `gkr_forward_generation.cuh E_FMA_ALPHA`):
/// `acc = Σ_k α^k · col_k`. Operands are the source columns col_k in order;
/// challenges are NOT operand lanes (spec §5) — α^k is read from the
/// `const_challenge` bank indexed by operand position k. α^0 = 1 is a free lift
/// (no bank read), matching `challenges::alpha_power_bank_index`.
fn gate_output_fold(
    ins: &crate::isa_v2::Instr2,
    src: &SourceBanks,
    read: &dyn Fn(&Operand) -> Ext,
) -> Ext {
    let mut acc = Ext::ZERO;
    for (k, o) in ins.operands.iter().enumerate() {
        let col = read(o);
        if k == 0 {
            // α^0 = 1: multiply-free lift.
            acc.add_assign(&col);
        } else {
            let mut term = col;
            let alpha_k = src.const_challenge[k];
            term.mul_assign(&alpha_k);
            acc.add_assign(&term);
        }
    }
    acc
}

/// Recover a `RoutineId` from the 7-bit header byte (mirrors the compiler's
/// `routine_from_u8`; an out-of-range byte is a corrupt program).
fn routine_from_u8(routine: u8) -> RoutineId {
    match routine {
        0 => RoutineId::GateOutputFold,
        1 => RoutineId::Product,
        2 => RoutineId::MaskIdentity,
        3 => RoutineId::AggregateLookupPair,
        4 => RoutineId::LookupBasePair,
        5 => RoutineId::LookupExtPair,
        6 => RoutineId::LookupBaseMinusMult,
        7 => RoutineId::LookupExtMinusMult,
        8 => RoutineId::LookupCachedDens,
        9 => RoutineId::LookupUnbalancedBase,
        10 => RoutineId::LookupUnbalancedExt,
        11 => RoutineId::VectorLookupGate,
        12 => RoutineId::MaterializeSingleLookup,
        13 => RoutineId::LookupDecoderDensSetup,
        14 => RoutineId::GrandProductWithoutCaches,
        15 => RoutineId::MaterializeGrandProductTerm,
        16 => RoutineId::SingleColumnLookup,
        17 => RoutineId::VectorizedLookup,
        18 => RoutineId::VectorizedLookupSetup,
        19 => RoutineId::MemoryTuple,
        20 => RoutineId::MemoryInitTeardownPair,
        other => panic!("unknown routine id {other} in fused program header"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::isa_v2::Instr2;

    fn bf(v: u32) -> Bf {
        Bf::from_u32_with_reduction(v)
    }

    /// Smoke test: a Sum over two Affine sources, a Dot (sum-of-products), and a
    /// GateOutputFold reading α from `const_challenge`. Assert the three
    /// Materialize outputs equal hand-computed references.
    #[test]
    fn sum_dot_and_fold_execute() {
        // Matrix slot 0 (ext-field backing) holds the source columns we read,
        // plus the three output columns we Materialize into.
        //   col 0 = 3, col 1 = 5, col 2 = 7, col 3 = 11
        //   cols 4,5,6 reserved for the Sum/Dot/Fold outputs.
        let matrix = vec![MatrixSlotData {
            field_ext: true,
            columns: vec![
                lift(bf(3)),
                lift(bf(5)),
                lift(bf(7)),
                lift(bf(11)),
                Ext::ZERO,
                Ext::ZERO,
                Ext::ZERO,
            ],
        }];

        // α = 2 (lifted). const_challenge[k] holds α^k for k >= 1; entry 0 is
        // unused (α^0 is a free lift in the fold).
        let alpha = lift(bf(2));
        let mut alpha2 = alpha;
        alpha2.mul_assign(&alpha); // α^2 = 4
        let const_challenge = vec![Ext::ZERO, alpha, alpha2];

        let src = SourceBanks {
            matrix,
            consts: vec![],
            const_challenge,
            arg_challenge: vec![],
            gamma: Ext::ZERO,
            perm_challenges: vec![],
            perm_additive: Ext::ZERO,
            gather_tables: GatherTables::default(),
            gid: 0,
        };

        let p = Program2 {
            instrs: vec![
                // SumK: col0 + col1 = 3 + 5 = 8 → Materialize slot 0 col 4.
                Instr2 {
                    header: Header::Arith { op: ArithOp::Sum, arity: 2 },
                    operands: vec![
                        Operand::Affine { slot: 0, col: 0 },
                        Operand::Affine { slot: 0, col: 1 },
                    ],
                    dsts: vec![Dst::Materialize { slot: 0, col: 4 }],
                    memtup: None,
                },
                // DotK: col0*col1 + col2*col3 = 3*5 + 7*11 = 15 + 77 = 92
                //       → Materialize slot 0 col 5.
                Instr2 {
                    header: Header::Arith { op: ArithOp::Dot, arity: 2 },
                    operands: vec![
                        Operand::Affine { slot: 0, col: 0 },
                        Operand::Affine { slot: 0, col: 1 },
                        Operand::Affine { slot: 0, col: 2 },
                        Operand::Affine { slot: 0, col: 3 },
                    ],
                    dsts: vec![Dst::Materialize { slot: 0, col: 5 }],
                    memtup: None,
                },
                // GateOutputFold: α^0·col0 + α^1·col1 + α^2·col2
                //   = 1*3 + 2*5 + 4*7 = 3 + 10 + 28 = 41 → Materialize slot 0 col 6.
                Instr2 {
                    header: Header::Macro {
                        routine: RoutineId::GateOutputFold as u8,
                        n_operands: 3,
                    },
                    operands: vec![
                        Operand::Affine { slot: 0, col: 0 },
                        Operand::Affine { slot: 0, col: 1 },
                        Operand::Affine { slot: 0, col: 2 },
                    ],
                    dsts: vec![Dst::Materialize { slot: 0, col: 6 }],
                    memtup: None,
                },
            ],
            consts: vec![],
            n_slot_cells: 0,
            n_matrix_slots: 1,
        };

        let got = execute2(&p, &[], &src);

        // Hand references.
        let expect_sum = lift(bf(8)); // 3 + 5
        let expect_dot = lift(bf(92)); // 3*5 + 7*11
        let expect_fold = lift(bf(41)); // 1*3 + 2*5 + 4*7

        assert_eq!(got.materialized.len(), 3);
        assert_eq!(got.materialized[0], ((0, 4), expect_sum));
        assert_eq!(got.materialized[1], ((0, 5), expect_dot));
        assert_eq!(got.materialized[2], ((0, 6), expect_fold));
    }

    // -----------------------------------------------------------------------
    // R3 per-routine unit oracle. Each test builds a hand `Instr2` with the
    // documented R2 lane layout + a `SourceBanks` with KNOWN challenge values,
    // runs `execute2`, and asserts the materialized output(s) equal a HAND
    // reference computed with a DIFFERENT decomposition than the impl (a
    // re-ordered product/sum, a commuted cross-term, or a re-expanded fold), so
    // a transcription slip in the impl diverges from the test. Field values are
    // small concrete bf so the expectation is checkable by inspection.
    // -----------------------------------------------------------------------

    fn e(v: u32) -> Ext {
        lift(bf(v))
    }

    /// A `SourceBanks` whose matrix slot 0 (ext) holds `cols` and that carries
    /// the given γ + perm challenges + perm_additive + α-power bank. Operand
    /// `Affine{slot:0, col:k}` reads `cols[k]`.
    fn banks(
        cols: Vec<Ext>,
        gamma: Ext,
        perm_challenges: Vec<Ext>,
        perm_additive: Ext,
        const_challenge: Vec<Ext>,
    ) -> SourceBanks {
        SourceBanks {
            matrix: vec![MatrixSlotData { field_ext: true, columns: cols }],
            consts: vec![],
            const_challenge,
            arg_challenge: vec![],
            gamma,
            perm_challenges,
            perm_additive,
            gather_tables: GatherTables::default(),
            gid: 0,
        }
    }

    /// Run one macro `routine` over `n_operands` consecutive `Affine` lanes
    /// (cols 0..n_operands) materializing `output_count` outputs into cols
    /// `n_operands..`. Returns the materialized values in dst order. `memtup` and
    /// extra lanes can be injected by the caller via a custom `Instr2`.
    fn run(
        routine: RoutineId,
        operands: Vec<Operand>,
        output_count: usize,
        memtup: Option<crate::isa_v2::MemTup>,
        src: &SourceBanks,
    ) -> Vec<Ext> {
        let n = operands.len();
        let dsts: Vec<Dst> = (0..output_count)
            .map(|j| Dst::Materialize { slot: 0, col: (n + j) as u16 })
            .collect();
        let p = Program2 {
            instrs: vec![Instr2 {
                header: Header::Macro {
                    routine: routine as u8,
                    n_operands: if memtup.is_some() {
                        memtup.as_ref().unwrap().roles.len() as u8
                    } else {
                        n as u8
                    },
                },
                operands,
                dsts,
                memtup,
            }],
            consts: vec![],
            n_slot_cells: 0,
            n_matrix_slots: 1,
        };
        execute2(&p, &[], src).materialized.iter().map(|(_, v)| *v).collect()
    }

    fn aff(col: u16) -> Operand {
        Operand::Affine { slot: 0, col }
    }

    /// id 1 — Product `a·b`. Different decomposition: `(b·a)` commuted.
    #[test]
    fn product_unit() {
        // cols [a=3, b=5]; out col 2.
        let src = banks(vec![e(3), e(5), Ext::ZERO], Ext::ZERO, vec![], Ext::ZERO, vec![]);
        let got = run(RoutineId::Product, vec![aff(0), aff(1)], 1, None, &src);
        // impl: a·b. reference: b·a.
        let mut expect = e(5);
        expect.mul_assign(&e(3));
        assert_eq!(got, vec![expect]);
        assert_eq!(expect, e(15));
    }

    /// id 2 — MaskIdentity `(v−1)·m + 1`. Different decomposition: expand to
    /// `v·m − m + 1`.
    #[test]
    fn mask_identity_unit() {
        // cols [v=7, m=4]; out col 2.
        let src = banks(vec![e(7), e(4), Ext::ZERO], Ext::ZERO, vec![], Ext::ZERO, vec![]);
        let got = run(RoutineId::MaskIdentity, vec![aff(0), aff(1)], 1, None, &src);
        // reference: v·m − m + 1 = 28 − 4 + 1 = 25.
        let (v, m) = (e(7), e(4));
        let mut expect = v;
        expect.mul_assign(&m); // v·m
        expect.sub_assign(&m); // − m
        expect.add_assign(&Ext::ONE);
        assert_eq!(got, vec![expect]);
        assert_eq!(expect, e(25));
    }

    /// id 3 — AggregateLookupPair `num=a·d+c·b, den=b·d`; lanes [a,b,c,d].
    /// Different decomposition: den=d·b, num=c·b + d·a.
    #[test]
    fn aggregate_lookup_pair_unit() {
        // cols [a=2,b=3,c=5,d=7]; outs cols 4,5.
        let src = banks(
            vec![e(2), e(3), e(5), e(7), Ext::ZERO, Ext::ZERO],
            Ext::ZERO,
            vec![],
            Ext::ZERO,
            vec![],
        );
        let got = run(
            RoutineId::AggregateLookupPair,
            vec![aff(0), aff(1), aff(2), aff(3)],
            2,
            None,
            &src,
        );
        let (a, b, c, d) = (e(2), e(3), e(5), e(7));
        let mut den = d;
        den.mul_assign(&b); // d·b
        let mut t0 = c;
        t0.mul_assign(&b); // c·b
        let mut t1 = d;
        t1.mul_assign(&a); // d·a
        let mut num = t0;
        num.add_assign(&t1); // c·b + d·a
        assert_eq!(got, vec![num, den]);
        // a·d+c·b = 14+15 = 29; b·d = 21.
        assert_eq!(num, e(29));
        assert_eq!(den, e(21));
    }

    /// ids 4/5 — LookupBasePair / LookupExtPair: num=sh(b)+sh(d), den=sh(b)·sh(d);
    /// lanes [b,d]; sh(x)=x+γ. Different decomposition: shift via a separate
    /// gamma-add and form den as sh(d)·sh(b).
    #[test]
    fn lookup_pair_unit() {
        let gamma = e(10);
        // cols [b=3, d=4]; outs 2,3.
        let src = banks(vec![e(3), e(4), Ext::ZERO, Ext::ZERO], gamma, vec![], Ext::ZERO, vec![]);
        for routine in [RoutineId::LookupBasePair, RoutineId::LookupExtPair] {
            let got = run(routine, vec![aff(0), aff(1)], 2, None, &src);
            // sh(b)=13, sh(d)=14. num=27, den=182.
            let mut shb = e(3);
            shb.add_assign(&gamma);
            let mut shd = e(4);
            shd.add_assign(&gamma);
            let mut num = shd;
            num.add_assign(&shb); // sh(d)+sh(b) (reverse add order)
            let mut den = shd;
            den.mul_assign(&shb); // sh(d)·sh(b)
            assert_eq!(got, vec![num, den], "{routine:?}");
            assert_eq!(num, e(27));
            assert_eq!(den, e(182));
        }
    }

    /// ids 6/7 — Lookup{Base,Ext}MinusMult: num=sh(d) − c·sh(b), den=sh(b)·sh(d);
    /// lanes [b,c,d]; c NOT shifted. Different decomposition: num as
    /// −(c·sh(b)) + sh(d).
    #[test]
    fn lookup_minus_mult_unit() {
        let gamma = e(10);
        // cols [b=3, c=2, d=4]; outs 3,4.
        let src = banks(
            vec![e(3), e(2), e(4), Ext::ZERO, Ext::ZERO],
            gamma,
            vec![],
            Ext::ZERO,
            vec![],
        );
        for routine in [RoutineId::LookupBaseMinusMult, RoutineId::LookupExtMinusMult] {
            let got = run(routine, vec![aff(0), aff(1), aff(2)], 2, None, &src);
            // sh(b)=13, sh(d)=14, c=2. num=14 − 2·13 = 14 − 26 = −12; den=13·14=182.
            let (mut shb, c, mut shd) = (e(3), e(2), e(4));
            shb.add_assign(&gamma);
            shd.add_assign(&gamma);
            let mut neg_cb = c;
            neg_cb.mul_assign(&shb);
            neg_cb.negate(); // −c·sh(b)
            let mut num = neg_cb;
            num.add_assign(&shd); // −c·sh(b) + sh(d)
            let mut den = shb;
            den.mul_assign(&shd);
            assert_eq!(got, vec![num, den], "{routine:?}");
            assert_eq!(den, e(182));
            // num = 14 − 26 = −12.
            let mut neg12 = e(12);
            neg12.negate();
            assert_eq!(num, neg12);
        }
    }

    /// ids 8/13 — LookupCachedDens / LookupDecoderDensSetup: num=a·sh(d) − c·sh(b),
    /// den=sh(b)·sh(d); lanes [a,b,c,d]; a,c NOT shifted. Different decomposition:
    /// num as a·sh(d) plus the negated c·sh(b).
    #[test]
    fn lookup_cached_dens_unit() {
        let gamma = e(10);
        // cols [a=5,b=3,c=2,d=4]; outs 4,5.
        let src = banks(
            vec![e(5), e(3), e(2), e(4), Ext::ZERO, Ext::ZERO],
            gamma,
            vec![],
            Ext::ZERO,
            vec![],
        );
        for routine in [RoutineId::LookupCachedDens, RoutineId::LookupDecoderDensSetup] {
            let got = run(routine, vec![aff(0), aff(1), aff(2), aff(3)], 2, None, &src);
            // sh(b)=13, sh(d)=14. num=5·14 − 2·13 = 70 − 26 = 44; den=182.
            let (a, mut shb, c, mut shd) = (e(5), e(3), e(2), e(4));
            shb.add_assign(&gamma);
            shd.add_assign(&gamma);
            let mut ad = a;
            ad.mul_assign(&shd);
            let mut cb = c;
            cb.mul_assign(&shb);
            cb.negate();
            let mut num = ad;
            num.add_assign(&cb); // a·sh(d) + (−c·sh(b))
            let mut den = shb;
            den.mul_assign(&shd);
            assert_eq!(got, vec![num, den], "{routine:?}");
            assert_eq!(num, e(44));
            assert_eq!(den, e(182));
        }
    }

    /// ids 9/10 — LookupUnbalanced{Base,Ext}: num=a·sh(d)+b, den=b·sh(d);
    /// lanes [a,b,d]; b NOT shifted. Different decomposition: num as b + sh(d)·a.
    #[test]
    fn lookup_unbalanced_unit() {
        let gamma = e(10);
        // cols [a=5,b=3,d=4]; outs 3,4.
        let src = banks(
            vec![e(5), e(3), e(4), Ext::ZERO, Ext::ZERO],
            gamma,
            vec![],
            Ext::ZERO,
            vec![],
        );
        for routine in [RoutineId::LookupUnbalancedBase, RoutineId::LookupUnbalancedExt] {
            let got = run(routine, vec![aff(0), aff(1), aff(2)], 2, None, &src);
            // sh(d)=14. num=5·14 + 3 = 73; den=3·14 = 42.
            let (a, b, mut shd) = (e(5), e(3), e(4));
            shd.add_assign(&gamma);
            let mut da = shd;
            da.mul_assign(&a); // sh(d)·a
            let mut num = b;
            num.add_assign(&da); // b + sh(d)·a
            let mut den = b;
            den.mul_assign(&shd);
            assert_eq!(got, vec![num, den], "{routine:?}");
            assert_eq!(num, e(73));
            assert_eq!(den, e(42));
        }
    }

    /// ids 16/12 — SingleColumnLookup / MaterializeSingleLookup: value =
    /// constant + Σ coeff·col; lanes [Ldc(const), (Ldc(coeff), col)…]. Here the
    /// coeffs/constant ride Affine lanes carrying their values (the read closure
    /// is lane-kind agnostic), so we drive them as columns. Different
    /// decomposition: accumulate the terms in reverse, then add the constant.
    #[test]
    fn single_column_lincomb_unit() {
        // value = const(2) + 3·col(=10) + 5·col(=7).
        // cols: [const=2, coeff0=3, x0=10, coeff1=5, x1=7]; out col 5.
        let src = banks(
            vec![e(2), e(3), e(10), e(5), e(7), Ext::ZERO],
            Ext::ZERO,
            vec![],
            Ext::ZERO,
            vec![],
        );
        for routine in [RoutineId::SingleColumnLookup, RoutineId::MaterializeSingleLookup] {
            let got = run(
                routine,
                vec![aff(0), aff(1), aff(2), aff(3), aff(4)],
                1,
                None,
                &src,
            );
            // reference: 5·7 + 3·10 + 2 = 35 + 30 + 2 = 67 (reverse term order).
            let mut acc = Ext::ZERO;
            let mut t1 = e(5);
            t1.mul_assign(&e(7));
            acc.add_assign(&t1);
            let mut t0 = e(3);
            t0.mul_assign(&e(10));
            acc.add_assign(&t0);
            acc.add_assign(&e(2));
            assert_eq!(got, vec![acc], "{routine:?}");
            assert_eq!(acc, e(67));
        }
    }

    /// ids 17/11 — VectorizedLookup / VectorLookupGate: value =
    /// Σ_k α^k·(constant_k + Σ coeff·col), self-describing groups
    /// [Ldc(term_count), Ldc(const), (Ldc(coeff), col)…]; α^k column-indexed.
    /// Two columns with DIFFERENT term counts (1 and 2) exercise the
    /// self-describing decode. Different decomposition: compute each column sum,
    /// then weight by α-powers folded outside-in.
    #[test]
    fn vectorized_lookup_unit() {
        // α = 2 ⇒ α^0 = 1, α^1 = 2. const_challenge[1] = α^1.
        let alpha = e(2);
        let const_challenge = vec![Ext::ZERO, alpha];
        // col 0: term_count=1, const=1, (coeff=3, x=4)  ⇒ 1 + 3·4 = 13.
        // col 1: term_count=2, const=2, (coeff=5,x=6),(coeff=7,x=8) ⇒ 2 + 30 + 56 = 88.
        // value = α^0·13 + α^1·88 = 13 + 2·88 = 13 + 176 = 189.
        // operand lanes (all via Affine columns carrying the literal values):
        //   [tc=1, c=1, coeff=3, x=4, tc=2, c=2, coeff=5, x=6, coeff=7, x=8]; out col 10.
        let cols = vec![
            e(1),  // 0 tc col0
            e(1),  // 1 const col0
            e(3),  // 2 coeff
            e(4),  // 3 x
            e(2),  // 4 tc col1
            e(2),  // 5 const col1
            e(5),  // 6 coeff
            e(6),  // 7 x
            e(7),  // 8 coeff
            e(8),  // 9 x
            Ext::ZERO,
        ];
        let src = banks(cols, Ext::ZERO, vec![], Ext::ZERO, const_challenge);
        let operands: Vec<Operand> = (0..10).map(aff).collect();
        for routine in [RoutineId::VectorizedLookup, RoutineId::VectorLookupGate] {
            let got = run(routine, operands.clone(), 1, None, &src);
            // reference: col1 sum first, weighted by α^1; then col0 weighted by α^0.
            let mut col1 = e(2);
            let mut a = e(5);
            a.mul_assign(&e(6));
            col1.add_assign(&a);
            let mut b = e(7);
            b.mul_assign(&e(8));
            col1.add_assign(&b); // 88
            let mut weighted1 = col1;
            weighted1.mul_assign(&alpha); // α^1·88 = 176
            let mut col0 = e(1);
            let mut c = e(3);
            c.mul_assign(&e(4));
            col0.add_assign(&c); // 13
            let mut expect = weighted1;
            expect.add_assign(&col0); // 176 + 13
            assert_eq!(got, vec![expect], "{routine:?}");
            assert_eq!(expect, e(189));
        }
    }

    /// id 18 — VectorizedLookupSetup: value = the single RowIndexedSetupE4 gather
    /// n[gid]. Drive a gather table directly and confirm the value passes through.
    #[test]
    fn vectorized_lookup_setup_unit() {
        let setup: Vec<Ext> = vec![e(200), e(201), e(202)];
        let gather_tables = GatherTables {
            n: vec![setup.clone()],
            mapping: vec![Vec::new()],
            n_len: vec![Some(setup.len())],
            decoder_mask: vec![None],
            alpha_powers: vec![],
        };
        let descs = vec![GatherDescriptor {
            kind: IndirectKind::RowIndexedSetupE4,
            field_ext: true,
            n_slot: None,
            mapping_slot: None,
            n_len: None,
            decoder: None,
        }];
        let mut src = banks(vec![Ext::ZERO], Ext::ZERO, vec![], Ext::ZERO, vec![]);
        src.gather_tables = gather_tables;
        src.gid = 1; // n[1] = 201.
        let p = Program2 {
            instrs: vec![Instr2 {
                header: Header::Macro {
                    routine: RoutineId::VectorizedLookupSetup as u8,
                    n_operands: 1,
                },
                operands: vec![Operand::Indirect { e4: true, desc: 0 }],
                dsts: vec![Dst::Materialize { slot: 0, col: 0 }],
                memtup: None,
            }],
            consts: vec![],
            n_slot_cells: 0,
            n_matrix_slots: 1,
        };
        let got = execute2(&p, &descs, &src);
        assert_eq!(got.materialized, vec![((0, 0), e(201))]);
    }

    /// id 19 — MemoryTuple: tuple = perm_additive + address-space term +
    /// Σ_role chal[role]·term + folded-const terms. Cover IsRam arm + addr lo/hi
    /// + ts lo/hi + value lo/hi roles + a constant address term + ts offset.
    /// Different decomposition: build the role contributions in a shuffled order
    /// and the constant terms with the challenge applied after the product.
    #[test]
    fn memory_tuple_unit() {
        use crate::isa_v2::MemTup;
        // perm_additive = 100. perm_challenges by role (distinct so a wrong-role
        // mapping diverges):
        //   R_ADDR_LOW=2, R_ADDR_HIGH=3, R_TS_LOW=4, R_TS_HIGH=5, R_VAL_LOW=6, R_VAL_HIGH=7.
        let perm = vec![e(2), e(3), e(4), e(5), e(6), e(7)];
        let perm_additive = e(100);
        // cols (Affine sources):
        //   0 = as_payload (IsRam col) = 9
        //   1 = addr_low term col = 11
        //   2 = addr_high term col = 13
        //   3 = ts_low term col = 17
        //   4 = ts_high term col = 19
        //   5 = val_low term col = 23
        //   6 = val_high term col = 29
        //   7 = const addr_low value = 31
        //   8 = const ts_low_offset value = 37
        //   9 = out
        let cols = vec![
            e(9), e(11), e(13), e(17), e(19), e(23), e(29), e(31), e(37), Ext::ZERO,
        ];
        let src = banks(cols, Ext::ZERO, perm.clone(), perm_additive, vec![]);
        let memtup = MemTup {
            roles: vec![
                (0, aff(1)), // ADDRESS_LOW_TERM  → R_ADDR_LOW
                (1, aff(2)), // ADDRESS_HIGH_TERM → R_ADDR_HIGH
                (2, aff(3)), // TIMESTAMP_LOW_TERM → R_TS_LOW
                (3, aff(4)), // TIMESTAMP_HIGH_TERM → R_TS_HIGH
                (4, aff(5)), // VALUE_LOW_TERM → R_VAL_LOW
                (6, aff(6)), // VALUE_HIGH_TERM → R_VAL_HIGH
            ],
            as_arm: 3, // IsRam → + col
            as_payload: Some(aff(0)),
            consts: vec![
                (MT_CONST_ADDR_LOW, aff(7)),      // chal(R_ADDR_LOW)·31
                (MT_CONST_TS_LOW_OFFSET, aff(8)), // chal(R_TS_LOW)·37
            ],
        };
        let got = run(RoutineId::MemoryTuple, vec![], 1, Some(memtup), &src);

        // Reference (different decomposition: sum role·challenge products in a
        // shuffled order, apply each constant challenge AFTER reading the value).
        // tuple = 100 (additive) + 9 (IsRam)
        //   + 2·11 + 3·13 + 4·17 + 5·19 + 6·23 + 7·29   (role terms)
        //   + 2·31 (addr_low const) + 4·37 (ts_low const)
        let pairs = [
            (perm[4], e(23)), // val_low
            (perm[1], e(13)), // addr_high
            (perm[5], e(29)), // val_high
            (perm[0], e(11)), // addr_low
            (perm[3], e(19)), // ts_high
            (perm[2], e(17)), // ts_low
        ];
        let mut acc = e(100);
        acc.add_assign(&e(9)); // IsRam payload
        for (ch, col) in pairs {
            let mut t = col;
            t.mul_assign(&ch); // col·chal (commuted)
            acc.add_assign(&t);
        }
        let mut ca = e(31);
        ca.mul_assign(&perm[0]);
        acc.add_assign(&ca);
        let mut ct = e(37);
        ct.mul_assign(&perm[2]);
        acc.add_assign(&ct);
        assert_eq!(got, vec![acc]);
        // Numeric: 100+9 + (22+39+68+95+138+203) + 62 + 148 = 109 + 565 + 210 = 884.
        assert_eq!(acc, e(884));
    }

    /// id 19 — MemoryTuple special-indirect arm: the term-7 (VALUE_HIGH_EXTRA)
    /// dynamic-offset column is scaled by chal(R_ADDR_LOW)·dyn_coeff, the
    /// `low_offset` folds under chal(R_ADDR_LOW). Different decomposition:
    /// pre-multiply dyn_coeff·col, then apply the addr-low challenge.
    #[test]
    fn memory_tuple_special_indirect_unit() {
        use crate::isa_v2::MemTup;
        // R_ADDR_LOW challenge = 2. perm_additive = 0 (isolate the indirect math).
        let perm = vec![e(2), e(3), e(4), e(5), e(6), e(7)];
        // cols: 0 = dyn-offset col (term7) = 5; 1 = dyn_coeff value = 9;
        //       2 = low_offset value = 4; 3 = out.
        let cols = vec![e(5), e(9), e(4), Ext::ZERO];
        let src = banks(cols, Ext::ZERO, perm.clone(), Ext::ZERO, vec![]);
        let memtup = MemTup {
            roles: vec![(MEMORY_TUPLE_VALUE_HIGH_EXTRA_TERM, aff(0))],
            as_arm: 0, // Empty (no address-space contribution)
            as_payload: None,
            consts: vec![
                (MT_CONST_ADDR_LOW_DYN_COEFF, aff(1)),
                (MT_CONST_ADDR_LOW_OFFSET, aff(2)),
            ],
        };
        let got = run(RoutineId::MemoryTuple, vec![], 1, Some(memtup), &src);
        // tuple = chal(ADDR_LOW)·dyn_coeff·col(term7) + chal(ADDR_LOW)·low_offset
        //       = 2·9·5 + 2·4 = 90 + 8 = 98.
        let mut dyn_term = e(9); // dyn_coeff
        dyn_term.mul_assign(&e(5)); // ·col(term7)
        dyn_term.mul_assign(&perm[0]); // ·chal(ADDR_LOW)
        let mut off_term = e(4);
        off_term.mul_assign(&perm[0]);
        let mut acc = dyn_term;
        acc.add_assign(&off_term);
        assert_eq!(got, vec![acc]);
        assert_eq!(acc, e(98));
    }
}
