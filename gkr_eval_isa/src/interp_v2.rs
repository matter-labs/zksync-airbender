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
    ArithOp, Dst, Header, IndirectKind, LdcSub, Operand, Program2, RoutineId, SPECIAL_NEG_ONE,
    SPECIAL_ONE, SPECIAL_ZERO,
};
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
    pub gather_tables: GatherTables,
    /// Current row index (the gather mapping `gid`).
    pub gid: usize,
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

        let acc = match ins.header {
            Header::Arith { op, .. } => match op {
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
            },
            Header::Macro { routine, .. } => {
                exec_macro(routine_from_u8(routine), ins, src, &read)
            }
        };

        // Footer: write each dst. Arith has one; multi-output macros (num/den)
        // write the same accumulator placeholder per dst until Task 3.3 wires
        // their distinct outputs. GateOutputFold is single-output.
        for dst in &ins.dsts {
            match *dst {
                Dst::Slot { e4, cell } => write_cells(&mut cells, cell as u16, e4, acc),
                Dst::Materialize { slot, col } => {
                    let field_ext = src.matrix[slot as usize].field_ext;
                    assert_store_width(field_ext, acc);
                    materialized.push(((slot, col), acc));
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

/// Dispatch one macro routine. Task 3.1 implements `GateOutputFold`; the rest
/// are `todo!("Task 3.3")`. The smoke-test path only reaches GateOutputFold, so
/// no panic fires there.
fn exec_macro(
    routine: RoutineId,
    ins: &crate::isa_v2::Instr2,
    src: &SourceBanks,
    read: &dyn Fn(&Operand) -> Ext,
) -> Ext {
    match routine {
        RoutineId::GateOutputFold => gate_output_fold(ins, src, read),
        RoutineId::LookupNumDen
        | RoutineId::GrandProductStep
        | RoutineId::AggregateLookupPair
        | RoutineId::SingleColumnLookup
        | RoutineId::MemoryTuple
        | RoutineId::VectorizedLookup
        | RoutineId::VectorizedLookupSetup
        | RoutineId::ProductStep
        | RoutineId::MemoryInitTeardownPair => {
            todo!("Task 3.3: macro routine {routine:?} not yet implemented")
        }
    }
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
        1 => RoutineId::LookupNumDen,
        2 => RoutineId::GrandProductStep,
        3 => RoutineId::AggregateLookupPair,
        4 => RoutineId::SingleColumnLookup,
        5 => RoutineId::MemoryTuple,
        6 => RoutineId::VectorizedLookup,
        7 => RoutineId::VectorizedLookupSetup,
        8 => RoutineId::ProductStep,
        9 => RoutineId::MemoryInitTeardownPair,
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
}
