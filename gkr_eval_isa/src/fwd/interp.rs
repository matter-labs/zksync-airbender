//! CPU interpreter (spec §4–§6). Per-row, per-root outputs; reuses dag_ir resolvers.

use super::binding::BackingKey;
use super::context::{CompiledLayer, DagForwardContext, OutputCell, RootOutput, RowOutputs};
use super::error::InterpError;
use super::isa::*;
use cs::gkr_compiler::dag_ir::{
    eval_layer_expr, Bf, DagLayer, Ext, ReadPlace, Resolvers, VirtualSetupKind,
};
use field::{Field, FieldExtension, PrimeField};
use std::collections::HashMap;

#[inline]
fn lift(b: Bf) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(b)
}

/// How the interpreter resolves a `Special { desc }` operand.
enum SpecialMode<'p> {
    /// SP1: re-run the authoritative fold (circular; synthetic/debug only).
    Fold,
    /// SP2: read the real peek binding.
    Peek(&'p dyn crate::fwd::peek::PeekResolver),
}

pub fn interpret_layer_row(
    compiled: &CompiledLayer,
    layer: &DagLayer,
    r: &Resolvers<'_>,
    row: usize,
) -> Result<RowOutputs, InterpError> {
    interpret_layer_row_impl(compiled, layer, r, &SpecialMode::Fold, row)
}

pub fn interpret_layer_row_with_peeks(
    compiled: &CompiledLayer,
    layer: &DagLayer,
    r: &Resolvers<'_>,
    peek: &dyn crate::fwd::peek::PeekResolver,
    row: usize,
) -> Result<RowOutputs, InterpError> {
    interpret_layer_row_impl(compiled, layer, r, &SpecialMode::Peek(peek), row)
}

fn interpret_layer_row_impl(
    compiled: &CompiledLayer,
    layer: &DagLayer,
    r: &Resolvers<'_>,
    mode: &SpecialMode<'_>,
    row: usize,
) -> Result<RowOutputs, InterpError> {
    let ctx = &compiled.ctx;
    let mut acc = Ext::ZERO;
    let mut cells: Vec<Ext> = vec![Ext::ZERO; compiled.budget.max(4)];
    let mut globals: HashMap<(u8, u16), Ext> = HashMap::new();

    for instr in &compiled.program.instrs {
        match instr {
            Instr::Mov { dir, field: _, dst, src } => match dir {
                MovDir::AccFromSrc => {
                    acc = resolve(&src.unwrap(), &cells, &globals, ctx, r, row, layer, mode)?;
                }
                MovDir::DstFromAcc => {
                    write_dst(&dst.unwrap(), acc, &mut cells, &mut globals);
                }
                MovDir::DstFromSrc => {
                    let v = resolve(&src.unwrap(), &cells, &globals, ctx, r, row, layer, mode)?;
                    write_dst(&dst.unwrap(), v, &mut cells, &mut globals);
                }
            },
            Instr::Add { sign, operands, .. } => {
                for o in operands {
                    let v = resolve(o, &cells, &globals, ctx, r, row, layer, mode)?;
                    match sign {
                        Sign::Plus => { acc.add_assign(&v); }
                        Sign::Minus => { acc.sub_assign(&v); }
                    }
                }
            }
            Instr::Mul { operands, .. } => {
                // Unary MUL Special(NegOne) → negate acc (spec §4).
                if operands.len() == 1 {
                    if let OperandLine::Ldc { sub: LdcSub::Special, idx } = operands[0] {
                        if idx == Special::NegOne as u16 {
                            let mut n = Ext::ZERO;
                            n.sub_assign(&acc);
                            acc = n;
                            continue;
                        }
                    }
                }
                for o in operands {
                    let v = resolve(o, &cells, &globals, ctx, r, row, layer, mode)?;
                    acc.mul_assign(&v);
                }
            }
            Instr::Fma { sign, pairs, .. } => {
                for (l, rhs) in pairs {
                    let mut prod = resolve(l, &cells, &globals, ctx, r, row, layer, mode)?;
                    prod.mul_assign(&resolve(rhs, &cells, &globals, ctx, r, row, layer, mode)?);
                    match sign {
                        Sign::Plus => { acc.add_assign(&prod); }
                        Sign::Minus => { acc.sub_assign(&prod); }
                    }
                }
            }
        }
    }

    let mut by_root = HashMap::new();
    for (rid, out) in &compiled.root_outputs {
        let v = match out {
            RootOutput::Cell(OutputCell::Smem(c)) => cells[*c as usize],
            RootOutput::Cell(OutputCell::Global { slot, col }) => {
                globals[&(*slot, *col)]
            }
            // CopyAlias: resolved OUTSIDE the ISA stream (zero lanes).
            RootOutput::Alias(op) => {
                resolve(op, &cells, &globals, ctx, r, row, layer, mode)?
            }
        };
        by_root.insert(*rid, v);
    }
    Ok(RowOutputs { by_root })
}

// Free fn (not a closure): borrows `globals` immutably while the caller's loop
// mutates it via `write_dst`.
fn resolve(
    o: &OperandLine,
    cells: &[Ext],
    globals: &HashMap<(u8, u16), Ext>,
    ctx: &DagForwardContext,
    r: &Resolvers<'_>,
    row: usize,
    layer: &DagLayer,
    mode: &SpecialMode<'_>,
) -> Result<Ext, InterpError> {
    match *o {
        OperandLine::Global { slot, col } => {
            // VM materialized this backing this row (incl. Prior re-read of a cache).
            if let Some(v) = globals.get(&(slot, col)) {
                return Ok(*v);
            }
            let key = ctx.backings.backing(slot).ok_or(InterpError::UnknownSlot(slot))?;
            Ok(match key {
                BackingKey::VirtualSetup { kind } => {
                    lift(r.virtual_setup.virtual_setup(kind, row))
                }
                _ => r.read.read(&backing_to_read_place(key, col), row),
            })
        }
        OperandLine::Smem { cell } => Ok(cells[cell as usize]),
        OperandLine::Ldc { sub, idx } => match sub {
            LdcSub::Const => Ok(lift(Bf::from_u32_with_reduction(
                ctx.consts.get(idx).ok_or(InterpError::UnknownConst(idx))?,
            ))),
            LdcSub::Special => Ok(match idx {
                0 => Ext::ZERO,
                1 => Ext::ONE,
                2 => {
                    let mut z = Ext::ZERO;
                    z.sub_assign(&Ext::ONE);
                    z
                }
                _ => return Err(InterpError::MalformedInstr("special idx".into())),
            }),
            LdcSub::ConstChallenge | LdcSub::ArgChallenge => {
                let cr = ctx
                    .challenges
                    .get(sub, idx)
                    .ok_or(InterpError::UnknownChallenge(idx))?;
                Ok(r.challenge.challenge(cr))
            }
        },
        OperandLine::Special { desc } => {
            let d = ctx
                .specials
                .get(desc)
                .ok_or(InterpError::UnknownSpecial(desc))?;
            match mode {
                SpecialMode::Fold => Ok(eval_layer_expr(layer, d.origin_expr, row, r)),
                SpecialMode::Peek(p) => p.peek(d, row, r).map_err(InterpError::Peek),
            }
        }
    }
}

fn backing_to_read_place(key: &BackingKey, col: u16) -> ReadPlace {
    let c = col as usize;
    match key {
        BackingKey::BaseLayerMemory => ReadPlace::BaseLayerMemory { column: c },
        BackingKey::BaseLayerWitness => ReadPlace::BaseLayerWitness { column: c },
        BackingKey::Setup => ReadPlace::Setup { column: c },
        BackingKey::Scratch => ReadPlace::Scratch { slot: c },
        BackingKey::LayerOutput { layer } => ReadPlace::LayerOutput { layer: *layer, offset: c },
        BackingKey::CacheOutput { layer } => ReadPlace::CacheOutput { layer: *layer, offset: c },
        BackingKey::VirtualSetup { .. } => unreachable!("virtual setup handled before read"),
    }
}

fn write_dst(
    dst: &DstLine,
    v: Ext,
    cells: &mut Vec<Ext>,
    globals: &mut HashMap<(u8, u16), Ext>,
) {
    match *dst {
        DstLine::Smem { cell } => {
            if cells.len() <= cell as usize {
                cells.resize(cell as usize + 4, Ext::ZERO);
            }
            cells[cell as usize] = v;
        }
        DstLine::GlobalMaterialize { slot, col } => {
            globals.insert((slot, col), v);
        }
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fwd::binding::{BackingKey, BackingTable};
    use crate::fwd::context::{CompiledLayer, CompileTrace, DagForwardContext, OutputCell, RootOutput, RowOutputs};
    use crate::fwd::stats::CompileStats;
    use crate::fwd::error::InterpError;
    use crate::fwd::isa::*;
    use crate::fwd::source::{ConstBank, SpecialTable};
    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, ChallengeRef, DagLayer, Ext, ReadPlace, Resolvers, RootId,
        VirtualSetupKind,
    };
    use std::collections::BTreeMap;

    // ── Stub resolvers ───────────────────────────────────────────────────────

    /// Returns `lift(Bf::from_u32_with_reduction(col + row))`.
    struct ColPlusRowReadResolver;
    impl cs::gkr_compiler::dag_ir::ReadResolver for ColPlusRowReadResolver {
        fn read(&self, place: &ReadPlace, row: usize) -> Ext {
            let col = match *place {
                ReadPlace::BaseLayerMemory { column } => column,
                ReadPlace::BaseLayerWitness { column } => column,
                ReadPlace::Setup { column } => column,
                ReadPlace::Scratch { slot } => slot,
                ReadPlace::LayerOutput { offset, .. } => offset,
                ReadPlace::CacheOutput { offset, .. } => offset,
            };
            lift(Bf::from_u32_with_reduction(col as u32 + row as u32))
        }
    }

    struct ZeroLookupResolver;
    impl cs::gkr_compiler::dag_ir::LookupResolver for ZeroLookupResolver {
        fn lookup(
            &self,
            _kind: &cs::gkr_compiler::dag_ir::LookupValueKind,
            _set_index: usize,
            _evaluated_query: Ext,
            _row: usize,
        ) -> Bf {
            Bf::ZERO
        }
    }

    struct ZeroVirtualSetupResolver;
    impl cs::gkr_compiler::dag_ir::VirtualSetupResolver for ZeroVirtualSetupResolver {
        fn virtual_setup(&self, _kind: &VirtualSetupKind, _row: usize) -> Bf {
            Bf::ZERO
        }
    }

    struct FixedChallengeResolver(Ext);
    impl cs::gkr_compiler::dag_ir::ChallengeResolver for FixedChallengeResolver {
        fn challenge(&self, _r: &ChallengeRef) -> Ext {
            self.0
        }
    }

    // ── Helpers ──────────────────────────────────────────────────────────────

    fn empty_layer() -> DagLayer {
        DagLayer {
            sources: vec![],
            exprs: vec![],
            roots: vec![],
            batching: BatchingOrder { roots: vec![] },
            resolutions: BTreeMap::new(),
        }
    }

    fn make_resolvers<'a>(
        read: &'a dyn cs::gkr_compiler::dag_ir::ReadResolver,
        challenge: &'a dyn cs::gkr_compiler::dag_ir::ChallengeResolver,
    ) -> Resolvers<'a> {
        Resolvers {
            read,
            lookup: &ZeroLookupResolver,
            virtual_setup: &ZeroVirtualSetupResolver,
            challenge,
        }
    }

    /// Build a minimal `CompiledLayer` with a one-backing `BackingTable` (BaseLayerMemory),
    /// no consts/challenges/specials.
    fn minimal_compiled(program: Program, root_outputs: Vec<(RootId, RootOutput)>) -> CompiledLayer {
        let mut backings = BackingTable::default();
        backings.intern(BackingKey::BaseLayerMemory).unwrap();
        let ctx = DagForwardContext {
            specials: SpecialTable::default(),
            consts: ConstBank::default(),
            challenges: crate::fwd::source::ChallengeBanks::default(),
            backings,
            actions: std::collections::HashMap::new(),
            cache_loc: std::collections::HashMap::new(),
            cross_layer_fields: std::collections::HashMap::new(),
        };
        CompiledLayer {
            program,
            ctx,
            root_outputs,
            skipped: vec![],
            trace: CompileTrace::default(),
            budget: 4,
            stats: CompileStats::default(),
            resident_realized: vec![],
        }
    }

    // ── Test 1: MOV AccFromSrc + ADD sum ────────────────────────────────────

    /// Program: MOV acc ← Global{slot=0, col=3}; ADD Global{slot=0, col=5}
    /// Row = 2.
    /// read(col, row) = col + row.
    /// Expected acc = lift(3+2) + lift(5+2) = lift(5) + lift(7) = lift(12).
    #[test]
    fn mov_acc_from_src_then_add() {
        let program = Program {
            instrs: vec![
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Global { slot: 0, col: 3 }),
                },
                Instr::Add {
                    field: OperandField::Base,
                    sign: Sign::Plus,
                    operands: vec![OperandLine::Global { slot: 0, col: 5 }],
                },
            ],
        };
        let compiled = minimal_compiled(program, vec![]);
        let layer = empty_layer();
        let read = ColPlusRowReadResolver;
        let challenge = FixedChallengeResolver(Ext::ZERO);
        let r = make_resolvers(&read, &challenge);

        let out = interpret_layer_row(&compiled, &layer, &r, 2).unwrap();
        assert!(out.by_root.is_empty());

        // Verify via manual re-run: the interpreter consumes the program correctly.
        // Acc after program = lift(5) + lift(7) = lift(12).
        let expected = {
            let mut e = lift(Bf::from_u32_with_reduction(5));
            e.add_assign(&lift(Bf::from_u32_with_reduction(7)));
            e
        };
        // To observe acc we route it through a root output via Smem.
        let program2 = Program {
            instrs: vec![
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Global { slot: 0, col: 3 }),
                },
                Instr::Add {
                    field: OperandField::Base,
                    sign: Sign::Plus,
                    operands: vec![OperandLine::Global { slot: 0, col: 5 }],
                },
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: OperandField::Base,
                    dst: Some(DstLine::Smem { cell: 0 }),
                    src: None,
                },
            ],
        };
        let compiled2 = minimal_compiled(
            program2,
            vec![(RootId(0), RootOutput::Cell(OutputCell::Smem(0)))],
        );
        let out2 = interpret_layer_row(&compiled2, &layer, &r, 2).unwrap();
        assert_eq!(out2.by_root[&RootId(0)], expected, "MOV+ADD mismatch");
    }

    // ── Test 2: MUL product ─────────────────────────────────────────────────

    /// Program: MOV acc ← Global{col=2}; MUL Global{col=3}
    /// Row = 1. read = col+row.
    /// acc = lift(2+1) * lift(3+1) = lift(3) * lift(4) = lift(12).
    #[test]
    fn mul_product() {
        let program = Program {
            instrs: vec![
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Global { slot: 0, col: 2 }),
                },
                Instr::Mul {
                    field: OperandField::Base,
                    operands: vec![OperandLine::Global { slot: 0, col: 3 }],
                },
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: OperandField::Base,
                    dst: Some(DstLine::Smem { cell: 0 }),
                    src: None,
                },
            ],
        };
        let compiled = minimal_compiled(
            program,
            vec![(RootId(0), RootOutput::Cell(OutputCell::Smem(0)))],
        );
        let layer = empty_layer();
        let read = ColPlusRowReadResolver;
        let challenge = FixedChallengeResolver(Ext::ZERO);
        let r = make_resolvers(&read, &challenge);

        let out = interpret_layer_row(&compiled, &layer, &r, 1).unwrap();
        let mut expected = lift(Bf::from_u32_with_reduction(3)); // col 2 + row 1
        expected.mul_assign(&lift(Bf::from_u32_with_reduction(4))); // col 3 + row 1
        assert_eq!(out.by_root[&RootId(0)], expected, "MUL product mismatch");
    }

    // ── Test 3: FMA dot-product accumulation ────────────────────────────────

    /// Program: acc = 0 initially; FMA (col=1, col=2) + (col=3, col=4)
    /// Row = 0. read = col + row = col.
    /// acc = lift(1)*lift(2) + lift(3)*lift(4) = lift(2) + lift(12) = lift(14).
    #[test]
    fn fma_dot_product() {
        let program = Program {
            instrs: vec![
                Instr::Fma {
                    field_lhs: OperandField::Base,
                    field_rhs: OperandField::Base,
                    sign: Sign::Plus,
                    pairs: vec![
                        (OperandLine::Global { slot: 0, col: 1 }, OperandLine::Global { slot: 0, col: 2 }),
                        (OperandLine::Global { slot: 0, col: 3 }, OperandLine::Global { slot: 0, col: 4 }),
                    ],
                },
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: OperandField::Base,
                    dst: Some(DstLine::Smem { cell: 0 }),
                    src: None,
                },
            ],
        };
        let compiled = minimal_compiled(
            program,
            vec![(RootId(0), RootOutput::Cell(OutputCell::Smem(0)))],
        );
        let layer = empty_layer();
        let read = ColPlusRowReadResolver;
        let challenge = FixedChallengeResolver(Ext::ZERO);
        let r = make_resolvers(&read, &challenge);

        let out = interpret_layer_row(&compiled, &layer, &r, 0).unwrap();
        // 1*2 + 3*4 = 2 + 12 = 14
        let expected = lift(Bf::from_u32_with_reduction(14));
        assert_eq!(out.by_root[&RootId(0)], expected, "FMA dot-product mismatch");
    }

    // ── Test 4: unary MUL Special(NegOne) negates acc ───────────────────────

    /// Program: MOV acc ← Global{col=5}; MUL Ldc{Special, NegOne}
    /// Row = 0. read(col=5, row=0) = lift(5). After negate: lift(-5) = lift(P-5).
    #[test]
    fn unary_mul_negate() {
        let program = Program {
            instrs: vec![
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Global { slot: 0, col: 5 }),
                },
                Instr::Mul {
                    field: OperandField::Base,
                    operands: vec![OperandLine::Ldc {
                        sub: LdcSub::Special,
                        idx: Special::NegOne as u16,
                    }],
                },
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: OperandField::Base,
                    dst: Some(DstLine::Smem { cell: 0 }),
                    src: None,
                },
            ],
        };
        let compiled = minimal_compiled(
            program,
            vec![(RootId(0), RootOutput::Cell(OutputCell::Smem(0)))],
        );
        let layer = empty_layer();
        let read = ColPlusRowReadResolver;
        let challenge = FixedChallengeResolver(Ext::ZERO);
        let r = make_resolvers(&read, &challenge);

        let out = interpret_layer_row(&compiled, &layer, &r, 0).unwrap();
        // lift(5) negated = lift(P - 5)
        let mut expected = Ext::ZERO;
        expected.sub_assign(&lift(Bf::from_u32_with_reduction(5)));
        assert_eq!(out.by_root[&RootId(0)], expected, "negate mismatch");
    }

    // ── Test 5: base-acc + Ext-challenge ADD (mixed promote) ─────────────────

    /// Program: MOV acc ← Global{col=2}; ADD Ldc{ConstChallenge, idx=0}
    /// acc starts as lift(col=2, row=0) = lift(2).
    /// challenge returns alpha_val = lift(Bf(3)) i.e. [3,0,0,0].
    /// result = lift(2) + lift(3) = lift(5).
    #[test]
    fn base_acc_plus_ext_challenge_add() {
        // We need a challenge in the bank.
        use cs::gkr_compiler::dag_ir::{ChallengeKey, ChallengeRef, ChallengePower};
        let alpha_ref = ChallengeRef {
            key: ChallengeKey::LookupAdditive,
            power: ChallengePower::One,
        };
        let alpha_val = lift(Bf::from_u32_with_reduction(3));

        // Build compiled with alpha_ref in challenges bank.
        let mut backings = BackingTable::default();
        backings.intern(BackingKey::BaseLayerMemory).unwrap();
        let mut challenges = crate::fwd::source::ChallengeBanks::default();
        let (sub, idx) = challenges.intern(&alpha_ref);

        let ctx = DagForwardContext {
            specials: SpecialTable::default(),
            consts: ConstBank::default(),
            challenges,
            backings,
            actions: std::collections::HashMap::new(),
            cache_loc: std::collections::HashMap::new(),
            cross_layer_fields: std::collections::HashMap::new(),
        };

        let program = Program {
            instrs: vec![
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Global { slot: 0, col: 2 }),
                },
                Instr::Add {
                    field: OperandField::Ext,
                    sign: Sign::Plus,
                    operands: vec![OperandLine::Ldc { sub, idx }],
                },
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: OperandField::Ext,
                    dst: Some(DstLine::Smem { cell: 0 }),
                    src: None,
                },
            ],
        };
        let compiled = CompiledLayer {
            program,
            ctx,
            root_outputs: vec![(RootId(0), RootOutput::Cell(OutputCell::Smem(0)))],
            skipped: vec![],
            trace: CompileTrace::default(),
            budget: 4,
            stats: CompileStats::default(),
            resident_realized: vec![],
        };

        let layer = empty_layer();
        let read = ColPlusRowReadResolver;
        let challenge = FixedChallengeResolver(alpha_val);
        let r = make_resolvers(&read, &challenge);

        let out = interpret_layer_row(&compiled, &layer, &r, 0).unwrap();
        // lift(2) + lift(3) = lift(5)
        let expected = lift(Bf::from_u32_with_reduction(5));
        assert_eq!(out.by_root[&RootId(0)], expected, "mixed add mismatch");
    }

    // ── Test 6: DstFromAcc to Smem + read Smem back via GlobalMaterialize ───

    /// Program: MOV acc ← Global{col=7}; MOV Smem{0} ← acc; MOV acc ← Smem{0}; MOV GlobalMaterialize{slot=0,col=0} ← acc.
    /// Row = 0. read(7,0) = lift(7). GlobalMaterialize write; root reads from globals.
    #[test]
    fn smem_roundtrip_and_global_materialize() {
        let program = Program {
            instrs: vec![
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Global { slot: 0, col: 7 }),
                },
                // Write acc to Smem{0}
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: OperandField::Base,
                    dst: Some(DstLine::Smem { cell: 0 }),
                    src: None,
                },
                // Read Smem{0} back into acc (verify round-trip)
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Smem { cell: 0 }),
                },
                // Write acc to GlobalMaterialize{slot=0, col=0}
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: OperandField::Base,
                    dst: Some(DstLine::GlobalMaterialize { slot: 0, col: 0 }),
                    src: None,
                },
            ],
        };
        let compiled = minimal_compiled(
            program,
            vec![(RootId(0), RootOutput::Cell(OutputCell::Global { slot: 0, col: 0 }))],
        );
        let layer = empty_layer();
        let read = ColPlusRowReadResolver;
        let challenge = FixedChallengeResolver(Ext::ZERO);
        let r = make_resolvers(&read, &challenge);

        let out = interpret_layer_row(&compiled, &layer, &r, 0).unwrap();
        let expected = lift(Bf::from_u32_with_reduction(7));
        assert_eq!(out.by_root[&RootId(0)], expected, "smem roundtrip mismatch");
    }

    // ── Test 8: with_peeks uses PeekResolver for Special operands ────────────

    /// Build a CompiledLayer: program MOV acc ← Special{desc:0}; root 0 = Smem{0} (acc saved).
    /// The descriptor side-table has one entry (PeekSetup, origin_expr = ExprId(0)).
    fn compiled_mov_acc_from_special_desc0() -> (CompiledLayer, DagLayer) {
        use crate::fwd::source::{SpecialDescriptor, SpecialStrategy};
        use cs::gkr_compiler::dag_ir::ExprId;

        let mut specials = crate::fwd::source::SpecialTable::default();
        specials.push(SpecialDescriptor { strategy: SpecialStrategy::PeekSetup, origin_expr: ExprId(0) });

        let program = Program {
            instrs: vec![
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Special { desc: 0 }),
                },
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: OperandField::Base,
                    dst: Some(DstLine::Smem { cell: 0 }),
                    src: None,
                },
            ],
        };

        let mut backings = crate::fwd::binding::BackingTable::default();
        backings.intern(crate::fwd::binding::BackingKey::BaseLayerMemory).unwrap();
        let ctx = crate::fwd::context::DagForwardContext {
            specials,
            consts: crate::fwd::source::ConstBank::default(),
            challenges: crate::fwd::source::ChallengeBanks::default(),
            backings,
            actions: std::collections::HashMap::new(),
            cache_loc: std::collections::HashMap::new(),
            cross_layer_fields: std::collections::HashMap::new(),
        };
        let compiled = CompiledLayer {
            program,
            ctx,
            root_outputs: vec![(RootId(0), RootOutput::Cell(OutputCell::Smem(0)))],
            skipped: vec![],
            trace: CompileTrace::default(),
            budget: 4,
            stats: CompileStats::default(),
            resident_realized: vec![],
        };
        (compiled, empty_layer())
    }

    #[test]
    fn with_peeks_uses_peek_resolver_for_special_operand() {
        // A program: MOV acc <- Special{desc:0}; (acc is the root output).
        // SP1 interpret_layer_row would resolve via eval_layer_expr; with_peeks must use the peek.
        use crate::fwd::peek::{PeekError, PeekResolver};
        use crate::fwd::source::SpecialDescriptor;
        struct FixedPeek(Ext);
        impl PeekResolver for FixedPeek {
            fn peek(&self, _d: &SpecialDescriptor, _row: usize, _r: &Resolvers<'_>) -> Result<Ext, PeekError> {
                Ok(self.0)
            }
        }
        let (compiled, layer) = compiled_mov_acc_from_special_desc0();
        let read = ColPlusRowReadResolver;
        let challenge = FixedChallengeResolver(Ext::ZERO);
        let r = make_resolvers(&read, &challenge);
        let sentinel = lift(Bf::from_u32_with_reduction(123456 % ((1u64 << 31) as u32 - 1) as u32));
        let out = interpret_layer_row_with_peeks(&compiled, &layer, &r, &FixedPeek(sentinel), 0).unwrap();
        assert_eq!(*out.by_root.values().next().unwrap(), sentinel);
    }

    // ── Test 7: root_outputs mapping returns correct value in RowOutputs ─────

    /// Two compute roots: root 0 stored in Smem{0}, root 1 in Smem{1}.
    /// Row = 3. read(col, row) = col + row.
    #[test]
    fn root_outputs_mapping() {
        let program = Program {
            instrs: vec![
                // Root 0: acc = lift(10+3) = lift(13); store to Smem{0}
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Global { slot: 0, col: 10 }),
                },
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: OperandField::Base,
                    dst: Some(DstLine::Smem { cell: 0 }),
                    src: None,
                },
                // Root 1: acc = lift(20+3) = lift(23); store to Smem{1}
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Global { slot: 0, col: 20 }),
                },
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: OperandField::Base,
                    dst: Some(DstLine::Smem { cell: 1 }),
                    src: None,
                },
            ],
        };
        let compiled = minimal_compiled(
            program,
            vec![
                (RootId(0), RootOutput::Cell(OutputCell::Smem(0))),
                (RootId(1), RootOutput::Cell(OutputCell::Smem(1))),
            ],
        );
        let layer = empty_layer();
        let read = ColPlusRowReadResolver;
        let challenge = FixedChallengeResolver(Ext::ZERO);
        let r = make_resolvers(&read, &challenge);

        let out = interpret_layer_row(&compiled, &layer, &r, 3).unwrap();
        assert_eq!(out.by_root[&RootId(0)], lift(Bf::from_u32_with_reduction(13)), "root 0 mismatch");
        assert_eq!(out.by_root[&RootId(1)], lift(Bf::from_u32_with_reduction(23)), "root 1 mismatch");
    }
}
