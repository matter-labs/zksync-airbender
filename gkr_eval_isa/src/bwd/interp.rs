//! Golden backward-eval interpreter (spec §2, Task 6). Executes a
//! [`BwdCompiledLayer`] for ONE logical row of the round's representation, at
//! one finite evaluation point ([`Role`]), returning the accumulated root value.
//!
//! # Role transform (the resolver boundary)
//!
//! Every SOURCE read — R0-regime `Global` backings AND Ext-regime `FoldSource`
//! specials — reads the pair `(2x, 2x+1)` of the PREVIOUS representation and
//! combines it per the evaluation point:
//!   * `T0 -> v(2x)` (point 0);
//!   * `T2 -> 2·v(2x+1) − v(2x)` (point 2 of the linear interpolant through
//!     `v(2x)` at 0 and `v(2x+1)` at 1).
//!
//! Row-independent operands (`Ldc` consts/challenges) are role-invariant by
//! construction (`2c − c = c`), so the transform is applied only where it can
//! differ — reads that take a row. Smem cells hold values already resolved
//! within THIS row's computation, so they are read straight.
//!
//! # FoldSource resolution ([`FoldState`] from per-run [`BwdBindings`])
//!
//! Per bound `state`, the pair element `v(y)` is:
//!   * `Materialized` → one resolver read of the previous-round buffer at `y`
//!     (the caller's resolver serves the folded buffer);
//!   * `LazyFromOriginals { depth }` → recompute `y` from `2^depth` originals,
//!     folded with `round_challenges[..depth]` (the caller's resolver serves
//!     originals).
//! The role combine is applied AFTER the element values are obtained, in both
//! cases.
//!
//! # Fold convention
//!
//! The sumcheck fold is `f_{k+1}(y) = f_k(2y) + r_k·(f_k(2y+1) − f_k(2y))`,
//! round `k` (0-indexed) using `round_challenges[k]`; round 0 is the innermost
//! (leaf-adjacent) combine, round `depth-1` the outermost. This matches the
//! prover's fold (`prover/.../access_and_fold/input_in_base.rs`:
//! `result = f0 + challenge·(f1 − f0)`); the role points `T0`/`T2` are
//! evaluations of that same linear interpolant, so fold and role are the one
//! convention. (The prover pairs low/high array halves; this instrument pins
//! adjacent `(2x, 2x+1)` pairs per the Task-6 interface — a self-consistent row
//! layout for the golden model.)

use super::compile::BwdCompiledLayer;
use super::distill::{BwdBindings, DistilledLayer};
use super::source::{BwdSpecial, FoldState, OriginLeaf};
use crate::fwd::error::InterpError;
use crate::fwd::interp::smem_lane;
use crate::fwd::isa::*;
use cs::gkr_compiler::dag_ir::{Bf, Ext, ReadPlace, Resolvers, VirtualSetupKind};
use field::{Field, FieldExtension, PrimeField};

#[inline]
fn lift(b: Bf) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(b)
}

/// The finite evaluation point a backward row is evaluated at: point 0 (`T0`)
/// or point 2 (`T2`) of the round's univariate over the folding variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    T0,
    T2,
}

/// Combine the pair `(a = v(2x), b = v(2x+1))` at the role's evaluation point:
/// `T0 -> a`; `T2 -> 2·b − a`.
///
/// Exposed so the value-parity oracle (`tests/bwd_value_parity.rs`) applies the
/// EXACT SAME role transform as the interpreter — the differential is
/// program-vs-expression, never transform-vs-transform.
#[inline]
pub fn role_combine(role: Role, a: Ext, b: Ext) -> Ext {
    match role {
        Role::T0 => a,
        Role::T2 => {
            let mut v = b;
            v.add_assign(&b); // 2·b
            v.sub_assign(&a); // 2·b − a
            v
        }
    }
}

/// The read primitive backing a `FoldSource`/`VirtualSetup` element: an origin
/// column (`r.read`) or a procedurally generated virtual setup (`r.virtual_setup`).
enum ReadPrim<'a> {
    Read(&'a ReadPlace),
    Vs(&'a VirtualSetupKind),
}

#[inline]
fn read_prim(p: &ReadPrim<'_>, y: usize, r: &Resolvers<'_>) -> Ext {
    match p {
        ReadPrim::Read(place) => r.read.read(place, y),
        ReadPrim::Vs(kind) => lift(r.virtual_setup.virtual_setup(kind, y)),
    }
}

/// The depth-`depth` sumcheck fold of the point function `base` at position
/// `y` from originals, using `ch[..depth]` (round 0 innermost, round
/// `depth-1` outermost): `fold(y) = fold(2y) + c·(fold(2y+1) − fold(2y))`.
///
/// Exposed so the value-parity oracle and its materialized-buffer resolver fold
/// with the EXACT SAME recurrence the interpreter uses (see [`role_combine`]).
pub fn sumcheck_fold_point(
    base: &dyn Fn(usize) -> Ext,
    y: usize,
    depth: u8,
    ch: &[Ext],
) -> Result<Ext, InterpError> {
    if depth == 0 {
        return Ok(base(y));
    }
    let c = ch
        .get(depth as usize - 1)
        .ok_or_else(|| InterpError::MalformedInstr("round_challenges shorter than fold depth".into()))?;
    let a = sumcheck_fold_point(base, 2 * y, depth - 1, ch)?;
    let b = sumcheck_fold_point(base, 2 * y + 1, depth - 1, ch)?;
    // a + c·(b − a)
    let mut d = b;
    d.sub_assign(&a);
    d.mul_assign(c);
    let mut out = a;
    out.add_assign(&d);
    Ok(out)
}

/// The depth-`depth` sumcheck fold of read primitive `p` at position `y`,
/// reading originals through `r`.
fn fold_prim(
    p: &ReadPrim<'_>,
    y: usize,
    depth: u8,
    ch: &[Ext],
    r: &Resolvers<'_>,
) -> Result<Ext, InterpError> {
    sumcheck_fold_point(&|z| read_prim(p, z, r), y, depth, ch)
}

/// The element value `v(y)` of a fold source under its bound `state`.
#[inline]
fn fold_element(
    p: &ReadPrim<'_>,
    state: FoldState,
    y: usize,
    ch: &[Ext],
    r: &Resolvers<'_>,
) -> Result<Ext, InterpError> {
    match state {
        FoldState::Materialized => Ok(read_prim(p, y, r)),
        FoldState::LazyFromOriginals { depth } => fold_prim(p, y, depth, ch, r),
    }
}

/// Resolve one operand of a backward instruction, applying the role transform
/// at every source read (`Global` backings and `Special` fold sources).
#[allow(clippy::too_many_arguments)]
fn resolve(
    o: &OperandLine,
    field: OperandField,
    cells: &[Ext],
    c: &BwdCompiledLayer,
    bindings: &BwdBindings,
    r: &Resolvers<'_>,
    role: Role,
    row: usize,
    round_challenges: &[Ext],
) -> Result<Ext, InterpError> {
    match *o {
        OperandLine::Global { slot, col } => {
            // R0-regime origin backing: role-combine the pair of the previous
            // representation directly (single read per element, no fold).
            let place = c
                .backings
                .slot_col_to_read_place(slot, col)
                .ok_or(InterpError::UnknownSlot(slot))?;
            let a = r.read.read(&place, 2 * row);
            let b = r.read.read(&place, 2 * row + 1);
            Ok(role_combine(role, a, b))
        }
        OperandLine::Smem { cell } => Ok(cells[smem_lane(cell, field)]),
        OperandLine::Ldc { sub, idx } => match sub {
            LdcSub::Const => Ok(lift(Bf::from_u32_with_reduction(
                c.consts.get(idx).ok_or(InterpError::UnknownConst(idx))?,
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
                let cr = c
                    .challenges
                    .get(sub, idx)
                    .ok_or(InterpError::UnknownChallenge(idx))?;
                Ok(r.challenge.challenge(cr))
            }
        },
        OperandLine::Special { desc } => {
            let spec = c.specials.get(desc).ok_or(InterpError::UnknownSpecial(desc))?;
            let state = *bindings
                .states
                .get(desc as usize)
                .ok_or_else(|| InterpError::MalformedInstr("desc has no binding".into()))?;
            let prim = match spec {
                BwdSpecial::FoldSource { origin } => match origin {
                    OriginLeaf::Read(place) => ReadPrim::Read(place),
                    OriginLeaf::VirtualSetup { kind } => ReadPrim::Vs(kind),
                },
                BwdSpecial::VirtualSetup { kind } => ReadPrim::Vs(kind),
            };
            let a = fold_element(&prim, state, 2 * row, round_challenges, r)?;
            let b = fold_element(&prim, state, 2 * row + 1, round_challenges, r)?;
            Ok(role_combine(role, a, b))
        }
    }
}

fn write_dst(dst: &DstLine, field: OperandField, v: Ext, cells: &mut Vec<Ext>) {
    match *dst {
        DstLine::Smem { cell } => {
            let lane = smem_lane(cell, field);
            if cells.len() <= lane {
                cells.resize(lane + 4, Ext::ZERO);
            }
            cells[lane] = v;
        }
        // Bwd programs never emit GlobalMaterialize (result-in-acc convention);
        // if one appears the program is malformed for the backward VM.
        DstLine::GlobalMaterialize { .. } => {}
    }
}

/// Interpret one backward row of `c` at evaluation point `role`, returning the
/// distilled root's accumulated value (result-in-acc terminal convention).
///
/// `bindings` supplies the per-descriptor [`FoldState`] for this round/policy
/// (a signature extension over the Task-6 draft — REV2 moved `FoldState` out of
/// descriptors into per-run [`BwdBindings`], so it must be threaded in here).
/// `round_challenges` are the fold challenges `r_0, r_1, …` consulted by
/// `LazyFromOriginals` sources; `d` is the distilled layer the program was
/// compiled from (its `specials` mirror `c.specials`).
pub fn interpret_bwd_row(
    c: &BwdCompiledLayer,
    d: &DistilledLayer,
    bindings: &BwdBindings,
    r: &Resolvers<'_>,
    role: Role,
    row: usize,
    round_challenges: &[Ext],
) -> Result<Ext, InterpError> {
    debug_assert_eq!(
        bindings.states.len(),
        d.specials.len(),
        "bindings must be dense over the distilled descriptor table"
    );
    let mut acc = Ext::ZERO;
    let mut cells: Vec<Ext> = vec![Ext::ZERO; c.budget.max(4)];

    macro_rules! res {
        ($op:expr, $field:expr) => {
            resolve($op, $field, &cells, c, bindings, r, role, row, round_challenges)?
        };
    }

    for instr in &c.program.instrs {
        match instr {
            Instr::Mov { dir, field, dst, src } => match dir {
                MovDir::AccFromSrc => {
                    acc = res!(&src.unwrap(), *field);
                }
                MovDir::DstFromAcc => {
                    write_dst(&dst.unwrap(), *field, acc, &mut cells);
                }
                MovDir::DstFromSrc => {
                    let v = res!(&src.unwrap(), *field);
                    write_dst(&dst.unwrap(), *field, v, &mut cells);
                }
            },
            Instr::Add { field, sign, operands, .. } => {
                for o in operands {
                    let v = res!(o, *field);
                    match sign {
                        Sign::Plus => {
                            acc.add_assign(&v);
                        }
                        Sign::Minus => {
                            acc.sub_assign(&v);
                        }
                    }
                }
            }
            Instr::Mul { field, negate_acc, operands, .. } => {
                // Sign bit = negate acc FIRST (spec §1.2); zero operands = pure negation.
                if *negate_acc {
                    acc.negate();
                }
                for o in operands {
                    let v = res!(o, *field);
                    acc.mul_assign(&v);
                }
            }
            Instr::Fma { field_lhs, field_rhs, sign, pairs, .. } => {
                for (l, rhs) in pairs {
                    let mut prod = res!(l, *field_lhs);
                    prod.mul_assign(&res!(rhs, *field_rhs));
                    match sign {
                        Sign::Plus => {
                            acc.add_assign(&prod);
                        }
                        Sign::Minus => {
                            acc.sub_assign(&prod);
                        }
                    }
                }
            }
        }
    }
    Ok(acc)
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bwd::compile::compile_distilled;
    use crate::bwd::distill::{bind, distill};
    use crate::bwd::source::MaterializationPolicy;
    use cs::gkr_compiler::dag_ir::{
        eval_layer_root, BatchingOrder, ChallengeKey, ChallengePower, ChallengeRef, ClaimInfo,
        DagLayer, Expr, ExprId, FieldKind, LookupValueKind, ReadPlace, ReadResolver, RootGroup,
        RootId, RootOrigin, RootSlot, SinkInfo, SinkKind, SourceId, SourceInfo, SourceKind,
        VirtualSetupKind,
    };
    use cs::gkr_compiler::dag_ir::{
        BwdRegime, ChallengeResolver, LookupResolver, Root, VirtualSetupResolver,
    };
    use std::collections::{BTreeMap, HashMap};

    // ── Resolvers ─────────────────────────────────────────────────────────────

    /// Originals: `BaseLayerWitness{column}` -> lift(7·column + row + 1).
    struct WitnessRead;
    impl ReadResolver for WitnessRead {
        fn read(&self, place: &ReadPlace, row: usize) -> Ext {
            match place {
                ReadPlace::BaseLayerWitness { column } => {
                    lift(Bf::from_u32_with_reduction(7 * *column as u32 + row as u32 + 1))
                }
                other => panic!("unexpected read place {other:?}"),
            }
        }
    }

    /// Previous-round buffer that IS the depth-1 fold of `WitnessRead`:
    /// buffer(y) = O(2y) + r0·(O(2y+1) − O(2y)).
    struct BufferRead {
        r0: Ext,
    }
    impl ReadResolver for BufferRead {
        fn read(&self, place: &ReadPlace, y: usize) -> Ext {
            let o = WitnessRead;
            let a = o.read(place, 2 * y);
            let b = o.read(place, 2 * y + 1);
            let mut d = b;
            d.sub_assign(&a);
            d.mul_assign(&self.r0);
            let mut out = a;
            out.add_assign(&d);
            out
        }
    }

    /// Role-wrapped reads: read(place, x) = role_combine(base(2x), base(2x+1)).
    /// The independent oracle for the role transform at the resolver boundary.
    struct RoleRead<'a> {
        base: &'a dyn ReadResolver,
        role: Role,
    }
    impl ReadResolver for RoleRead<'_> {
        fn read(&self, place: &ReadPlace, x: usize) -> Ext {
            role_combine(self.role, self.base.read(place, 2 * x), self.base.read(place, 2 * x + 1))
        }
    }

    struct ZeroLookup;
    impl LookupResolver for ZeroLookup {
        fn lookup(&self, _: &LookupValueKind, _: usize, _: Ext, _: usize) -> Bf {
            Bf::ZERO
        }
    }
    struct ZeroVs;
    impl VirtualSetupResolver for ZeroVs {
        fn virtual_setup(&self, _: &VirtualSetupKind, _: usize) -> Bf {
            Bf::ZERO
        }
    }
    /// ClaimBatching powers of a fixed beta; any other key panics.
    struct BetaChallenge(Ext);
    impl ChallengeResolver for BetaChallenge {
        fn challenge(&self, r: &ChallengeRef) -> Ext {
            assert_eq!(r.key, ChallengeKey::ClaimBatching, "unexpected challenge {r:?}");
            match r.power {
                ChallengePower::One => self.0,
                ChallengePower::Static(i) => pow(self.0, i),
            }
        }
    }

    fn resolvers<'a>(read: &'a dyn ReadResolver, ch: &'a BetaChallenge) -> Resolvers<'a> {
        static LOOKUP: ZeroLookup = ZeroLookup;
        static VS: ZeroVs = ZeroVs;
        Resolvers { read, lookup: &LOOKUP, virtual_setup: &VS, challenge: ch }
    }

    fn pow(base: Ext, n: u32) -> Ext {
        let mut acc = Ext::ONE;
        for _ in 0..n {
            acc.mul_assign(&base);
        }
        acc
    }

    // ── Layer helpers ─────────────────────────────────────────────────────────

    fn read_src(column: usize) -> SourceInfo {
        SourceInfo { kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column } } }
    }

    fn claim_only_root(expr: ExprId, relation_index: usize) -> Root {
        Root {
            expr,
            materialize: None,
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index,
                    slot: RootSlot::Constraint(0),
                },
            }),
        }
    }

    fn claim_root(expr: ExprId, relation_index: usize) -> Root {
        Root {
            expr,
            materialize: Some(SinkInfo {
                kind: SinkKind::Inner { layer: 1, offset: relation_index },
                field: FieldKind::Ext,
            }),
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index,
                    slot: RootSlot::Output(0),
                },
            }),
        }
    }

    fn layer(sources: Vec<SourceInfo>, exprs: Vec<Expr>, roots: Vec<Root>) -> DagLayer {
        let batching = BatchingOrder {
            roots: roots
                .iter()
                .enumerate()
                .filter(|(_, r)| r.claim.is_some())
                .map(|(i, _)| RootId(i as u32))
                .collect(),
        };
        DagLayer { sources, exprs, roots, batching, resolutions: BTreeMap::new() }
    }

    /// Single bare-Read-leaf claim-only root.
    fn bare_read_layer() -> DagLayer {
        layer(
            vec![read_src(0)],
            vec![Expr::Source(SourceId(0))],
            vec![claim_only_root(ExprId(0), 0)],
        )
    }

    // (a) ── role math on a single-Read root, bit-exact ────────────────────────

    #[test]
    fn role_math_matches_direct_resolver_reads() {
        let l = bare_read_layer();
        let read = WitnessRead;
        let ch = BetaChallenge(Ext::ZERO);
        let r = resolvers(&read, &ch);
        let place = ReadPlace::BaseLayerWitness { column: 0 };

        // R0: leaf stays a Global backing.
        let d = distill(&l, BwdRegime::R0, &HashMap::new(), None);
        let c = compile_distilled(&d, 16, None).expect("R0 compile");
        let b = bind(&d, MaterializationPolicy::AlwaysMaterialize, 0);

        // Ext: leaf becomes a FoldSource; round 0 binds LazyFromOriginals{0} =
        // one read per element = identical role math.
        let de = distill(&l, BwdRegime::Ext, &HashMap::new(), None);
        let ce = compile_distilled(&de, 16, None).expect("Ext compile");
        let be = bind(&de, MaterializationPolicy::AlwaysMaterialize, 0);

        for x in 0..5 {
            let v_even = read.read(&place, 2 * x);
            let v_odd = read.read(&place, 2 * x + 1);

            let t0 = interpret_bwd_row(&c, &d, &b, &r, Role::T0, x, &[]).unwrap();
            assert_eq!(t0, v_even, "R0/T0 must equal v(2x) at row {x}");

            let mut expected_t2 = v_odd;
            expected_t2.add_assign(&v_odd);
            expected_t2.sub_assign(&v_even);
            let t2 = interpret_bwd_row(&c, &d, &b, &r, Role::T2, x, &[]).unwrap();
            assert_eq!(t2, expected_t2, "R0/T2 must equal 2·v(2x+1)−v(2x) at row {x}");

            // Ext round-0 fold source gives the same finite-point values.
            let t0e = interpret_bwd_row(&ce, &de, &be, &r, Role::T0, x, &[]).unwrap();
            let t2e = interpret_bwd_row(&ce, &de, &be, &r, Role::T2, x, &[]).unwrap();
            assert_eq!(t0e, v_even, "Ext round-0 FoldSource T0 mismatch at row {x}");
            assert_eq!(t2e, expected_t2, "Ext round-0 FoldSource T2 mismatch at row {x}");
        }
    }

    // (b) ── lazy-from-originals == materialized-buffer ─────────────────────────

    #[test]
    fn lazy_from_originals_equals_materialized_buffer() {
        let l = bare_read_layer();
        let d = distill(&l, BwdRegime::Ext, &HashMap::new(), None);
        let c = compile_distilled(&d, 16, None).expect("Ext compile");

        let r0 = lift(Bf::from_u32_with_reduction(13));

        // Lazy run: resolver serves ORIGINALS, state = depth-1 recompute.
        let orig = WitnessRead;
        let chl = BetaChallenge(Ext::ZERO);
        let r_orig = resolvers(&orig, &chl);
        let lazy_b = bind(&d, MaterializationPolicy::LazyUpTo(1), 1);
        assert!(lazy_b.states.iter().all(|s| *s == FoldState::LazyFromOriginals { depth: 1 }));

        // Materialized run: resolver serves the depth-1 BUFFER, state = Materialized.
        let buf = BufferRead { r0 };
        let chm = BetaChallenge(Ext::ZERO);
        let r_buf = resolvers(&buf, &chm);
        let mat_b = bind(&d, MaterializationPolicy::AlwaysMaterialize, 3);
        assert!(mat_b.states.iter().all(|s| *s == FoldState::Materialized));

        for role in [Role::T0, Role::T2] {
            for x in 0..5 {
                let lazy = interpret_bwd_row(&c, &d, &lazy_b, &r_orig, role, x, &[r0]).unwrap();
                let mat = interpret_bwd_row(&c, &d, &mat_b, &r_buf, role, x, &[r0]).unwrap();
                assert_eq!(lazy, mat, "lazy vs materialized mismatch role {role:?} row {x}");
            }
        }
    }

    // ── depth-2 fold matches the hand-rolled recurrence (challenge ordering) ──

    #[test]
    fn depth2_fold_matches_recurrence() {
        let l = bare_read_layer();
        let d = distill(&l, BwdRegime::Ext, &HashMap::new(), None);
        let c = compile_distilled(&d, 16, None).expect("Ext compile");
        let read = WitnessRead;
        let ch = BetaChallenge(Ext::ZERO);
        let r = resolvers(&read, &ch);
        let place = ReadPlace::BaseLayerWitness { column: 0 };
        let r0 = lift(Bf::from_u32_with_reduction(3));
        let r1 = lift(Bf::from_u32_with_reduction(5));

        // f2(y) = combine_{r1}( combine_{r0}(O(4y),O(4y+1)), combine_{r0}(O(4y+2),O(4y+3)) )
        let f1 = |base: usize| {
            let mut d = read.read(&place, base + 1);
            d.sub_assign(&read.read(&place, base));
            d.mul_assign(&r0);
            let mut out = read.read(&place, base);
            out.add_assign(&d);
            out
        };
        let f2 = |y: usize| {
            let a = f1(4 * y);
            let b = f1(4 * y + 2);
            let mut d = b;
            d.sub_assign(&a);
            d.mul_assign(&r1);
            let mut out = a;
            out.add_assign(&d);
            out
        };

        let b2 = bind(&d, MaterializationPolicy::LazyUpTo(2), 2);
        assert!(b2.states.iter().all(|s| *s == FoldState::LazyFromOriginals { depth: 2 }));
        for x in 0..4 {
            let got = interpret_bwd_row(&c, &d, &b2, &r, Role::T0, x, &[r0, r1]).unwrap();
            assert_eq!(got, f2(2 * x), "depth-2 T0 fold mismatch at row {x}");

            let got2 = interpret_bwd_row(&c, &d, &b2, &r, Role::T2, x, &[r0, r1]).unwrap();
            let mut exp = f2(2 * x + 1);
            exp.add_assign(&f2(2 * x + 1));
            exp.sub_assign(&f2(2 * x));
            assert_eq!(got2, exp, "depth-2 T2 fold mismatch at row {x}");
        }
    }

    // (c) ── alpha-spine end-to-end vs eval_layer_root per root ─────────────────

    /// Three claim roots over shared Read leaves (products make the per-leaf role
    /// transform observable):  r0 = w0+w1,  r1 = w0*w2,  r2 = w1+w2.
    fn three_root_layer() -> DagLayer {
        DagLayer {
            sources: vec![read_src(0), read_src(1), read_src(2)],
            exprs: vec![
                Expr::Source(SourceId(0)),             // 0 = w0
                Expr::Source(SourceId(1)),             // 1 = w1
                Expr::Source(SourceId(2)),             // 2 = w2
                Expr::Add(vec![ExprId(0), ExprId(1)]), // 3 = w0 + w1
                Expr::Mul(vec![ExprId(0), ExprId(2)]), // 4 = w0 * w2
                Expr::Add(vec![ExprId(1), ExprId(2)]), // 5 = w1 + w2
            ],
            roots: vec![
                claim_root(ExprId(3), 0),
                claim_root(ExprId(4), 1),
                claim_only_root(ExprId(5), 2),
            ],
            batching: BatchingOrder { roots: vec![RootId(0), RootId(1), RootId(2)] },
            resolutions: BTreeMap::new(),
        }
    }

    #[test]
    fn alpha_spine_end_to_end_matches_role_wrapped_eval() {
        let canonical = three_root_layer();
        let d = distill(&canonical, BwdRegime::R0, &HashMap::new(), None);
        let c = compile_distilled(&d, 16, None).expect("compile");
        let b = bind(&d, MaterializationPolicy::AlwaysMaterialize, 0);

        let beta = lift(Bf::from_u32_with_reduction(11));
        let base = WitnessRead;
        let ch = BetaChallenge(beta);
        let r = resolvers(&base, &ch);

        for role in [Role::T0, Role::T2] {
            // Independent oracle: dag_ir's evaluator over the CANONICAL layer with
            // role-wrapped reads, alpha-combined by hand (β^i per batching slot).
            let rrole = RoleRead { base: &base, role };
            let oracle = resolvers(&rrole, &ch);
            for x in 0..5 {
                let mut expected = eval_layer_root(&canonical, RootId(0), x, &oracle);
                let mut t1 = eval_layer_root(&canonical, RootId(1), x, &oracle);
                t1.mul_assign(&beta);
                expected.add_assign(&t1);
                let mut t2 = eval_layer_root(&canonical, RootId(2), x, &oracle);
                t2.mul_assign(&pow(beta, 2));
                expected.add_assign(&t2);

                let got = interpret_bwd_row(&c, &d, &b, &r, role, x, &[]).unwrap();
                assert_eq!(got, expected, "alpha spine role {role:?} mismatch at row {x}");
            }
        }
    }

    // ── unknown-descriptor / short-challenge error surfaces ─────────────────────

    #[test]
    fn short_round_challenges_is_malformed() {
        let l = bare_read_layer();
        let d = distill(&l, BwdRegime::Ext, &HashMap::new(), None);
        let c = compile_distilled(&d, 16, None).expect("Ext compile");
        let read = WitnessRead;
        let ch = BetaChallenge(Ext::ZERO);
        let r = resolvers(&read, &ch);
        // depth-2 fold but only one challenge supplied.
        let b = bind(&d, MaterializationPolicy::LazyUpTo(2), 2);
        let err = interpret_bwd_row(&c, &d, &b, &r, Role::T0, 0, &[Ext::ONE]).unwrap_err();
        assert!(matches!(err, InterpError::MalformedInstr(_)));
    }
}
