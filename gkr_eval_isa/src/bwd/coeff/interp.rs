//! Scalar interpreters for the coefficient ISA (design §4, §9).
//!
//! Two of them, over one [`CoeffResolver`]:
//!
//!   * [`interpret_coeff_layer`] — the SEMANTIC reference. One row in,
//!     `(acc_c0, acc_c2)` out. There is no `T0`/`T2` role, no generic arithmetic
//!     accumulator, and no `acc_c1`: the round update recovers `c1` from the
//!     normalized claim. It deliberately knows nothing about cells, moves, paging,
//!     or the wire encoding.
//!   * [`interpret_encoded_program`] — the ENCODED interpreter. It decodes the
//!     §9.1 word stream in exact word order, runs a real cell file, and resolves
//!     the §8 typed value uses through the SAME resolver. §12.4's gate is that the
//!     two produce identical `(acc_c0, acc_c2)`.
//!
//! The cell file is modelled per BF lane and typed: a resident read must find a
//! value of the width its opcode assigns, at the lane it names. A misaligned E4
//! lane, a stale lane, or a BF/E4 width confusion is therefore an error and not a
//! silently wrong number.

use cs::gkr_compiler::dag_ir::Ext;
use field::Field;

use super::bind::CoeffSourceBinding;
use super::encode::{
    CoeffCodecError, DecodedCell, DecodedInstr, DecodedUse, EncodedProgram, OperandRole,
    SourceCoord, category_arity, category_role, coord_source, decode_program, move_width,
    operand_width,
};
use super::model::{
    CoeffError, CoeffLayer, CoeffTerm, CoefficientRecipeId, Projection, ProjectionId, SourceId,
    TermId,
};
use super::place::PlanAction;
use super::schedule::{LANES_PER_CELL, ValueWidth};

/// The two values a coefficient program needs from its environment.
///
/// [`CoeffResolver::coefficient`] is only ever called for a BANKED id: reserved
/// literals (`+1`/`-1`) are resolved by the interpreter itself, so an
/// implementation never has to allocate an evaluated bank entry for them.
///
/// [`CoeffResolver::source_pair`] returns the source's two named projections at
/// `row`, in that order: `(Endpoint0, Delta) = (s0, s1 - s0)`. It is a PAIR
/// because a native dual factor performs one physical source-pair resolution, not
/// two projection reads (§8).
pub trait CoeffResolver {
    fn coefficient(&self, id: CoefficientRecipeId) -> Ext;
    fn source_pair(&self, id: SourceId, row: usize) -> (Ext, Ext);
}

/// Interpret one row of `layer`, returning `(acc_c0, acc_c2)`.
///
/// `acc_c0` starts at the per-thread `c_init` initializer (or zero when the layer
/// has none) and `acc_c2` at zero; every term then adds its own contribution:
///
/// ```text
/// C0Linear(k, a0)        acc_c0 += k * a0
/// C2Product(k, da, db)   acc_c2 += k * da * db
/// DualProduct(k, A, B)   acc_c0 += k * A.s0 * B.s0 ; acc_c2 += k * A.ds * B.ds
/// ```
pub fn interpret_coeff_layer(
    layer: &CoeffLayer,
    row: usize,
    resolver: &impl CoeffResolver,
) -> Result<(Ext, Ext), CoeffError> {
    let mut acc_c0 = match layer.c_init {
        Some(id) => coefficient(layer, id, resolver)?,
        None => Ext::ZERO,
    };
    let mut acc_c2 = Ext::ZERO;

    for term in &layer.terms {
        let k = coefficient(layer, term.coefficient(), resolver)?;
        match term {
            CoeffTerm::C0Linear { id, value, .. } => {
                let (e0, _) = projection(layer, *id, *value, Projection::Endpoint0, row, resolver)?;
                let mut v = k;
                v.mul_assign(&e0);
                acc_c0.add_assign(&v);
            }
            CoeffTerm::C2Product { id, lhs, rhs, .. } => {
                let (_, dl) = projection(layer, *id, *lhs, Projection::Delta, row, resolver)?;
                let (_, dr) = projection(layer, *id, *rhs, Projection::Delta, row, resolver)?;
                let mut v = k;
                v.mul_assign(&dl);
                v.mul_assign(&dr);
                acc_c2.add_assign(&v);
            }
            CoeffTerm::DualProduct { lhs, rhs, .. } => {
                let (l0, ld) = source_pair(layer, *lhs, row, resolver)?;
                let (r0, rd) = source_pair(layer, *rhs, row, resolver)?;
                let mut c0 = k;
                c0.mul_assign(&l0);
                c0.mul_assign(&r0);
                acc_c0.add_assign(&c0);
                let mut c2 = k;
                c2.mul_assign(&ld);
                c2.mul_assign(&rd);
                acc_c2.add_assign(&c2);
            }
        }
    }
    Ok((acc_c0, acc_c2))
}

/// Reserved literals resolve internally (no bank entry, no resolver call); every
/// other id is validated against the bank before the resolver is asked. A banked
/// zero recipe is a compiler error, so it is rejected rather than evaluated.
fn coefficient(
    layer: &CoeffLayer,
    id: CoefficientRecipeId,
    resolver: &impl CoeffResolver,
) -> Result<Ext, CoeffError> {
    if let Some(v) = id.literal() {
        return Ok(v);
    }
    match layer.banked_recipe(id) {
        None => Err(CoeffError::UnknownCoefficient { id }),
        Some(r) if r.is_zero() => Err(CoeffError::EncodedZeroCoefficient { id }),
        Some(_) => Ok(resolver.coefficient(id)),
    }
}

fn source_pair(
    layer: &CoeffLayer,
    id: SourceId,
    row: usize,
    resolver: &impl CoeffResolver,
) -> Result<(Ext, Ext), CoeffError> {
    if layer.source(id).is_none() {
        return Err(CoeffError::UnknownSource { id });
    }
    Ok(resolver.source_pair(id, row))
}

/// Resolve a projection, rejecting a role its opcode cannot consume.
fn projection(
    layer: &CoeffLayer,
    term: TermId,
    p: ProjectionId,
    expected: Projection,
    row: usize,
    resolver: &impl CoeffResolver,
) -> Result<(Ext, Ext), CoeffError> {
    if p.projection != expected {
        return Err(CoeffError::ProjectionRoleMismatch { term, expected, found: p.projection });
    }
    source_pair(layer, p.source, row, resolver)
}

// ── The cell file ────────────────────────────────────────────────────────────

/// One BF lane of the cell file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CellSlot {
    /// Nothing live here.
    Empty,
    /// The FIRST lane of a resident value of `width`.
    Head { width: ValueWidth, value: Ext },
    /// A later lane of the value whose head is at `head`.
    Tail { head: u16 },
}

/// `4 * cells` BF lanes, typed: an E4 value owns four consecutive four-aligned
/// lanes and a BF value owns one.
struct CellFile {
    slots: Vec<CellSlot>,
}

impl CellFile {
    fn new(lanes: u32) -> Self {
        CellFile { slots: vec![CellSlot::Empty; lanes as usize] }
    }

    /// The lane range `lane` occupies at `width`, or `None` when it does not fit.
    fn range(&self, lane: u16, width: ValueWidth) -> Option<std::ops::Range<usize>> {
        let start = usize::from(lane);
        let end = start + width.lanes() as usize;
        (end <= self.slots.len() && (width == ValueWidth::Bf || start as u32 % LANES_PER_CELL == 0))
            .then_some(start..end)
    }

    /// Evict whatever value owns `lane`, whole.
    fn evict(&mut self, lane: usize) {
        let head = match self.slots[lane] {
            CellSlot::Empty => return,
            CellSlot::Head { .. } => lane,
            CellSlot::Tail { head } => usize::from(head),
        };
        let width = match self.slots[head] {
            CellSlot::Head { width, .. } => width.lanes() as usize,
            // A tail whose head is not a head cannot happen: `write` always sets
            // both, and `evict` always clears both.
            _ => 1,
        };
        for slot in head..(head + width).min(self.slots.len()) {
            self.slots[slot] = CellSlot::Empty;
        }
    }

    fn write(&mut self, lane: u16, width: ValueWidth, value: Ext) -> Result<(), CoeffCodecError> {
        let range = self
            .range(lane, width)
            .ok_or(CoeffCodecError::CellWidthMismatch { lane, expected: width })?;
        for slot in range.clone() {
            self.evict(slot);
        }
        self.slots[range.start] = CellSlot::Head { width, value };
        for slot in (range.start + 1)..range.end {
            self.slots[slot] = CellSlot::Tail { head: lane };
        }
        Ok(())
    }

    fn read(&self, lane: u16, width: ValueWidth) -> Result<Ext, CoeffCodecError> {
        if self.range(lane, width).is_none() {
            return Err(CoeffCodecError::CellWidthMismatch { lane, expected: width });
        }
        match self.slots[usize::from(lane)] {
            CellSlot::Head { width: found, value } if found == width => Ok(value),
            CellSlot::Head { .. } => Err(CoeffCodecError::CellWidthMismatch { lane, expected: width }),
            CellSlot::Empty | CellSlot::Tail { .. } => {
                Err(CoeffCodecError::CellNotResident { lane })
            }
        }
    }
}

// ── The encoded interpreter ──────────────────────────────────────────────────

/// The two projection values one operand slot produced. Only the parts its
/// [`OperandRole`] consumes are meaningful.
#[derive(Clone, Copy, Debug)]
struct Resolved {
    endpoint0: Ext,
    delta: Ext,
}

/// Interpret one row of an ENCODED program, returning `(acc_c0, acc_c2)`.
///
/// The stream is decoded in exact word order (§9.1) and every value use is
/// resolved exactly as §8 specifies: a resident read materializes nothing, a fill
/// consumes the just-resolved register value, and a plan reads its resident lanes
/// BEFORE it writes its fills — which is what lets a delta overwrite the endpoint
/// lane it was computed from.
pub fn interpret_encoded_program(
    program: &EncodedProgram,
    binding: &CoeffSourceBinding,
    row: usize,
    resolver: &impl CoeffResolver,
) -> Result<(Ext, Ext), CoeffCodecError> {
    let instrs = decode_program(program, binding)?;
    let mut acc_c0 = match program.c_init {
        Some(id) => encoded_coefficient(id, resolver),
        None => Ext::ZERO,
    };
    let mut acc_c2 = Ext::ZERO;
    let mut cells = CellFile::new(program.lanes());

    for instr in &instrs {
        match instr {
            DecodedInstr::Move { category, from_lane, to_lane } => {
                let width =
                    move_width(*category).expect("`decode_program` only emits move categories");
                let value = cells.read(*from_lane, width)?;
                cells.write(*to_lane, width, value)?;
            }
            DecodedInstr::Term { category, coefficient, uses } => {
                let k = encoded_coefficient(*coefficient, resolver);
                let role =
                    category_role(*category).expect("`decode_program` only emits term categories");
                let arity = category_arity(*category);
                let mut resolved = Vec::with_capacity(uses.len());
                for (position, use_) in uses.iter().enumerate() {
                    let width = operand_width(*category, position)
                        .expect("`decode_program` bounds the position by the opcode's arity");
                    resolved.push(resolve_use(
                        use_, role, width, binding, row, resolver, &mut cells,
                    )?);
                }
                // A squared term's single resolution feeds both operand positions
                // (§9.1 arity, `encode` module doc).
                let operand = |position: usize| resolved[position.min(resolved.len() - 1)];
                match role {
                    OperandRole::Endpoint0 => {
                        let mut v = k;
                        v.mul_assign(&operand(0).endpoint0);
                        acc_c0.add_assign(&v);
                    }
                    OperandRole::Delta => {
                        let mut v = k;
                        v.mul_assign(&operand(0).delta);
                        v.mul_assign(&operand(arity - 1).delta);
                        acc_c2.add_assign(&v);
                    }
                    OperandRole::Pair => {
                        let (lhs, rhs) = (operand(0), operand(arity - 1));
                        let mut c0 = k;
                        c0.mul_assign(&lhs.endpoint0);
                        c0.mul_assign(&rhs.endpoint0);
                        acc_c0.add_assign(&c0);
                        let mut c2 = k;
                        c2.mul_assign(&lhs.delta);
                        c2.mul_assign(&rhs.delta);
                        acc_c2.add_assign(&c2);
                    }
                }
            }
        }
    }
    Ok((acc_c0, acc_c2))
}

/// A reserved literal resolves internally; every other id goes to the resolver —
/// the same split [`interpret_coeff_layer`] makes, so the two agree by
/// construction.
fn encoded_coefficient(id: CoefficientRecipeId, resolver: &impl CoeffResolver) -> Ext {
    id.literal().unwrap_or_else(|| resolver.coefficient(id))
}

/// `decode_program` already proved every coordinate resolves against this exact
/// binding, so the lookup cannot miss.
fn resolve_source(
    coord: SourceCoord,
    binding: &CoeffSourceBinding,
    row: usize,
    resolver: &impl CoeffResolver,
) -> (Ext, Ext) {
    let source = coord_source(binding, coord).expect("`decode_program` bound this coordinate");
    resolver.source_pair(source, row)
}

fn resolve_use(
    use_: &DecodedUse,
    role: OperandRole,
    width: ValueWidth,
    binding: &CoeffSourceBinding,
    row: usize,
    resolver: &impl CoeffResolver,
    cells: &mut CellFile,
) -> Result<Resolved, CoeffCodecError> {
    match *use_ {
        DecodedUse::Direct { coord } => {
            let (s0, ds) = resolve_source(coord, binding, row, resolver);
            Ok(Resolved { endpoint0: s0, delta: ds })
        }
        DecodedUse::Cell(DecodedCell::Single { lane }) => {
            let value = cells.read(lane, width)?;
            // The single form carries the ROLE's projection, whichever it is.
            Ok(match role {
                OperandRole::Endpoint0 => Resolved { endpoint0: value, delta: Ext::ZERO },
                _ => Resolved { endpoint0: Ext::ZERO, delta: value },
            })
        }
        DecodedUse::Cell(DecodedCell::Pair { endpoint0_lane, delta_lane }) => Ok(Resolved {
            endpoint0: cells.read(endpoint0_lane, width)?,
            delta: cells.read(delta_lane, width)?,
        }),
        DecodedUse::Fill { coord, dst_lane } => {
            let (s0, ds) = resolve_source(coord, binding, row, resolver);
            // §8: the fill consumes the resolved register value; the requested
            // projection is the one the role names.
            let retained = match role {
                OperandRole::Endpoint0 => s0,
                _ => ds,
            };
            cells.write(dst_lane, width, retained)?;
            Ok(Resolved { endpoint0: s0, delta: ds })
        }
        DecodedUse::Planned { coord, endpoint0, delta } => {
            // Read phase.
            let resident_e0 = match endpoint0 {
                PlanAction::UseResident { lane } => Some((lane, cells.read(lane, width)?)),
                _ => None,
            };
            let resident_delta = match delta {
                PlanAction::UseResident { lane } => Some(cells.read(lane, width)?),
                _ => None,
            };
            let needs_source = resident_e0.is_none() || resident_delta.is_none();
            let resolved =
                needs_source.then(|| resolve_source(coord, binding, row, resolver));
            let s0 = match (resident_e0, resolved) {
                (Some((lane, value)), Some((source_s0, _))) => {
                    // §12.2: the lane holds the projection the plan claims.
                    if value != source_s0 {
                        return Err(CoeffCodecError::ResidentValueMismatch { lane });
                    }
                    value
                }
                (Some((_, value)), None) => value,
                (None, Some((source_s0, _))) => source_s0,
                (None, None) => Ext::ZERO,
            };
            let ds = match (resident_delta, resolved) {
                (Some(value), _) => value,
                (None, Some((_, source_ds))) => source_ds,
                (None, None) => Ext::ZERO,
            };
            // Write phase, strictly after every resident read.
            if let PlanAction::Fill { lane } = endpoint0 {
                cells.write(lane, width, s0)?;
            }
            if let PlanAction::Fill { lane } = delta {
                cells.write(lane, width, ds)?;
            }
            Ok(Resolved { endpoint0: s0, delta: ds })
        }
    }
}
