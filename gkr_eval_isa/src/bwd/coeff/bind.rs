//! Final source binding for a coefficient schedule (design §9.4, §10, §12.3).
//!
//! The LAST compiler pass before encoding. It takes a placed program — whose
//! every value is still a [`SourceId`]/[`ProjectionId`] — and gives each
//! source-bearing input word its §9.4 coordinate:
//!
//! ```text
//! [ column:7 | source_window:6 | first_access:1 | mode:2 ]
//! ```
//!
//! Three rules make that coordinate meaningful, and all three live here:
//!
//!   1. **Windows are assigned only now.** A large logical backing is partitioned
//!      into freely based, dense windows of at most
//!      [`SOURCE_WINDOW_COLUMNS`](crate::source_bind::SOURCE_WINDOW_COLUMNS)
//!      contiguous columns, and a program uses at most
//!      [`MAX_SOURCE_WINDOWS`](crate::source_bind::MAX_SOURCE_WINDOWS) of them.
//!      Nothing earlier in the pipeline has a window: ordering, paging, placement
//!      and moves are decided in the source/projection vocabulary, so the
//!      partition is a pure function of the FINAL source set (§9.4).
//!   2. **One coordinate per PHYSICAL source resolution**, not per logical
//!      projection. A native dual factor resolves both projections through one
//!      input word; an `Endpoint0`/`Delta` plan resolves the pair through one
//!      input word; a resident [`ValueUse::Cell`] read resolves nothing at all and
//!      carries a lane, not a source (§9.4, §9.5, §12.3).
//!   3. **`first_access` is assigned dead last** (§10.3): after ordering, paging,
//!      placement, moves, native-dual formation, canonicalization and window
//!      partitioning. The first physical resolution of each source carries it. The
//!      bit is INERT when the round's target depth does not publish — inert, not
//!      absent: the marker is emitted either way, and `materialize` says which
//!      régime the program runs under.
//!
//! No semantics-changing pass may run after this one.
//!
//! The window partitioning and the marker itself are
//! [`crate::source_bind::bind_source_sequence`], the same core the forward
//! compiler's `Program` adapter runs; this module is the coefficient adapter
//! around it. What is deliberately NOT here: the u16 encoding (Task 7), the
//! descriptor's publish backing/stride (Task 9), and any peephole.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use cs::gkr_compiler::dag_ir::{FieldKind, ReadPlace};

use super::model::{CoeffLayer, SourceId};
use super::place::{CoeffPlacement, ScheduledInstr, ValueUse};
use super::schedule::PUBLISH_TARGET_DEPTH;
use super::stats::{WindowFamily, window_family};
use crate::source_bind::{self, BindFailure, LogicalSourceUse, bind_source_sequence};

// ── Output ───────────────────────────────────────────────────────────────────

/// One addressable column of one window.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoundColumn {
    /// The backing's OWN column, not the window-relative offset.
    pub column: usize,
    pub source: SourceId,
}

/// One bound source window: at most 128 contiguous columns of ONE logical
/// backing, of which only [`BoundSourceWindow::columns`] are addressable.
///
/// This is the static half of §10.2's source-window descriptor. The read backing
/// and its procedural kind are [`BoundSourceWindow::family`]; the origin field is
/// [`BoundSourceWindow::backing_field`]; the target depth and materialize flag are
/// layer-wide and live on [`CoeffSourceBinding`]. Strides and the publish backing
/// are device layout: they belong to Task 9's launch descriptor, not here — and
/// not to the artifact either, which §13 keeps free of physical pointers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundSourceWindow {
    pub family: WindowFamily,
    pub first_column: usize,
    /// Referenced columns, ascending, all in
    /// `[first_column, first_column + 128)`.
    pub columns: Vec<BoundColumn>,
}

impl BoundSourceWindow {
    /// The backing matrix's own field. Only a cross-layer output or cache can be
    /// `Ext`; base storage and procedural setup polynomials are base-valued.
    pub fn backing_field(&self) -> FieldKind {
        match self.family {
            WindowFamily::LayerOutput { ext, .. } | WindowFamily::CacheOutput { ext, .. } => {
                if ext { FieldKind::Ext } else { FieldKind::Base }
            }
            _ => FieldKind::Base,
        }
    }

    /// Whether the resolver evaluates this window's columns in closed form
    /// instead of reading DRAM (§9.6's procedural source kind).
    pub fn is_procedural(&self) -> bool {
        matches!(self.family, WindowFamily::VirtualSetup { .. })
    }
}

/// One source-bearing input word's bound coordinate, in exact execution order.
///
/// A [`ValueUse::Cell`] operand produces NO entry: it reads a resident lane and
/// resolves nothing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoundInput {
    /// Index into [`CoeffPlacement::instrs`].
    pub instr: u32,
    /// Operand slot within that term — the [`super::schedule::term_slots`] index.
    pub slot: u8,
    /// The source this word resolves. For a native dual factor or an
    /// `Endpoint0`/`Delta` plan, the ONE source of the whole pair resolution.
    pub source: SourceId,
    pub window: u8,
    /// Offset from the window's `first_column`, `< 128`.
    pub column: u8,
    pub first_access: bool,
}

/// A placed program's complete source binding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoeffSourceBinding {
    /// The fold depth this program is bound for.
    pub target_depth: u8,
    /// §10.2's static policy: publish on first physical access iff
    /// `target_depth >= PUBLISH_TARGET_DEPTH`. One constant, not a decision — when
    /// it is false every `first_access` bit is inert.
    pub materialize: bool,
    pub windows: Vec<BoundSourceWindow>,
    pub uses: Vec<BoundInput>,
}

impl CoeffSourceBinding {
    /// The source a bound coordinate names, or `None` for an unassigned column.
    pub fn resolve(&self, window: u8, column: u8) -> Option<SourceId> {
        let entry = self.windows.get(window as usize)?;
        let absolute = entry.first_column.checked_add(column as usize)?;
        entry
            .columns
            .binary_search_by_key(&absolute, |c| c.column)
            .ok()
            .map(|index| entry.columns[index].source)
    }
}

// ── Errors ───────────────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceBindError {
    /// The layout needs more than 64 windows (§9.4's `source_window:6`).
    WindowOverflow,
    /// A placed use names a source the layer's table does not have.
    UnknownSource { source: SourceId },
}

/// Everything §12.3 can reject.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceCertificateError {
    /// The bound sequence is not the placed program's own resolution sequence —
    /// i.e. something transformed the program after binding, or binding read a
    /// different program.
    SequenceMismatch { index: usize },
    /// A coordinate does not resolve back to the source it was bound for.
    CoordinateMismatch { index: usize, source: SourceId },
    /// A coordinate does not fit §9.4's six/seven-bit split.
    CoordinateOutOfRange { index: usize, window: u8, column: u8 },
    /// A resolved source's marked resolution is not its first, or it has none, or
    /// it has several.
    FirstAccessNotFirst { source: SourceId, marked: usize },
    /// The window layout is not dense, ascending, in-span or unmergeable.
    MalformedWindow { window: usize },
    /// A window's declared [`BoundSourceWindow::family`], or one of its column
    /// addresses, is not the one its own source resolves to.
    ///
    /// The family is not decoration: it is what selects DRAM versus procedural
    /// resolution ([`BoundSourceWindow::is_procedural`]) and the backing's own
    /// field width ([`BoundSourceWindow::backing_field`]). A window claiming the
    /// wrong family would still `resolve` to the right [`SourceId`] — the column
    /// table is keyed by column alone — so nothing else in the certificate can
    /// catch it.
    WindowFamilyMismatch { window: usize, column: usize, source: SourceId },
    /// `materialize` is not §10.2's static policy for `target_depth`.
    MaterializationNotPolicy { target_depth: u8, materialize: bool },
}

// ── Binding ──────────────────────────────────────────────────────────────────

/// The physical source resolution one operand slot performs, if any.
///
/// This is rule 2, and it is the whole semantic content of the task: the input
/// word's mode decides whether the word carries a SOURCE COORDINATE at all, and a
/// pair resolution — native dual or `Endpoint0`/`Delta` plan — carries exactly
/// one.
fn resolved_source(use_: &ValueUse) -> Option<SourceId> {
    match *use_ {
        ValueUse::Direct { source } => Some(source),
        ValueUse::Fill { projection, .. } => Some(projection.source),
        ValueUse::PlannedDelta { source, .. } => Some(source),
        // `Cell` carries a physical lane, never a source coordinate.
        ValueUse::Cell(_) => None,
    }
}

/// Every physical source resolution of a placed program, in execution order.
fn resolution_sequence(placement: &CoeffPlacement) -> Vec<(u32, u8, SourceId)> {
    let mut out = Vec::new();
    for (index, instr) in placement.instrs.iter().enumerate() {
        let ScheduledInstr::Term { uses, .. } = instr else {
            // A move relocates a value that is already resident; it resolves
            // nothing and carries no source coordinate (§9.6).
            continue;
        };
        for (slot, use_) in uses.iter().enumerate() {
            if let Some(source) = resolved_source(use_) {
                out.push((index as u32, slot as u8, source));
            }
        }
    }
    out
}

/// Bind one placed coefficient program's sources.
///
/// `cross_fields` is the circuit's cross-layer field map (a
/// [`DistilledLayer`](crate::bwd::distill::DistilledLayer)'s `cross_fields`): it
/// decides which homogeneous matrix a cross-layer output read belongs to, exactly
/// as it does for the Task 3 census.
pub fn bind_coeff_sources(
    layer: &CoeffLayer,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
    placement: &CoeffPlacement,
) -> Result<CoeffSourceBinding, SourceBindError> {
    let sequence = resolution_sequence(placement);

    // Where each source lives. Backings are indexed in `WindowFamily` order, and
    // the core numbers windows by ascending backing, so the window order is
    // deterministic and independent of the term order.
    let mut placed: Vec<(WindowFamily, usize)> = Vec::with_capacity(layer.sources.len());
    for source in &layer.sources {
        placed.push(window_family(source, cross_fields));
    }
    let backings: BTreeSet<WindowFamily> = sequence
        .iter()
        .map(|&(_, _, source)| {
            placed
                .get(source.0 as usize)
                .map(|&(family, _)| family)
                .ok_or(SourceBindError::UnknownSource { source })
        })
        .collect::<Result<_, _>>()?;
    // Every backing needs at least one window, so more backings than windows is
    // already an overflow — checked before the indices below, so the `u8` backing
    // index can never wrap silently.
    if backings.len() > source_bind::MAX_SOURCE_WINDOWS {
        return Err(SourceBindError::WindowOverflow);
    }
    let families: BTreeMap<WindowFamily, u8> = backings
        .into_iter()
        .enumerate()
        .map(|(index, family)| (family, index as u8))
        .collect();

    let uses: Vec<LogicalSourceUse> = sequence
        .iter()
        .map(|&(_, _, source)| {
            let (family, column) = placed[source.0 as usize];
            LogicalSourceUse {
                slot: families[&family],
                column,
                // A coefficient source's fold state is a property of the WINDOW
                // (§10.2's backing/target depth), never of a use, so there is no
                // per-column fold descriptor to agree on here.
                fold_desc: None,
            }
        })
        .collect();

    let binding = bind_source_sequence(&uses, true).map_err(|failure| match failure {
        BindFailure::WindowOverflow => SourceBindError::WindowOverflow,
        BindFailure::ConflictingFoldDesc { .. } => {
            unreachable!("a coefficient use carries no fold descriptor")
        }
    })?;

    // `(family, column)` is injective over sources — a read family plus its
    // address IS the `ReadPlace`, and each procedural kind is its own
    // single-column family — so the reverse map is well defined.
    let source_at: BTreeMap<(WindowFamily, usize), SourceId> = sequence
        .iter()
        .map(|&(_, _, source)| (placed[source.0 as usize], source))
        .collect();
    let family_at: Vec<WindowFamily> = families.keys().copied().collect();

    let windows = binding
        .windows
        .iter()
        .map(|window| {
            let family = family_at[window.slot as usize];
            BoundSourceWindow {
                family,
                first_column: window.first_column,
                columns: window
                    .columns
                    .iter()
                    .map(|&column| BoundColumn {
                        column,
                        source: source_at[&(family, column)],
                    })
                    .collect(),
            }
        })
        .collect();

    let target_depth = placement.request.target_depth;
    Ok(CoeffSourceBinding {
        target_depth,
        materialize: target_depth >= PUBLISH_TARGET_DEPTH,
        windows,
        uses: sequence
            .iter()
            .zip(&binding.uses)
            .map(|(&(instr, slot, source), bound)| BoundInput {
                instr,
                slot,
                source,
                window: bound.window,
                column: bound.column,
                first_access: bound.first_access,
            })
            .collect(),
    })
}

// ── §12.3: the source and materialization certificate ────────────────────────

/// Prove a binding against the program it claims to bind.
///
/// Design §12.3, minus the two claims no compiler pass can decide. Both are
/// RESOLVER/RUNTIME obligations, discharged by Tasks 10-13 rather than here, and
/// they are named so nobody re-derives the gap as a finding:
///
///   * **"read and publish backings do not alias destructively"** is a property of
///     the DEVICE layout — which buffer the resolver publishes into versus which
///     one it reads. Task 8's artifact deliberately contains no physical pointer
///     and no publish backing (§13), so the fact this clause is about does not
///     exist at compile time. It becomes checkable when Task 9's descriptor
///     assigns the concrete backings, and it is the source-resolution path in
///     Tasks 10-13 that must honour it.
///   * **"non-materializing sources do not depend on publication"** is the §10.2
///     resolver contract: when [`CoeffSourceBinding::materialize`] is false, every
///     `first_access` bit is INERT and no resolution may read a published buffer.
///     The certificate can and does prove the static half — `materialize` is
///     exactly §10.2's policy for `target_depth` — but "the resolver ignores the
///     marker" is a statement about the resolver's behaviour, which this module
///     cannot observe. Task 10's D0-D3 source resolution owns it.
///
/// `cross_fields` is the same circuit-level map [`bind_coeff_sources`] was given.
/// It is required — not optional — because it is the only way to recompute a
/// window's true [`WindowFamily`], and a family the certificate does not check is
/// a family that can be wrong.
pub fn certify_source_binding(
    layer: &CoeffLayer,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
    placement: &CoeffPlacement,
    binding: &CoeffSourceBinding,
) -> Result<(), SourceCertificateError> {
    // "First access is assigned after every program transform": re-derive the
    // sequence from the FINAL placement and require the binding to be exactly it.
    // A program transformed after binding cannot satisfy this.
    let sequence = resolution_sequence(placement);
    if sequence.len() != binding.uses.len() {
        return Err(SourceCertificateError::SequenceMismatch {
            index: sequence.len().min(binding.uses.len()),
        });
    }
    for (index, (&(instr, slot, source), bound)) in sequence.iter().zip(&binding.uses).enumerate() {
        if (instr, slot, source) != (bound.instr, bound.slot, bound.source) {
            return Err(SourceCertificateError::SequenceMismatch { index });
        }
        if bound.window as usize >= source_bind::MAX_SOURCE_WINDOWS
            || bound.column as usize >= source_bind::SOURCE_WINDOW_COLUMNS
        {
            return Err(SourceCertificateError::CoordinateOutOfRange {
                index,
                window: bound.window,
                column: bound.column,
            });
        }
        if binding.resolve(bound.window, bound.column) != Some(source) {
            return Err(SourceCertificateError::CoordinateMismatch { index, source });
        }
    }

    // "A native dual factor counts as one physical source resolution" is enforced
    // by construction — one `ValueUse` per deduplicated operand slot, one
    // coordinate per source-bearing use — and checked by the sequence equality
    // above, which re-derives it from the placement's own slots.

    // "Each materializing source with a physical miss has exactly one first use",
    // and "later non-first materialized uses are dominated by publication": in
    // execution order, the FIRST resolution of a source is the marked one, so
    // every later use follows it.
    let mut first_seen: BTreeMap<SourceId, usize> = BTreeMap::new();
    let mut marked: BTreeMap<SourceId, usize> = BTreeMap::new();
    for (index, use_) in binding.uses.iter().enumerate() {
        first_seen.entry(use_.source).or_insert(index);
        if use_.first_access {
            *marked.entry(use_.source).or_default() += 1;
            if first_seen[&use_.source] != index {
                return Err(SourceCertificateError::FirstAccessNotFirst {
                    source: use_.source,
                    marked: index,
                });
            }
        }
    }
    for (source, index) in &first_seen {
        if marked.get(source).copied() != Some(1) {
            return Err(SourceCertificateError::FirstAccessNotFirst {
                source: *source,
                marked: *index,
            });
        }
    }

    // The window layout: dense, ascending, in span, and — within one backing —
    // unmergeable, which is what makes the partition canonical.
    let mut previous: Option<(WindowFamily, usize)> = None;
    for (index, window) in binding.windows.iter().enumerate() {
        let malformed = || SourceCertificateError::MalformedWindow { window: index };
        let first = window.columns.first().ok_or_else(malformed)?;
        let last = window.columns.last().ok_or_else(malformed)?;
        if first.column != window.first_column
            || last.column - window.first_column >= source_bind::SOURCE_WINDOW_COLUMNS
        {
            return Err(malformed());
        }
        if window.columns.windows(2).any(|pair| pair[0].column >= pair[1].column) {
            return Err(malformed());
        }
        // Every column resolves to a real source, and the window's DECLARED family
        // and column address are the ones that source actually lives at. This is
        // the check that gives `BoundSourceWindow::family` its meaning: the
        // descriptor picks DRAM versus procedural resolution off it, so it must be
        // re-derived from the source, never trusted.
        for column in &window.columns {
            let Some(source) = layer.source(column.source) else {
                return Err(malformed());
            };
            if window_family(source, cross_fields) != (window.family, column.column) {
                return Err(SourceCertificateError::WindowFamilyMismatch {
                    window: index,
                    column: column.column,
                    source: column.source,
                });
            }
        }
        if let Some((family, first_column)) = previous
            && family == window.family
            && window.first_column < first_column + source_bind::SOURCE_WINDOW_COLUMNS
        {
            return Err(malformed());
        }
        previous = Some((window.family, window.first_column));
    }

    if binding.materialize != (binding.target_depth >= PUBLISH_TARGET_DEPTH) {
        return Err(SourceCertificateError::MaterializationNotPolicy {
            target_depth: binding.target_depth,
            materialize: binding.materialize,
        });
    }
    Ok(())
}
