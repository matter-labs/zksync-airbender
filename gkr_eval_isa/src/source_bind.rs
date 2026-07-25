//! Final source binding: freely based dense windows over one logical column
//! space, plus the first-access marker, generic over the caller's backing table.
//!
//! This is the sequence core the forward compiler has always run
//! ([`crate::fwd::binding::bind_final_sources`]), lifted out of that module so the
//! backward coefficient schedule can reuse it. The forward path keeps its own
//! `Program` adapter, its own `BackingKey`/`BackingTable` vocabulary, its own
//! `SourceWindowTable`, and its own error type; only the window-partitioning and
//! first-access core moved here. Nothing in this module knows about instructions,
//! operands, `ReadPlace`, `ProjectionId`, or fields.
//!
//! # The model (design §9.4, §10.3)
//!
//! A use names a `(slot, column)`: an opaque LOGICAL BACKING index and that
//! backing's own column. Binding assigns windows:
//!
//!   1. a window belongs to exactly one backing;
//!   2. it is freely based — its `first_column` is a referenced column, never an
//!      aligned multiple of anything;
//!   3. it covers at most [`SOURCE_WINDOW_COLUMNS`] contiguous columns, of which
//!      only the REFERENCED ones are addressable; and
//!   4. a program uses at most [`MAX_SOURCE_WINDOWS`] windows.
//!
//! Windows are numbered by ascending `(slot, column)`, so **the caller's backing
//! order is the window order**: a caller that wants a particular window numbering
//! (the forward path wants `BackingKey` order) assigns its slot indices in that
//! order before calling.
//!
//! `first_access` is assigned LAST (§10.3) and only when the caller asks for it:
//! the first use of each `(slot, column)` in the sequence order carries the bit
//! and later uses of the same column do not. The sequence is therefore the
//! caller's exact execution order — one entry per PHYSICAL source resolution, not
//! per logical projection, so a fused pair resolution consumes one bit.

use std::collections::{BTreeMap, HashSet};

/// Contiguous columns one window spans (§9.4's `column:7`).
pub const SOURCE_WINDOW_COLUMNS: usize = 128;

/// Windows one program may use (§9.4's `source_window:6`).
pub const MAX_SOURCE_WINDOWS: usize = 64;

// One number, two frozen wire formats. The forward ISA and the backward
// coefficient ISA both encode this coordinate, and a drift in either would make
// this core silently produce coordinates the encoder cannot represent.
const _: () = assert!(SOURCE_WINDOW_COLUMNS as u32 == crate::fwd::isa::SOURCE_WINDOW_COLUMNS);
const _: () = assert!(MAX_SOURCE_WINDOWS as u32 == crate::fwd::isa::MAX_SOURCE_WINDOWS);
const _: () = assert!(SOURCE_WINDOW_COLUMNS == crate::bwd::coeff::limits::SOURCE_WINDOW_COLUMNS);
const _: () = assert!(MAX_SOURCE_WINDOWS == crate::bwd::coeff::limits::MAX_SOURCE_WINDOWS);

/// One physical source resolution, in exact execution order.
///
/// `column` is the backing's OWN column index (`usize`, like every column space in
/// this crate — `ReadPlace`, `BackingTable::slot_columns`, `CoeffSource`); the
/// seven-bit narrowing happens in [`BoundSourceUse`], never here.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LogicalSourceUse {
    /// Logical backing index, in the caller's window order.
    pub slot: u8,
    /// The backing's own column.
    pub column: usize,
    /// Fold descriptor this column resolves through, when the caller has one. All
    /// uses of one column must agree.
    pub fold_desc: Option<u16>,
}

/// The bound coordinate of one use: §9.4's `[ column:7 | source_window:6 |
/// first_access:1 ]` payload, unpacked.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BoundSourceUse {
    pub window: u8,
    /// Offset from the window's `first_column`, `< SOURCE_WINDOW_COLUMNS`.
    pub column: u8,
    pub first_access: bool,
}

/// One assigned window, in window-index order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundWindow {
    pub slot: u8,
    pub first_column: usize,
    /// Referenced columns, ascending, all in
    /// `[first_column, first_column + SOURCE_WINDOW_COLUMNS)`. Only these are
    /// addressable: an unreferenced column inside the span is a hole.
    pub columns: Vec<usize>,
    /// The fold descriptor of every column that has one, keyed by absolute column.
    pub fold_descs: BTreeMap<usize, u16>,
}

/// A complete binding: the window layout, and one bound coordinate per input use
/// in the same order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceBinding {
    pub windows: Vec<BoundWindow>,
    pub uses: Vec<BoundSourceUse>,
}

/// Why a sequence could not be bound. Both variants are caller-diagnosable: the
/// caller owns the `(slot, column)` vocabulary and translates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindFailure {
    /// The layout needs more than [`MAX_SOURCE_WINDOWS`] windows.
    WindowOverflow,
    /// Two uses of one column disagree on its fold descriptor.
    ConflictingFoldDesc { slot: u8, column: usize },
}

/// Bind one execution-ordered sequence of physical source resolutions.
///
/// `mark_first_access` requests §10.3's marker. It is a deliberate parameter and
/// not a property of the sequence: the forward VM has no first-access semantics at
/// all and must leave every bit clear.
pub fn bind_source_sequence(
    uses: &[LogicalSourceUse],
    mark_first_access: bool,
) -> Result<SourceBinding, BindFailure> {
    // `(slot, column)` ordering IS "group by backing, then ascending column", so
    // one map gives both the window grouping and the deterministic scan order.
    let mut referenced = BTreeMap::<(u8, usize), Option<u16>>::new();
    for use_ in uses {
        match referenced.entry((use_.slot, use_.column)) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(use_.fold_desc);
            }
            std::collections::btree_map::Entry::Occupied(entry)
                if *entry.get() != use_.fold_desc =>
            {
                return Err(BindFailure::ConflictingFoldDesc {
                    slot: use_.slot,
                    column: use_.column,
                });
            }
            std::collections::btree_map::Entry::Occupied(_) => {}
        }
    }

    // Greedy first-fit: open a window at the first column the active one cannot
    // cover. Optimal for a fixed span — starting later can only lose coverage —
    // and it is what makes the layout a pure function of the referenced set.
    let mut windows = Vec::<BoundWindow>::new();
    let mut locations = BTreeMap::<(u8, usize), (u8, u8)>::new();
    let mut active = None::<(u8, u8, usize)>; // (slot, window, first_column)
    for (&(slot, column), &fold_desc) in &referenced {
        let (window, first_column) = match active {
            Some((active_slot, window, first)) if active_slot == slot && column < first + SOURCE_WINDOW_COLUMNS => {
                (window, first)
            }
            _ => {
                if windows.len() >= MAX_SOURCE_WINDOWS {
                    return Err(BindFailure::WindowOverflow);
                }
                let window = windows.len() as u8;
                windows.push(BoundWindow {
                    slot,
                    first_column: column,
                    columns: Vec::new(),
                    fold_descs: BTreeMap::new(),
                });
                active = Some((slot, window, column));
                (window, column)
            }
        };
        let entry = &mut windows[window as usize];
        entry.columns.push(column);
        if let Some(desc) = fold_desc {
            entry.fold_descs.insert(column, desc);
        }
        locations.insert((slot, column), (window, (column - first_column) as u8));
    }

    let mut seen = HashSet::<(u8, usize)>::new();
    let bound = uses
        .iter()
        .map(|use_| {
            let &(window, column) = locations
                .get(&(use_.slot, use_.column))
                .expect("every use's column was just laid out");
            BoundSourceUse {
                window,
                column,
                first_access: mark_first_access && seen.insert((use_.slot, use_.column)),
            }
        })
        .collect();

    Ok(SourceBinding { windows, uses: bound })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn read(slot: u8, column: usize) -> LogicalSourceUse {
        LogicalSourceUse { slot, column, fold_desc: None }
    }

    #[test]
    fn windows_are_freely_based_and_hold_only_referenced_columns() {
        let binding = bind_source_sequence(&[read(0, 128), read(0, 1)], false).unwrap();
        assert_eq!(binding.windows.len(), 1);
        assert_eq!(binding.windows[0].first_column, 1);
        assert_eq!(binding.windows[0].columns, vec![1, 128]);
        assert_eq!(
            binding.uses,
            vec![
                BoundSourceUse { window: 0, column: 127, first_access: false },
                BoundSourceUse { window: 0, column: 0, first_access: false },
            ]
        );
    }

    #[test]
    fn a_backing_boundary_always_opens_a_new_window() {
        // Same column in two backings: two windows, never one shared span.
        let binding = bind_source_sequence(&[read(0, 7), read(1, 7)], false).unwrap();
        assert_eq!(binding.windows.len(), 2);
        assert_eq!((binding.windows[0].slot, binding.windows[1].slot), (0, 1));
        assert_eq!(binding.uses[0].window, 0);
        assert_eq!(binding.uses[1].window, 1);
    }

    #[test]
    fn windows_are_numbered_in_ascending_backing_order() {
        // The sequence visits backing 2 first; the LAYOUT still numbers by backing.
        let binding = bind_source_sequence(&[read(2, 0), read(0, 0), read(1, 0)], false).unwrap();
        assert_eq!(binding.windows.iter().map(|w| w.slot).collect::<Vec<_>>(), vec![0, 1, 2]);
        assert_eq!(
            binding.uses.iter().map(|u| u.window).collect::<Vec<_>>(),
            vec![2, 0, 1]
        );
    }

    #[test]
    fn first_access_marks_the_first_resolution_only() {
        let binding =
            bind_source_sequence(&[read(0, 5), read(0, 6), read(0, 5)], true).unwrap();
        assert_eq!(
            binding.uses.iter().map(|u| u.first_access).collect::<Vec<_>>(),
            vec![true, true, false]
        );
    }

    #[test]
    fn unmarked_mode_leaves_every_bit_clear() {
        let binding = bind_source_sequence(&[read(0, 5), read(0, 5)], false).unwrap();
        assert!(binding.uses.iter().all(|u| !u.first_access));
    }

    #[test]
    fn a_sixty_fifth_window_overflows() {
        let uses: Vec<_> = (0..=MAX_SOURCE_WINDOWS)
            .map(|i| read(0, i * SOURCE_WINDOW_COLUMNS))
            .collect();
        assert_eq!(bind_source_sequence(&uses, false), Err(BindFailure::WindowOverflow));
        assert_eq!(
            bind_source_sequence(&uses[..MAX_SOURCE_WINDOWS], false).unwrap().windows.len(),
            MAX_SOURCE_WINDOWS
        );
    }

    #[test]
    fn disagreeing_fold_descriptors_are_rejected() {
        let mut second = read(3, 9);
        second.fold_desc = Some(4);
        assert_eq!(
            bind_source_sequence(&[read(3, 9), second], false),
            Err(BindFailure::ConflictingFoldDesc { slot: 3, column: 9 })
        );
        // Agreeing descriptors bind, and the layout keeps them per column.
        let binding = bind_source_sequence(&[second, second], false).unwrap();
        assert_eq!(binding.windows[0].fold_descs.get(&9), Some(&4));
    }
}
