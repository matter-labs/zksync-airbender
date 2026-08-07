//! Source-window binding over logical backing columns.

use std::collections::{BTreeMap, BTreeSet};

pub(crate) const SOURCE_WINDOW_COLUMNS: usize = 128;
pub(crate) const MAX_SOURCE_WINDOWS: usize = 64;

const _: () = assert!(SOURCE_WINDOW_COLUMNS as u32 == crate::forward::isa::SOURCE_WINDOW_COLUMNS);
const _: () = assert!(MAX_SOURCE_WINDOWS as u32 == crate::forward::isa::MAX_SOURCE_WINDOWS);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct LogicalSourceUse {
    pub slot: u8,
    pub column: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct BoundSourceUse {
    pub window: u8,
    pub column: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BoundWindow {
    pub slot: u8,
    pub first_column: usize,
    pub columns: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SourceBinding {
    pub windows: Vec<BoundWindow>,
    pub uses: Vec<BoundSourceUse>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BindFailure {
    WindowOverflow,
}

pub(crate) fn bind_source_sequence(
    uses: &[LogicalSourceUse],
) -> Result<SourceBinding, BindFailure> {
    let referenced: BTreeSet<_> = uses.iter().map(|use_| (use_.slot, use_.column)).collect();
    let mut windows = Vec::new();
    let mut locations = BTreeMap::new();
    let mut active = None::<(u8, u8, usize)>;

    for &(slot, column) in &referenced {
        let (window, first_column) = match active {
            Some((active_slot, window, first))
                if active_slot == slot && column < first + SOURCE_WINDOW_COLUMNS =>
            {
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
                });
                active = Some((slot, window, column));
                (window, column)
            }
        };
        windows[window as usize].columns.push(column);
        locations.insert((slot, column), (window, (column - first_column) as u8));
    }

    let uses = uses
        .iter()
        .map(|use_| {
            let &(window, column) = locations
                .get(&(use_.slot, use_.column))
                .expect("every source use was bound");
            BoundSourceUse { window, column }
        })
        .collect();

    Ok(SourceBinding { windows, uses })
}
