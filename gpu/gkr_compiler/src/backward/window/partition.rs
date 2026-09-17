//! Source-disjoint partitions of whole R0 atoms.
//!
//! A part is a whole-unit subset of the program: BF atoms (head plus members), single
//! wide-linear and singleton E4 records, and three-record E4 pair groups never split, and every
//! section keeps the original unit order. Units sharing a physical source column land in the same
//! part (connected components over all four sections), so no source byte is read by two parts.
//! Procedural sources carry no bytes and create no sharing. Parts keep the complete source slot
//! table, windows, immediates, coefficient plans, shape; only the
//! record words, the source lanes and the four section ends are rebuilt. The scalar seed is not
//! part of the plan: the runtime applies the original seed in part 0 only.
use super::{
    validate_window_coefficient_ids, validate_window_source_lanes, WindowLoweringError,
    WindowProgram, WindowSourceLane, WINDOW_OPCODE_GROUP_BF, WINDOW_SOURCE_COLUMNS,
    WINDOW_SOURCE_COLUMN_BITS,
};
use gkr_eval_ir::FieldKind;
use std::collections::BTreeMap;

/// One physical column is read at eight corners for each of the 32 rows of a block tile.
const TILE_ROWS: usize = 32;
const CORNERS: usize = 8;

#[derive(Clone, Debug, PartialEq)]
pub struct R0PartitionPlan {
    pub parts: Vec<WindowProgram>,
    /// Unique physical source bytes per block tile read by each part (BF 4 B and E4 16 B per
    /// corner value); disjoint across parts, summing to the program's own footprint.
    pub source_bytes_per_tile: Vec<usize>,
}

struct Unit {
    section: usize,
    words: std::ops::Range<usize>,
    /// Canonical physical sources, sorted and deduplicated; procedural sources excluded.
    sources: Vec<u16>,
}

fn malformed(message: impl Into<String>) -> WindowLoweringError {
    WindowLoweringError::Encoding(message.into())
}

/// Canonical id per slot (the first slot bound to the same physical column) and the per-tile
/// byte weight per canonical id. Procedural windows map to `None`.
fn canonical_sources(
    program: &WindowProgram,
) -> Result<(Vec<Option<u16>>, Vec<usize>), WindowLoweringError> {
    let mut first = BTreeMap::new();
    let mut canonical = Vec::with_capacity(program.source_slots.len());
    let mut bytes = vec![0usize; program.source_slots.len()];
    for (slot, &lane) in program.source_slots.iter().enumerate() {
        let window = program
            .windows
            .get(usize::from(lane >> WINDOW_SOURCE_COLUMN_BITS))
            .ok_or_else(|| malformed("source slot names an absent window"))?;
        if window.procedural_kind().is_some() {
            canonical.push(None);
            continue;
        }
        let column = window
            .first_column
            .checked_add(usize::from(lane & (WINDOW_SOURCE_COLUMNS - 1)))
            .ok_or_else(|| malformed("source column offset overflows"))?;
        let width = match window.backing_field() {
            FieldKind::Base => 4,
            FieldKind::Ext => 16,
        };
        let id = u16::try_from(slot).map_err(|_| malformed("more than 65535 source slots"))?;
        let (first_slot, first_width) =
            *first.entry((window.family, column)).or_insert((id, width));
        if first_width != width {
            return Err(malformed(
                "aliased physical column bound with two different field widths",
            ));
        }
        canonical.push(Some(first_slot));
        bytes[usize::from(first_slot)] = TILE_ROWS * CORNERS * width;
    }
    Ok((canonical, bytes))
}

// The caller validates the wire and lane table before deriving whole-atom ranges.
fn units(program: &WindowProgram, lane_at: &[Option<u16>], canonical: &[Option<u16>]) -> Vec<Unit> {
    let mut units = Vec::new();
    let mut pc = 0usize;
    for section in 0..4 {
        while pc < program.sections[section] as usize {
            let records = if section == 0 && program.words[4 * pc] == WINDOW_OPCODE_GROUP_BF {
                1 + usize::from(program.words[4 * pc + 2])
            } else if section == 3 {
                3
            } else {
                1
            };
            let words = 4 * pc..4 * (pc + records);
            let mut sources: Vec<u16> = lane_at[words.clone()]
                .iter()
                .filter_map(|slot| slot.and_then(|slot| canonical[usize::from(slot)]))
                .collect();
            sources.sort_unstable();
            sources.dedup();
            units.push(Unit {
                section,
                words,
                sources,
            });
            pc += records;
        }
    }
    units
}

fn find(parent: &mut [usize], mut x: usize) -> usize {
    while parent[x] != x {
        parent[x] = parent[parent[x]];
        x = parent[x];
    }
    x
}

struct Component {
    first_unit: usize,
    units: Vec<usize>,
    records: usize,
    bytes: usize,
}

struct Partitioner<'a> {
    program: &'a WindowProgram,
    lane_at: Vec<Option<u16>>,
    units: Vec<Unit>,
    components: Vec<Component>,
}

impl<'a> Partitioner<'a> {
    fn new(program: &'a WindowProgram) -> Result<Self, WindowLoweringError> {
        validate_window_coefficient_ids(program)?;
        validate_window_source_lanes(program)?;
        let mut lane_at = vec![None; program.words.len()];
        for lane in &program.source_lanes {
            lane_at[lane.word as usize] = Some(lane.source);
        }
        let (canonical, bytes) = canonical_sources(program)?;
        let units = units(program, &lane_at, &canonical);
        // Connected components of units over shared canonical sources.
        let mut parent: Vec<usize> = (0..units.len()).collect();
        let mut owner: BTreeMap<u16, usize> = BTreeMap::new();
        for (index, unit) in units.iter().enumerate() {
            for &source in &unit.sources {
                match owner.get(&source) {
                    Some(&other) => {
                        let (a, b) = (find(&mut parent, index), find(&mut parent, other));
                        if a != b {
                            parent[a] = b;
                        }
                    }
                    None => {
                        owner.insert(source, index);
                    }
                }
            }
        }
        let mut components: BTreeMap<usize, Component> = BTreeMap::new();
        for (index, unit) in units.iter().enumerate() {
            let root = find(&mut parent, index);
            let component = components.entry(root).or_insert(Component {
                first_unit: index,
                units: Vec::new(),
                records: 0,
                bytes: 0,
            });
            component.units.push(index);
            component.records += unit.words.len() / 4;
        }
        for component in components.values_mut() {
            let mut seen = std::collections::BTreeSet::new();
            for &index in &component.units {
                for &source in &units[index].sources {
                    if seen.insert(source) {
                        component.bytes += bytes[usize::from(source)];
                    }
                }
            }
        }
        let mut components: Vec<Component> = components.into_values().collect();
        // Deterministic longest-processing-time packing: heaviest component first by unique bytes,
        // then records, then first unit; into the lightest bin by bytes, then records, then index.
        components.sort_by(|a, b| {
            b.bytes
                .cmp(&a.bytes)
                .then(b.records.cmp(&a.records))
                .then(a.first_unit.cmp(&b.first_unit))
        });
        Ok(Self {
            program,
            lane_at,
            units,
            components,
        })
    }

    fn plan(&self, requested_parts: usize) -> Result<R0PartitionPlan, WindowLoweringError> {
        if requested_parts == 0 {
            return Err(malformed("zero partitions requested"));
        }
        let Self {
            program,
            lane_at,
            units,
            components,
        } = self;
        let bins = requested_parts.min(components.len()).max(1);
        if bins == 1 {
            return Ok(R0PartitionPlan {
                parts: vec![(*program).clone()],
                source_bytes_per_tile: vec![components.iter().map(|c| c.bytes).sum()],
            });
        }
        let mut bin_bytes = vec![0usize; bins];
        let mut bin_records = vec![0usize; bins];
        let mut unit_bin = vec![usize::MAX; units.len()];
        for component in components {
            let bin = (0..bins)
                .min_by_key(|&bin| (bin_bytes[bin], bin_records[bin], bin))
                .expect("at least one bin");
            bin_bytes[bin] += component.bytes;
            bin_records[bin] += component.records;
            for &index in &component.units {
                unit_bin[index] = bin;
            }
        }

        let mut parts = Vec::with_capacity(bins);
        for bin in 0..bins {
            let mut part = (*program).clone();
            let mut words = Vec::new();
            let mut lanes = Vec::new();
            for section in 0..4 {
                for (index, unit) in units.iter().enumerate() {
                    if unit.section != section || unit_bin[index] != bin {
                        continue;
                    }
                    let base = words.len();
                    words.extend_from_slice(&program.words[unit.words.clone()]);
                    for (offset, slot) in lane_at[unit.words.clone()].iter().enumerate() {
                        if let Some(source) = slot {
                            lanes.push(WindowSourceLane {
                                word: u32::try_from(base + offset)
                                    .map_err(|_| malformed("part exceeds the u32 word space"))?,
                                source: *source,
                            });
                        }
                    }
                }
                part.sections[section] = u32::try_from(words.len() / 4)
                    .map_err(|_| malformed("part exceeds the u32 record space"))?;
            }
            if words.is_empty() {
                return Err(malformed("packing produced an empty part"));
            }
            part.words = words;
            part.source_lanes = lanes;
            validate_window_coefficient_ids(&part)?;
            validate_window_source_lanes(&part)?;
            parts.push(part);
        }
        Ok(R0PartitionPlan {
            parts,
            source_bytes_per_tile: bin_bytes,
        })
    }
}

pub mod policy;

#[cfg(test)]
mod tests;
