use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::accumulator_schedule::SemanticSourceKey;
use crate::r0_prototype_encoding::R0PrototypeOp;

pub const R0_TILE_BF_IDENTITY_BYTES: u32 = 32 * 8 * 4;
pub const R0_TILE_E4_IDENTITY_BYTES: u32 = 32 * 8 * 16;
pub const R0_TILE_SOURCE_NONE: u16 = u16::MAX;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R0TileCapacity {
    C8,
    C16,
    C32,
}

impl R0TileCapacity {
    pub const ALL: [Self; 3] = [Self::C8, Self::C16, Self::C32];

    pub const fn identities(self) -> usize {
        match self {
            Self::C8 => 8,
            Self::C16 => 16,
            Self::C32 => 32,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0SourceTile {
    pub first_record: u32,
    pub record_count: u32,
    pub bf_sources: Vec<SemanticSourceKey>,
    pub e4_sources: Vec<SemanticSourceKey>,
    pub record_local_sources: Vec<[u16; 2]>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0SourceTilePlan {
    pub capacity: R0TileCapacity,
    pub tiles: Vec<R0SourceTile>,
    pub max_dynamic_shared_bytes: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R0TilePlanError {
    InvalidClass(u8),
    InvalidArity(u8),
    RecordExceedsCapacity {
        record: usize,
        required: usize,
        capacity: usize,
    },
    SourceFieldConflict(SemanticSourceKey),
    CountOverflow,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TileField {
    Bf,
    E4,
}

fn typed_record_sources(
    operation: &R0PrototypeOp,
) -> Result<Vec<(SemanticSourceKey, TileField)>, R0TilePlanError> {
    let sources = match (operation.term_class, operation.source_b) {
        (0, None) => vec![(operation.source_a, TileField::Bf)],
        (1, None) => vec![(operation.source_a, TileField::E4)],
        (2, Some(source_b)) => vec![
            (operation.source_a, TileField::Bf),
            (source_b, TileField::Bf),
        ],
        (3, Some(source_b)) => vec![
            (operation.source_a, TileField::Bf),
            (source_b, TileField::E4),
        ],
        (4, Some(source_b)) => vec![
            (operation.source_a, TileField::E4),
            (source_b, TileField::E4),
        ],
        (class @ 0..=1, Some(_)) | (class @ 2..=4, None) => {
            return Err(R0TilePlanError::InvalidArity(class));
        }
        (class, _) => return Err(R0TilePlanError::InvalidClass(class)),
    };
    Ok(sources)
}

fn finish_tile(
    first_record: usize,
    records: &[Vec<(SemanticSourceKey, TileField)>],
) -> Result<R0SourceTile, R0TilePlanError> {
    let mut fields = BTreeMap::new();
    let mut bf_sources = Vec::new();
    let mut e4_sources = Vec::new();
    for record in records {
        for (source, field) in record {
            match fields.get(source) {
                Some(previous) if previous != field => {
                    return Err(R0TilePlanError::SourceFieldConflict(*source));
                }
                Some(_) => {}
                None => {
                    fields.insert(*source, *field);
                    match field {
                        TileField::Bf => bf_sources.push(*source),
                        TileField::E4 => e4_sources.push(*source),
                    }
                }
            }
        }
    }
    let bf_indices = bf_sources
        .iter()
        .enumerate()
        .map(|(index, source)| (*source, index))
        .collect::<BTreeMap<_, _>>();
    let e4_indices = e4_sources
        .iter()
        .enumerate()
        .map(|(index, source)| (*source, bf_sources.len() + index))
        .collect::<BTreeMap<_, _>>();
    let mut record_local_sources = Vec::with_capacity(records.len());
    for record in records {
        let mut local = [R0_TILE_SOURCE_NONE; 2];
        for (operand, (source, field)) in record.iter().enumerate() {
            let index = match field {
                TileField::Bf => bf_indices[source],
                TileField::E4 => e4_indices[source],
            };
            local[operand] = u16::try_from(index).map_err(|_| R0TilePlanError::CountOverflow)?;
        }
        record_local_sources.push(local);
    }
    Ok(R0SourceTile {
        first_record: u32::try_from(first_record).map_err(|_| R0TilePlanError::CountOverflow)?,
        record_count: u32::try_from(records.len()).map_err(|_| R0TilePlanError::CountOverflow)?,
        bf_sources,
        e4_sources,
        record_local_sources,
    })
}

pub fn plan_r0_source_tiles(
    operations: &[R0PrototypeOp],
    capacity: R0TileCapacity,
) -> Result<R0SourceTilePlan, R0TilePlanError> {
    let mut tiles = Vec::new();
    let mut first_record = 0usize;
    let mut records = Vec::<Vec<(SemanticSourceKey, TileField)>>::new();
    let mut identities = BTreeSet::<SemanticSourceKey>::new();
    for (record_index, operation) in operations.iter().enumerate() {
        let sources = typed_record_sources(operation)?;
        let record_identities = sources.iter().map(|entry| entry.0).collect::<BTreeSet<_>>();
        if record_identities.len() > capacity.identities() {
            return Err(R0TilePlanError::RecordExceedsCapacity {
                record: record_index,
                required: record_identities.len(),
                capacity: capacity.identities(),
            });
        }
        let required = identities.union(&record_identities).count();
        if !records.is_empty() && required > capacity.identities() {
            tiles.push(finish_tile(first_record, &records)?);
            records.clear();
            identities.clear();
            first_record = record_index;
        }
        identities.extend(record_identities);
        records.push(sources);
    }
    if !records.is_empty() {
        tiles.push(finish_tile(first_record, &records)?);
    }
    let max_dynamic_shared_bytes = tiles
        .iter()
        .map(|tile| {
            (tile.bf_sources.len() as u32) * R0_TILE_BF_IDENTITY_BYTES
                + (tile.e4_sources.len() as u32) * R0_TILE_E4_IDENTITY_BYTES
        })
        .max()
        .unwrap_or(0);
    Ok(R0SourceTilePlan {
        capacity,
        tiles,
        max_dynamic_shared_bytes,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use gpu_gkr_compiler::backward::analyze_coeff_grouping;

    use crate::accumulator_schedule::build_schedule_views;
    use crate::accumulator_schedule::{SemanticSourceKey, SourceProjection};
    use crate::census::compile_corpus;
    use crate::r0_artifact::{decode_r0_bundle, R0_CORPUS_BYTES};
    use crate::r0_prototype_encoding::prototype_operations;
    use crate::r0_prototype_encoding::{R0Phase, R0PrototypeOp};
    use crate::r0_prototype_manifest::R0ProgramEncoding;

    use super::{plan_r0_source_tiles, R0TileCapacity};

    fn source(id: u32, projection: SourceProjection) -> SemanticSourceKey {
        SemanticSourceKey {
            source: id,
            projection,
        }
    }

    fn linear(id: u32, class: u8) -> R0PrototypeOp {
        R0PrototypeOp {
            phase: if class == 0 { R0Phase::Bf } else { R0Phase::E4 },
            term_class: class,
            coefficient_id: 0,
            source_a: source(id, SourceProjection::Endpoint0),
            source_b: None,
            group_id: None,
            member_index: None,
        }
    }

    fn product(a: u32, b: u32, class: u8) -> R0PrototypeOp {
        R0PrototypeOp {
            phase: if class == 2 { R0Phase::Bf } else { R0Phase::E4 },
            term_class: class,
            coefficient_id: 0,
            source_a: source(a, SourceProjection::Delta),
            source_b: Some(source(b, SourceProjection::Delta)),
            group_id: None,
            member_index: None,
        }
    }

    #[test]
    fn cpu_pair_closed_greedy_tiles_keep_complete_records_and_stable_order() {
        let mut operations = vec![product(0, 1, 2)];
        operations.extend((2..8).map(|id| linear(id, 0)));
        operations.push(product(0, 8, 2));
        let plan = plan_r0_source_tiles(&operations, R0TileCapacity::C8).unwrap();
        assert_eq!(plan.tiles.len(), 2);
        assert_eq!(plan.tiles[0].first_record, 0);
        assert_eq!(plan.tiles[0].record_count, 7);
        assert_eq!(plan.tiles[0].bf_sources.len(), 8);
        assert!(plan.tiles[0].e4_sources.is_empty());
        assert_eq!(plan.tiles[0].record_local_sources.len(), 7);
        assert_eq!(plan.tiles[0].record_local_sources[0], [0, 1]);
        assert!(plan
            .tiles
            .iter()
            .all(|tile| tile.bf_sources.len() + tile.e4_sources.len() <= 8));
        assert_eq!(plan.tiles[1].record_count, 1);
        assert_eq!(plan.tiles[1].bf_sources[0].source, 0);
        assert_eq!(plan.tiles[1].bf_sources[1].source, 8);
    }

    #[test]
    fn cpu_all_e4_capacity_bytes_are_exact() {
        let operations = (0..32).map(|id| linear(id, 1)).collect::<Vec<_>>();
        for (capacity, bytes) in [
            (R0TileCapacity::C8, 32 * 1024),
            (R0TileCapacity::C16, 64 * 1024),
            (R0TileCapacity::C32, 128 * 1024),
        ] {
            let plan = plan_r0_source_tiles(&operations, capacity).unwrap();
            assert_eq!(plan.max_dynamic_shared_bytes, bytes);
            assert!(
                plan.tiles
                    .iter()
                    .all(|tile| tile.bf_sources.len() + tile.e4_sources.len()
                        <= capacity.identities())
            );
        }
    }

    #[test]
    fn cpu_all_corpus_tile_extrema_are_derived_from_complete_operations() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let frozen = bundle
            .coordinates
            .iter()
            .map(|coordinate| ((coordinate.circuit.as_str(), coordinate.layer), coordinate))
            .collect::<BTreeMap<_, _>>();
        let corpus = compile_corpus().unwrap();
        let mut cases = 0usize;
        let mut max_tiles = (0usize, String::new());
        let mut max_tile_sources = (0usize, String::new());
        for layer in &corpus.layers {
            let coordinate = frozen[&(layer.circuit.as_str(), layer.layer as u32)];
            let grouping = analyze_coeff_grouping(&layer.r0.coefficients).unwrap();
            let schedules =
                build_schedule_views(&layer.r0.coefficients, &layer.r0.binding, &grouping).unwrap();
            for encoding in R0ProgramEncoding::ALL {
                let operations = prototype_operations(
                    coordinate,
                    &layer.r0.coefficients,
                    &schedules,
                    &grouping,
                    encoding.grouped(),
                )
                .unwrap();
                for capacity in R0TileCapacity::ALL {
                    let plan = plan_r0_source_tiles(&operations, capacity).unwrap();
                    let label = format!(
                        "{}:{}:{}:{capacity:?}",
                        layer.circuit,
                        layer.layer,
                        encoding.as_str()
                    );
                    max_tiles = max_tiles.max((plan.tiles.len(), label.clone()));
                    max_tile_sources = max_tile_sources.max((
                        plan.tiles
                            .iter()
                            .map(|tile| tile.bf_sources.len() + tile.e4_sources.len())
                            .sum(),
                        label,
                    ));
                    assert_eq!(
                        plan.tiles
                            .iter()
                            .map(|tile| tile.record_count as usize)
                            .sum::<usize>(),
                        operations.len()
                    );
                    cases += 1;
                }
            }
        }
        assert_eq!(cases, 57 * 8 * 3);
        println!("R0_TILE_MAX_TILES {} {}", max_tiles.0, max_tiles.1);
        println!(
            "R0_TILE_MAX_SOURCE_OCCURRENCES {} {}",
            max_tile_sources.0, max_tile_sources.1
        );
    }
}
