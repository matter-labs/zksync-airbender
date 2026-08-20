use std::collections::BTreeSet;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Component, Path};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

use core::ops::Range;

use serde::{Deserialize, Serialize};

use crate::r0_geometry::R0Geometry;

pub const R0_PROTOTYPE_MANIFEST_VERSION: u32 = 1;
pub const R0_PROTOTYPE_TILE_CAPACITIES: [u8; 3] = [8, 16, 32];

static GENERATED_TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Compile-time hot-loop features derived from the checked, sectioned R0 wire
/// program.  Section presence is descriptor metadata rather than a shape bit:
/// an empty section is skipped by its uniform endpoint comparison.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(transparent)]
pub struct R0DedicatedShape(u16);

impl R0DedicatedShape {
    pub const EMPTY: Self = Self(0);
    pub const BF_PROCEDURAL: Self = Self(1 << 0);
    pub const BF_BANKED_IMMEDIATE: Self = Self(1 << 1);
    pub const BF_INNER_REDUCTION: Self = Self(1 << 2);
    pub const BF_LINEAR_TAIL: Self = Self(1 << 3);
    pub const E4_SINGLETON_CLASS_3: Self = Self(1 << 4);
    pub const E4_SINGLETON_CLASS_5: Self = Self(1 << 5);
    pub const E4_FIXED_PAIR: Self = Self(1 << 6);
    pub const BF_NEGATIVE_FACTOR: Self = Self(1 << 7);
    pub const E4_NEGATIVE_FACTOR: Self = Self(1 << 8);
    pub const E4_PAIR_CLASS_3: Self = Self(1 << 9);
    pub const E4_PAIR_CLASS_5: Self = Self(1 << 10);
    pub const BF_SINGLE_PRODUCT_PREFIX: Self = Self(1 << 11);

    pub const fn bits(self) -> u16 {
        self.0
    }

    pub const fn contains(self, feature: Self) -> bool {
        self.0 & feature.0 == feature.0
    }

    pub fn insert(&mut self, feature: Self) {
        self.0 |= feature.0;
    }
}

pub const R0_SECTIONED_UNIVERSAL_SHAPE: u16 = 4_095;
pub const R0_SECTIONED_SPECIALIZED_SHAPES: [u16; 14] = [
    1, 32, 433, 439, 1_015, 1_019, 1_120, 1_136, 1_270, 2_495, 3_067, 3_071, 3_192, 3_194,
];
pub const R0_SECTIONED_COMPILED_SHAPES_V4: [u16; 12] = [
    1, 32, 433, 439, 1_015, 1_019, 1_120, 1_136, 1_270, 3_067, 3_071, 3_194,
];
pub const R0_SECTIONED_UNION_SHAPES_V1: [u16; 33] = [
    0x001, 0x020, 0x021, 0x1b1, 0x1b7, 0x3f7, 0x3fb, 0x3ff, 0x460, 0x461, 0x470, 0x471, 0x4f6,
    0x4f7, 0x5f1, 0x5f7, 0x7f7, 0x7fb, 0x7ff, 0x9bf, 0xbfb, 0xbff, 0xc78, 0xc79, 0xc7a, 0xc7b,
    0xcfe, 0xcff, 0xdf9, 0xdfb, 0xdff, 0xffb, 0xfff,
];
pub const R0_SECTIONED_SHAPE_DISPATCH_V4: [(u16, u16); 14] = [
    (1, 1),
    (32, 32),
    (433, 433),
    (439, 439),
    (1_015, 1_015),
    (1_019, 1_019),
    (1_120, 1_120),
    (1_136, 1_136),
    (1_270, 1_270),
    (2_495, 3_071),
    (3_067, 3_067),
    (3_071, 3_071),
    (3_192, 3_194),
    (3_194, 3_194),
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum R0SectionedShapeMergePolicy {
    Exact,
    Merged,
    UnionBank,
}

impl R0SectionedShapeMergePolicy {
    pub fn parse(value: &str) -> Result<Self, R0PrototypeManifestError> {
        match value {
            "exact" => Ok(Self::Exact),
            "merged" => Ok(Self::Merged),
            "union_bank" => Ok(Self::UnionBank),
            _ => Err(R0PrototypeManifestError(format!(
                "invalid sectioned shape merge policy {value:?}"
            ))),
        }
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Exact => "exact",
            Self::Merged => "merged",
            Self::UnionBank => "union_bank",
        }
    }
}
pub const R0_SECTIONED_SWEEP_MIN_BLOCKS: [Option<u32>; 7] = [
    None,
    Some(7),
    Some(8),
    Some(9),
    Some(10),
    Some(12),
    Some(16),
];
pub const R0_SECTIONED_WIDE_MIN_BLOCKS_V3: [Option<u32>; 2] = [Some(3), Some(4)];

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R0SectionedGeometry {
    Wide9,
    Split3,
    Serial3Low,
    Serial3High,
}

impl R0SectionedGeometry {
    pub const ALL: [Self; 4] = [
        Self::Wide9,
        Self::Split3,
        Self::Serial3Low,
        Self::Serial3High,
    ];

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Wide9 => "wide9",
            Self::Split3 => "split3",
            Self::Serial3Low => "serial3_low",
            Self::Serial3High => "serial3_high",
        }
    }

    pub const fn owners(self) -> Range<u32> {
        match self {
            Self::Wide9 | Self::Split3 => 0..9,
            Self::Serial3Low | Self::Serial3High => 0..3,
        }
    }

    pub const fn threads(self) -> u32 {
        match self {
            Self::Wide9 => 288,
            Self::Split3 | Self::Serial3Low | Self::Serial3High => 96,
        }
    }

    pub const fn grid_multiplier(self) -> u32 {
        match self {
            Self::Split3 => 3,
            Self::Wide9 | Self::Serial3Low | Self::Serial3High => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R0SectionedOwnership {
    SelectorTriplet,
    FixedX0,
    FixedX1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0SectionedSymbolV1 {
    pub candidate_id: String,
    pub symbol: String,
    pub shape_bits: Option<u16>,
    pub geometry: R0SectionedGeometry,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub min_blocks: Option<u32>,
    pub ownership: R0SectionedOwnership,
    pub translation_unit: String,
    pub descriptor_kind: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0SectionedShapeDispatchV4 {
    pub input_shape: u16,
    pub compiled_shape: u16,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0SectionedGenericBuildControlsV2 {
    pub min_blocks: Option<u32>,
    pub maxreg: Option<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0SectionedManifestV1 {
    pub schema_version: u32,
    pub universal_shape: u16,
    pub specialized_shapes: [u16; 14],
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub generic_reference_build: Option<R0SectionedGenericBuildControlsV2>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub shape_dispatch: Vec<R0SectionedShapeDispatchV4>,
    pub symbols: Vec<R0SectionedSymbolV1>,
}

pub fn sectioned_owned_partitions(
    geometry: R0SectionedGeometry,
    owner: u32,
) -> Result<Vec<Vec<u8>>, R0PrototypeManifestError> {
    if !geometry.owners().contains(&owner) {
        return Err(R0PrototypeManifestError(format!(
            "invalid sectioned owner {owner} for {}",
            geometry.as_str()
        )));
    }
    let triplet = |selector: u32| {
        let base = u8::try_from(3 * selector).expect("sectioned selector is bounded");
        vec![base, base + 1, base + 2]
    };
    Ok(match geometry {
        R0SectionedGeometry::Wide9 | R0SectionedGeometry::Split3 => vec![triplet(owner)],
        R0SectionedGeometry::Serial3Low => {
            vec![
                triplet(3 * owner),
                triplet(3 * owner + 1),
                triplet(3 * owner + 2),
            ]
        }
        R0SectionedGeometry::Serial3High => vec![(0..9)
            .map(|within_owner| u8::try_from(9 * owner + within_owner).unwrap())
            .collect()],
    })
}

pub fn build_r0_sectioned_manifest() -> Result<R0SectionedManifestV1, R0PrototypeManifestError> {
    let mut symbols = Vec::with_capacity(60);
    let shapes =
        core::iter::once(None).chain(R0_SECTIONED_SPECIALIZED_SHAPES.into_iter().map(Some));
    for shape_bits in shapes {
        let shape_tag = shape_bits
            .map(|bits| format!("shape_{bits:03x}"))
            .unwrap_or_else(|| "universal".to_owned());
        let translation_unit = format!("native/generated/r0_sectioned_{shape_tag}.cu");
        for geometry in R0SectionedGeometry::ALL {
            let ownership = match geometry {
                R0SectionedGeometry::Wide9 | R0SectionedGeometry::Split3 => {
                    R0SectionedOwnership::SelectorTriplet
                }
                R0SectionedGeometry::Serial3Low | R0SectionedGeometry::Serial3High => {
                    R0SectionedOwnership::FixedX0
                }
            };
            symbols.push(R0SectionedSymbolV1 {
                candidate_id: format!("r0-sectioned/{shape_tag}/{}", geometry.as_str()),
                symbol: format!(
                    "ab_gkr_windowed_r0_sectioned_{shape_tag}_{}_kernel",
                    geometry.as_str()
                ),
                shape_bits,
                geometry,
                min_blocks: None,
                ownership,
                translation_unit: translation_unit.clone(),
                descriptor_kind: "r0_grouped_slot_ordinary".to_owned(),
            });
        }
    }
    symbols.sort_by(|left, right| left.candidate_id.cmp(&right.candidate_id));
    let manifest = R0SectionedManifestV1 {
        schema_version: 1,
        universal_shape: R0_SECTIONED_UNIVERSAL_SHAPE,
        specialized_shapes: R0_SECTIONED_SPECIALIZED_SHAPES,
        generic_reference_build: None,
        shape_dispatch: Vec::new(),
        symbols,
    };
    validate_r0_sectioned_manifest(&manifest)?;
    Ok(manifest)
}

pub fn validate_r0_sectioned_manifest(
    manifest: &R0SectionedManifestV1,
) -> Result<(), R0PrototypeManifestError> {
    if manifest.schema_version != 1
        || manifest.universal_shape != R0_SECTIONED_UNIVERSAL_SHAPE
        || manifest.specialized_shapes != R0_SECTIONED_SPECIALIZED_SHAPES
        || manifest.generic_reference_build.is_some()
        || !manifest.shape_dispatch.is_empty()
        || manifest.symbols.len() != 60
    {
        return Err(R0PrototypeManifestError(
            "sectioned manifest header/count mismatch".to_owned(),
        ));
    }
    validate_unique(
        "sectioned candidate id",
        manifest.symbols.iter().map(|row| row.candidate_id.as_str()),
    )?;
    validate_unique(
        "sectioned kernel symbol",
        manifest.symbols.iter().map(|row| row.symbol.as_str()),
    )?;
    for row in &manifest.symbols {
        if row.min_blocks.is_some() {
            return Err(R0PrototypeManifestError(format!(
                "schema-v1 sectioned row has launch bounds: {}",
                row.candidate_id
            )));
        }
        let expected_ownership = match row.geometry {
            R0SectionedGeometry::Wide9 | R0SectionedGeometry::Split3 => {
                R0SectionedOwnership::SelectorTriplet
            }
            R0SectionedGeometry::Serial3Low | R0SectionedGeometry::Serial3High => {
                R0SectionedOwnership::FixedX0
            }
        };
        if row.ownership != expected_ownership {
            return Err(R0PrototypeManifestError(format!(
                "sectioned ownership mismatch for {}: {:?} != {:?}",
                row.candidate_id, row.ownership, expected_ownership
            )));
        }
        if row.descriptor_kind != "r0_grouped_slot_ordinary" {
            return Err(R0PrototypeManifestError(format!(
                "sectioned descriptor mismatch for {}",
                row.candidate_id
            )));
        }
    }
    Ok(())
}

fn sectioned_bound_tag(min_blocks: Option<u32>) -> String {
    min_blocks.map_or_else(|| "natural".to_owned(), |value| format!("b{value}"))
}

fn sectioned_geometry_rank(geometry: R0SectionedGeometry) -> u8 {
    match geometry {
        R0SectionedGeometry::Wide9 => 0,
        R0SectionedGeometry::Split3 => 1,
        R0SectionedGeometry::Serial3Low => 2,
        R0SectionedGeometry::Serial3High => 3,
    }
}

fn sectioned_min_blocks_rank(min_blocks: Option<u32>) -> u32 {
    min_blocks.unwrap_or(0)
}

pub fn build_r0_sectioned_manifest_v2() -> Result<R0SectionedManifestV1, R0PrototypeManifestError> {
    let mut symbols = Vec::with_capacity(225);
    let shapes =
        core::iter::once(None).chain(R0_SECTIONED_SPECIALIZED_SHAPES.into_iter().map(Some));
    for shape_bits in shapes {
        let shape_tag = shape_bits
            .map(|bits| format!("shape_{bits:03x}"))
            .unwrap_or_else(|| "universal".to_owned());
        let translation_unit = format!("native/generated/r0_sectioned_{shape_tag}.cu");
        let mut push_candidate = |geometry: R0SectionedGeometry, min_blocks: Option<u32>| {
            let geometry_tag = geometry.as_str();
            let bound_tag = sectioned_bound_tag(min_blocks);
            let ownership = match geometry {
                R0SectionedGeometry::Wide9 | R0SectionedGeometry::Split3 => {
                    R0SectionedOwnership::SelectorTriplet
                }
                R0SectionedGeometry::Serial3Low => R0SectionedOwnership::FixedX0,
                R0SectionedGeometry::Serial3High => unreachable!("high3 is canary-only in v2"),
            };
            symbols.push(R0SectionedSymbolV1 {
                candidate_id: format!("r0-sectioned-v2/{shape_tag}/{geometry_tag}-{bound_tag}"),
                symbol: format!(
                    "ab_gkr_windowed_r0_sectioned_{shape_tag}_{geometry_tag}_{bound_tag}_kernel"
                ),
                shape_bits,
                geometry,
                min_blocks,
                ownership,
                translation_unit: translation_unit.clone(),
                descriptor_kind: "r0_grouped_slot_ordinary".to_owned(),
            });
        };
        push_candidate(R0SectionedGeometry::Wide9, Some(3));
        for geometry in [R0SectionedGeometry::Split3, R0SectionedGeometry::Serial3Low] {
            for min_blocks in R0_SECTIONED_SWEEP_MIN_BLOCKS {
                push_candidate(geometry, min_blocks);
            }
        }
    }
    symbols.sort_by_key(|row| {
        (
            row.shape_bits,
            sectioned_geometry_rank(row.geometry),
            sectioned_min_blocks_rank(row.min_blocks),
        )
    });
    let manifest = R0SectionedManifestV1 {
        schema_version: 2,
        universal_shape: R0_SECTIONED_UNIVERSAL_SHAPE,
        specialized_shapes: R0_SECTIONED_SPECIALIZED_SHAPES,
        generic_reference_build: Some(R0SectionedGenericBuildControlsV2 {
            min_blocks: None,
            maxreg: None,
        }),
        shape_dispatch: Vec::new(),
        symbols,
    };
    validate_r0_sectioned_manifest_v2(&manifest)?;
    Ok(manifest)
}

pub fn validate_r0_sectioned_manifest_v2(
    manifest: &R0SectionedManifestV1,
) -> Result<(), R0PrototypeManifestError> {
    if manifest.schema_version != 2
        || manifest.universal_shape != R0_SECTIONED_UNIVERSAL_SHAPE
        || manifest.specialized_shapes != R0_SECTIONED_SPECIALIZED_SHAPES
        || manifest.generic_reference_build
            != Some(R0SectionedGenericBuildControlsV2 {
                min_blocks: None,
                maxreg: None,
            })
        || !manifest.shape_dispatch.is_empty()
        || manifest.symbols.len() != 225
    {
        return Err(R0PrototypeManifestError(
            "sectioned schema-v2 header/count mismatch".to_owned(),
        ));
    }
    validate_unique(
        "sectioned schema-v2 candidate id",
        manifest.symbols.iter().map(|row| row.candidate_id.as_str()),
    )?;
    validate_unique(
        "sectioned schema-v2 kernel symbol",
        manifest.symbols.iter().map(|row| row.symbol.as_str()),
    )?;
    let mut keys = BTreeSet::new();
    for row in &manifest.symbols {
        if !keys.insert((row.shape_bits, row.geometry, row.min_blocks)) {
            return Err(R0PrototypeManifestError(format!(
                "duplicate sectioned schema-v2 key: {}",
                row.candidate_id
            )));
        }
        let valid_bound = match row.geometry {
            R0SectionedGeometry::Wide9 => row.min_blocks == Some(3),
            R0SectionedGeometry::Split3 | R0SectionedGeometry::Serial3Low => {
                R0_SECTIONED_SWEEP_MIN_BLOCKS.contains(&row.min_blocks)
            }
            R0SectionedGeometry::Serial3High => false,
        };
        if !valid_bound {
            return Err(R0PrototypeManifestError(format!(
                "invalid sectioned schema-v2 launch bound for {}",
                row.candidate_id
            )));
        }
        let expected_ownership = match row.geometry {
            R0SectionedGeometry::Wide9 | R0SectionedGeometry::Split3 => {
                R0SectionedOwnership::SelectorTriplet
            }
            R0SectionedGeometry::Serial3Low => R0SectionedOwnership::FixedX0,
            R0SectionedGeometry::Serial3High => unreachable!(),
        };
        let shape_tag = row
            .shape_bits
            .map(|bits| format!("shape_{bits:03x}"))
            .unwrap_or_else(|| "universal".to_owned());
        let geometry_tag = row.geometry.as_str();
        let bound_tag = sectioned_bound_tag(row.min_blocks);
        let expected_id = format!("r0-sectioned-v2/{shape_tag}/{geometry_tag}-{bound_tag}");
        let expected_symbol =
            format!("ab_gkr_windowed_r0_sectioned_{shape_tag}_{geometry_tag}_{bound_tag}_kernel");
        if row.ownership != expected_ownership
            || row.candidate_id != expected_id
            || row.symbol != expected_symbol
            || row.translation_unit != format!("native/generated/r0_sectioned_{shape_tag}.cu")
            || row.descriptor_kind != "r0_grouped_slot_ordinary"
        {
            return Err(R0PrototypeManifestError(format!(
                "sectioned schema-v2 row mismatch for {}",
                row.candidate_id
            )));
        }
    }
    let key = |row: &R0SectionedSymbolV1| {
        (
            row.shape_bits,
            sectioned_geometry_rank(row.geometry),
            sectioned_min_blocks_rank(row.min_blocks),
        )
    };
    if manifest
        .symbols
        .windows(2)
        .any(|pair| key(&pair[0]) >= key(&pair[1]))
    {
        return Err(R0PrototypeManifestError(
            "sectioned schema-v2 rows are not in canonical order".to_owned(),
        ));
    }
    Ok(())
}

pub fn build_r0_sectioned_manifest_v3() -> Result<R0SectionedManifestV1, R0PrototypeManifestError> {
    let mut symbols = Vec::with_capacity(240);
    let shapes =
        core::iter::once(None).chain(R0_SECTIONED_SPECIALIZED_SHAPES.into_iter().map(Some));
    for shape_bits in shapes {
        let shape_tag = shape_bits
            .map(|bits| format!("shape_{bits:03x}"))
            .unwrap_or_else(|| "universal".to_owned());
        let translation_unit = format!("native/generated/r0_sectioned_{shape_tag}.cu");
        let mut push_candidate = |geometry: R0SectionedGeometry, min_blocks: Option<u32>| {
            let geometry_tag = geometry.as_str();
            let bound_tag = sectioned_bound_tag(min_blocks);
            let ownership = match geometry {
                R0SectionedGeometry::Wide9 | R0SectionedGeometry::Split3 => {
                    R0SectionedOwnership::SelectorTriplet
                }
                R0SectionedGeometry::Serial3Low => R0SectionedOwnership::FixedX0,
                R0SectionedGeometry::Serial3High => unreachable!("high3 is canary-only"),
            };
            symbols.push(R0SectionedSymbolV1 {
                candidate_id: format!("r0-sectioned-v3/{shape_tag}/{geometry_tag}-{bound_tag}"),
                symbol: format!(
                    "ab_gkr_windowed_r0_sectioned_{shape_tag}_{geometry_tag}_{bound_tag}_kernel"
                ),
                shape_bits,
                geometry,
                min_blocks,
                ownership,
                translation_unit: translation_unit.clone(),
                descriptor_kind: "r0_grouped_slot_ordinary".to_owned(),
            });
        };
        for min_blocks in R0_SECTIONED_WIDE_MIN_BLOCKS_V3 {
            push_candidate(R0SectionedGeometry::Wide9, min_blocks);
        }
        for geometry in [R0SectionedGeometry::Split3, R0SectionedGeometry::Serial3Low] {
            for min_blocks in R0_SECTIONED_SWEEP_MIN_BLOCKS {
                push_candidate(geometry, min_blocks);
            }
        }
    }
    symbols.sort_by_key(|row| {
        (
            row.shape_bits,
            sectioned_geometry_rank(row.geometry),
            sectioned_min_blocks_rank(row.min_blocks),
        )
    });
    let manifest = R0SectionedManifestV1 {
        schema_version: 3,
        universal_shape: R0_SECTIONED_UNIVERSAL_SHAPE,
        specialized_shapes: R0_SECTIONED_SPECIALIZED_SHAPES,
        generic_reference_build: None,
        shape_dispatch: Vec::new(),
        symbols,
    };
    validate_r0_sectioned_manifest_v3(&manifest)?;
    Ok(manifest)
}

pub fn validate_r0_sectioned_manifest_v3(
    manifest: &R0SectionedManifestV1,
) -> Result<(), R0PrototypeManifestError> {
    if manifest.schema_version != 3
        || manifest.universal_shape != R0_SECTIONED_UNIVERSAL_SHAPE
        || manifest.specialized_shapes != R0_SECTIONED_SPECIALIZED_SHAPES
        || manifest.generic_reference_build.is_some()
        || !manifest.shape_dispatch.is_empty()
        || manifest.symbols.len() != 240
    {
        return Err(R0PrototypeManifestError(
            "sectioned schema-v3 header/count mismatch".to_owned(),
        ));
    }
    validate_unique(
        "sectioned schema-v3 candidate id",
        manifest.symbols.iter().map(|row| row.candidate_id.as_str()),
    )?;
    validate_unique(
        "sectioned schema-v3 kernel symbol",
        manifest.symbols.iter().map(|row| row.symbol.as_str()),
    )?;
    let mut keys = BTreeSet::new();
    for row in &manifest.symbols {
        if !keys.insert((row.shape_bits, row.geometry, row.min_blocks)) {
            return Err(R0PrototypeManifestError(format!(
                "duplicate sectioned schema-v3 key: {}",
                row.candidate_id
            )));
        }
        let valid_bound = match row.geometry {
            R0SectionedGeometry::Wide9 => R0_SECTIONED_WIDE_MIN_BLOCKS_V3.contains(&row.min_blocks),
            R0SectionedGeometry::Split3 | R0SectionedGeometry::Serial3Low => {
                R0_SECTIONED_SWEEP_MIN_BLOCKS.contains(&row.min_blocks)
            }
            R0SectionedGeometry::Serial3High => false,
        };
        if !valid_bound {
            return Err(R0PrototypeManifestError(format!(
                "invalid sectioned schema-v3 launch bound for {}",
                row.candidate_id
            )));
        }
        let expected_ownership = match row.geometry {
            R0SectionedGeometry::Wide9 | R0SectionedGeometry::Split3 => {
                R0SectionedOwnership::SelectorTriplet
            }
            R0SectionedGeometry::Serial3Low => R0SectionedOwnership::FixedX0,
            R0SectionedGeometry::Serial3High => unreachable!(),
        };
        let shape_tag = row
            .shape_bits
            .map(|bits| format!("shape_{bits:03x}"))
            .unwrap_or_else(|| "universal".to_owned());
        let geometry_tag = row.geometry.as_str();
        let bound_tag = sectioned_bound_tag(row.min_blocks);
        let expected_id = format!("r0-sectioned-v3/{shape_tag}/{geometry_tag}-{bound_tag}");
        let expected_symbol =
            format!("ab_gkr_windowed_r0_sectioned_{shape_tag}_{geometry_tag}_{bound_tag}_kernel");
        if row.ownership != expected_ownership
            || row.candidate_id != expected_id
            || row.symbol != expected_symbol
            || row.translation_unit != format!("native/generated/r0_sectioned_{shape_tag}.cu")
            || row.descriptor_kind != "r0_grouped_slot_ordinary"
        {
            return Err(R0PrototypeManifestError(format!(
                "sectioned schema-v3 row mismatch for {}",
                row.candidate_id
            )));
        }
    }
    let key = |row: &R0SectionedSymbolV1| {
        (
            row.shape_bits,
            sectioned_geometry_rank(row.geometry),
            sectioned_min_blocks_rank(row.min_blocks),
        )
    };
    if manifest
        .symbols
        .windows(2)
        .any(|pair| key(&pair[0]) >= key(&pair[1]))
    {
        return Err(R0PrototypeManifestError(
            "sectioned schema-v3 rows are not in canonical order".to_owned(),
        ));
    }
    Ok(())
}

pub fn build_r0_sectioned_manifest_v4() -> Result<R0SectionedManifestV1, R0PrototypeManifestError> {
    build_r0_sectioned_manifest_v4_for_merge_policy(R0SectionedShapeMergePolicy::Merged)
}

pub fn build_r0_sectioned_manifest_v4_for_merge_policy(
    merge_policy: R0SectionedShapeMergePolicy,
) -> Result<R0SectionedManifestV1, R0PrototypeManifestError> {
    let mut symbols = Vec::with_capacity(66);
    let compiled_shapes = match merge_policy {
        R0SectionedShapeMergePolicy::Exact => R0_SECTIONED_SPECIALIZED_SHAPES.to_vec(),
        R0SectionedShapeMergePolicy::Merged => R0_SECTIONED_COMPILED_SHAPES_V4.to_vec(),
        R0SectionedShapeMergePolicy::UnionBank => R0_SECTIONED_UNION_SHAPES_V1.to_vec(),
    };
    let symbol_shapes = match merge_policy {
        R0SectionedShapeMergePolicy::UnionBank => compiled_shapes
            .iter()
            .copied()
            .map(Some)
            .collect::<Vec<_>>(),
        R0SectionedShapeMergePolicy::Exact | R0SectionedShapeMergePolicy::Merged => {
            core::iter::once(None)
                .chain(compiled_shapes.iter().copied().map(Some))
                .collect()
        }
    };
    for shape_bits in symbol_shapes {
        let shape_tag = shape_bits
            .map(|bits| format!("shape_{bits:03x}"))
            .unwrap_or_else(|| "universal".to_owned());
        let translation_unit = format!("native/generated/r0_sectioned_{shape_tag}.cu");
        for min_blocks in R0_SECTIONED_WIDE_MIN_BLOCKS_V3 {
            let bound_tag = sectioned_bound_tag(min_blocks);
            symbols.push(R0SectionedSymbolV1 {
                candidate_id: format!("r0-sectioned-v4/{shape_tag}/wide9-{bound_tag}"),
                symbol: format!(
                    "ab_gkr_windowed_r0_sectioned_{shape_tag}_wide9_{bound_tag}_kernel"
                ),
                shape_bits,
                geometry: R0SectionedGeometry::Wide9,
                min_blocks,
                ownership: R0SectionedOwnership::SelectorTriplet,
                translation_unit: translation_unit.clone(),
                descriptor_kind: "r0_grouped_slot_ordinary".to_owned(),
            });
        }
    }
    symbols.sort_by_key(|row| (row.shape_bits, sectioned_min_blocks_rank(row.min_blocks)));
    let manifest = R0SectionedManifestV1 {
        schema_version: 4,
        universal_shape: R0_SECTIONED_UNIVERSAL_SHAPE,
        specialized_shapes: R0_SECTIONED_SPECIALIZED_SHAPES,
        generic_reference_build: None,
        shape_dispatch: match merge_policy {
            R0SectionedShapeMergePolicy::Exact => R0_SECTIONED_SPECIALIZED_SHAPES
                .into_iter()
                .map(|shape| R0SectionedShapeDispatchV4 {
                    input_shape: shape,
                    compiled_shape: shape,
                })
                .collect(),
            R0SectionedShapeMergePolicy::Merged => R0_SECTIONED_SHAPE_DISPATCH_V4
                .into_iter()
                .map(|(input_shape, compiled_shape)| R0SectionedShapeDispatchV4 {
                    input_shape,
                    compiled_shape,
                })
                .collect(),
            R0SectionedShapeMergePolicy::UnionBank => R0_SECTIONED_SPECIALIZED_SHAPES
                .into_iter()
                .map(|shape| R0SectionedShapeDispatchV4 {
                    input_shape: shape,
                    compiled_shape: shape,
                })
                .collect(),
        },
        symbols,
    };
    validate_r0_sectioned_manifest_v4(&manifest)?;
    Ok(manifest)
}

pub fn validate_r0_sectioned_manifest_v4(
    manifest: &R0SectionedManifestV1,
) -> Result<(), R0PrototypeManifestError> {
    let exact_dispatch = R0_SECTIONED_SPECIALIZED_SHAPES
        .into_iter()
        .map(|shape| (shape, shape))
        .collect::<Vec<_>>();
    let merged_dispatch = R0_SECTIONED_SHAPE_DISPATCH_V4.to_vec();
    let observed_dispatch = manifest
        .shape_dispatch
        .iter()
        .map(|row| (row.input_shape, row.compiled_shape))
        .collect::<Vec<_>>();
    let observed_symbol_shapes = manifest
        .symbols
        .iter()
        .filter_map(|row| row.shape_bits)
        .collect::<BTreeSet<_>>();
    let has_universal_symbol = manifest.symbols.iter().any(|row| row.shape_bits.is_none());
    let (compiled_shapes, expected_symbol_count) = if observed_dispatch == exact_dispatch
        && observed_symbol_shapes
            == R0_SECTIONED_UNION_SHAPES_V1
                .into_iter()
                .collect::<BTreeSet<_>>()
        && !has_universal_symbol
    {
        (R0_SECTIONED_UNION_SHAPES_V1.to_vec(), 66)
    } else if observed_dispatch == exact_dispatch {
        (R0_SECTIONED_SPECIALIZED_SHAPES.to_vec(), 30)
    } else if observed_dispatch == merged_dispatch {
        (R0_SECTIONED_COMPILED_SHAPES_V4.to_vec(), 26)
    } else {
        return Err(R0PrototypeManifestError(
            "sectioned schema-v4 shape dispatch mismatch".to_owned(),
        ));
    };
    if manifest.schema_version != 4
        || manifest.universal_shape != R0_SECTIONED_UNIVERSAL_SHAPE
        || manifest.specialized_shapes != R0_SECTIONED_SPECIALIZED_SHAPES
        || manifest.generic_reference_build.is_some()
        || manifest.symbols.len() != expected_symbol_count
        || manifest.shape_dispatch.len() != R0_SECTIONED_SPECIALIZED_SHAPES.len()
    {
        return Err(R0PrototypeManifestError(
            "sectioned schema-v4 header/count mismatch".to_owned(),
        ));
    }
    validate_unique(
        "sectioned schema-v4 candidate id",
        manifest.symbols.iter().map(|row| row.candidate_id.as_str()),
    )?;
    validate_unique(
        "sectioned schema-v4 kernel symbol",
        manifest.symbols.iter().map(|row| row.symbol.as_str()),
    )?;

    for row in &manifest.shape_dispatch {
        if row.input_shape & !row.compiled_shape != 0
            || !compiled_shapes.contains(&row.compiled_shape)
        {
            return Err(R0PrototypeManifestError(format!(
                "sectioned schema-v4 unsafe shape dispatch {:#05x} -> {:#05x}",
                row.input_shape, row.compiled_shape
            )));
        }
    }

    let mut keys = BTreeSet::new();
    for row in &manifest.symbols {
        if !keys.insert((row.shape_bits, row.min_blocks)) {
            return Err(R0PrototypeManifestError(format!(
                "duplicate sectioned schema-v4 key: {}",
                row.candidate_id
            )));
        }
        let shape_tag = row
            .shape_bits
            .map(|bits| format!("shape_{bits:03x}"))
            .unwrap_or_else(|| "universal".to_owned());
        let bound_tag = sectioned_bound_tag(row.min_blocks);
        if row.geometry != R0SectionedGeometry::Wide9
            || !R0_SECTIONED_WIDE_MIN_BLOCKS_V3.contains(&row.min_blocks)
            || row.ownership != R0SectionedOwnership::SelectorTriplet
            || row.candidate_id != format!("r0-sectioned-v4/{shape_tag}/wide9-{bound_tag}")
            || row.symbol
                != format!("ab_gkr_windowed_r0_sectioned_{shape_tag}_wide9_{bound_tag}_kernel")
            || row.translation_unit != format!("native/generated/r0_sectioned_{shape_tag}.cu")
            || row.descriptor_kind != "r0_grouped_slot_ordinary"
        {
            return Err(R0PrototypeManifestError(format!(
                "sectioned schema-v4 row mismatch for {}",
                row.candidate_id
            )));
        }
    }
    let expected_shape_keys = if has_universal_symbol {
        core::iter::once(None)
            .chain(compiled_shapes.into_iter().map(Some))
            .collect::<Vec<_>>()
    } else {
        compiled_shapes.into_iter().map(Some).collect()
    };
    let expected_keys = expected_shape_keys
        .into_iter()
        .flat_map(|shape| {
            R0_SECTIONED_WIDE_MIN_BLOCKS_V3
                .into_iter()
                .map(move |min_blocks| (shape, min_blocks))
        })
        .collect::<BTreeSet<_>>();
    if keys != expected_keys {
        return Err(R0PrototypeManifestError(
            "sectioned schema-v4 compiled symbol domain mismatch".to_owned(),
        ));
    }
    Ok(())
}

pub fn resolve_r0_sectioned_compiled_shape(
    manifest: &R0SectionedManifestV1,
    input_shape: u16,
) -> Result<u16, R0PrototypeManifestError> {
    if manifest.schema_version < 4 {
        return manifest
            .specialized_shapes
            .contains(&input_shape)
            .then_some(input_shape)
            .ok_or_else(|| {
                R0PrototypeManifestError(format!(
                    "unknown sectioned input shape {input_shape:#05x}"
                ))
            });
    }
    validate_r0_sectioned_manifest_v4(manifest)?;
    manifest
        .shape_dispatch
        .iter()
        .find(|row| row.input_shape == input_shape)
        .map(|row| row.compiled_shape)
        .ok_or_else(|| {
            R0PrototypeManifestError(format!("unknown sectioned input shape {input_shape:#05x}"))
        })
}

pub fn r0_sectioned_compatible_compiled_shapes(
    manifest: &R0SectionedManifestV1,
    input_shape: u16,
) -> Result<Vec<u16>, R0PrototypeManifestError> {
    validate_r0_sectioned_manifest_v4(manifest)?;
    if !R0_SECTIONED_SPECIALIZED_SHAPES.contains(&input_shape) {
        return Err(R0PrototypeManifestError(format!(
            "unknown sectioned input shape {input_shape:#05x}"
        )));
    }
    let compatible = manifest
        .symbols
        .iter()
        .filter_map(|row| row.shape_bits)
        .filter(|compiled_shape| input_shape & !compiled_shape == 0)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    if compatible.is_empty() {
        return Err(R0PrototypeManifestError(format!(
            "sectioned manifest has no compatible compiled shape for {input_shape:#05x}"
        )));
    }
    Ok(compatible)
}

pub fn r0_sectioned_shape_dispatch_is_allowed(input_shape: u16, compiled_shape: u16) -> bool {
    input_shape & !compiled_shape == 0
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R0ProgramEncoding {
    CurrentFixedSlot,
    CompactR0Port,
    SplitFixedSlot,
    SplitFixedDirect,
    HomogeneousSlot,
    HomogeneousDirect,
    GroupedSlot,
    GroupedDirect,
}

impl R0ProgramEncoding {
    pub const ALL: [Self; 8] = [
        Self::CurrentFixedSlot,
        Self::CompactR0Port,
        Self::SplitFixedSlot,
        Self::SplitFixedDirect,
        Self::HomogeneousSlot,
        Self::HomogeneousDirect,
        Self::GroupedSlot,
        Self::GroupedDirect,
    ];

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CurrentFixedSlot => "current_fixed_slot",
            Self::CompactR0Port => "compact_r0_port",
            Self::SplitFixedSlot => "split_fixed_slot",
            Self::SplitFixedDirect => "split_fixed_direct",
            Self::HomogeneousSlot => "homogeneous_slot",
            Self::HomogeneousDirect => "homogeneous_direct",
            Self::GroupedSlot => "grouped_slot",
            Self::GroupedDirect => "grouped_direct",
        }
    }

    pub const fn grouped(self) -> bool {
        matches!(self, Self::GroupedSlot | Self::GroupedDirect)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R0InnerFold {
    Canonical,
    U64,
}

impl R0InnerFold {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Canonical => "canonical",
            Self::U64 => "u64",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R0OuterFold {
    Canonical,
    U64,
    U96,
}

impl R0OuterFold {
    pub const ALL: [Self; 3] = [Self::Canonical, Self::U64, Self::U96];

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Canonical => "canonical",
            Self::U64 => "u64",
            Self::U96 => "u96",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R0SourcePolicy {
    Ordinary,
    Materialized,
}

impl R0SourcePolicy {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Ordinary => "ordinary",
            Self::Materialized => "materialized",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R0Lineage {
    Template,
    Reference,
}

impl R0Lineage {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Template => "template",
            Self::Reference => "reference",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0CandidateSymbolV1 {
    pub candidate_id: String,
    pub symbol: String,
    pub encoding: R0ProgramEncoding,
    pub inner: R0InnerFold,
    pub outer: R0OuterFold,
    pub geometry: R0Geometry,
    pub source_policy: R0SourcePolicy,
    pub lineage: R0Lineage,
    pub translation_unit: String,
    pub descriptor_kind: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0MeasurementConfigV1 {
    pub configuration_id: String,
    pub candidate_id: String,
    pub tile_capacity: Option<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0TranslationUnitV1 {
    pub translation_unit_id: String,
    pub source_path: String,
    pub encoding: R0ProgramEncoding,
    pub inner: R0InnerFold,
    pub outer: R0OuterFold,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0PrototypeManifestV1 {
    pub schema_version: u32,
    pub translation_units: Vec<R0TranslationUnitV1>,
    pub symbols: Vec<R0CandidateSymbolV1>,
    pub configurations: Vec<R0MeasurementConfigV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R0GeneratedFile {
    pub relative_path: String,
    pub contents: Vec<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum R0GeneratedMode {
    Write,
    Check,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R0GeneratedSync {
    pub files: usize,
    pub manifest_sha256: String,
}

impl R0GeneratedFile {
    pub fn text(&self) -> Result<&str, R0PrototypeManifestError> {
        core::str::from_utf8(&self.contents).map_err(|error| {
            R0PrototypeManifestError(format!(
                "generated file {} is not UTF-8: {error}",
                self.relative_path
            ))
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R0PrototypeManifestError(String);

impl core::fmt::Display for R0PrototypeManifestError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for R0PrototypeManifestError {}

pub fn build_r0_prototype_manifest() -> Result<R0PrototypeManifestV1, R0PrototypeManifestError> {
    let mut translation_units = Vec::with_capacity(30);
    let mut symbols = Vec::with_capacity(245);

    for encoding in R0ProgramEncoding::ALL {
        let inner_folds: &[R0InnerFold] = if encoding.grouped() {
            &[R0InnerFold::Canonical, R0InnerFold::U64]
        } else {
            &[R0InnerFold::Canonical]
        };
        for &inner in inner_folds {
            for outer in R0OuterFold::ALL {
                let source_path = format!(
                    "native/generated/r0_prototype_{}_{}_{}.cu",
                    encoding.as_str(),
                    inner.as_str(),
                    outer.as_str()
                );
                let translation_unit_id = format!(
                    "r0pb-tu/{}/{}/{}",
                    encoding.as_str(),
                    inner.as_str(),
                    outer.as_str()
                );
                translation_units.push(R0TranslationUnitV1 {
                    translation_unit_id,
                    source_path: source_path.clone(),
                    encoding,
                    inner,
                    outer,
                });

                for geometry in R0Geometry::ALL {
                    symbols.push(candidate_symbol(
                        encoding,
                        inner,
                        outer,
                        geometry,
                        R0SourcePolicy::Ordinary,
                        R0Lineage::Template,
                        source_path.clone(),
                    ));
                }
                for geometry in [
                    R0Geometry::Cta288Pair,
                    R0Geometry::Cta96Partitioned,
                    R0Geometry::Cta96X2Major,
                ] {
                    symbols.push(candidate_symbol(
                        encoding,
                        inner,
                        outer,
                        geometry,
                        R0SourcePolicy::Materialized,
                        R0Lineage::Template,
                        source_path.clone(),
                    ));
                }
            }
        }
    }

    for geometry in R0Geometry::ALL {
        symbols.push(candidate_symbol(
            R0ProgramEncoding::CurrentFixedSlot,
            R0InnerFold::Canonical,
            R0OuterFold::Canonical,
            geometry,
            R0SourcePolicy::Ordinary,
            R0Lineage::Reference,
            "existing_reference".to_owned(),
        ));
    }

    translation_units.sort_by(|left, right| left.source_path.cmp(&right.source_path));
    symbols.sort_by(|left, right| left.candidate_id.cmp(&right.candidate_id));
    let mut configurations = Vec::with_capacity(425);
    for symbol in &symbols {
        match symbol.source_policy {
            R0SourcePolicy::Ordinary => configurations.push(R0MeasurementConfigV1 {
                configuration_id: symbol.candidate_id.clone(),
                candidate_id: symbol.candidate_id.clone(),
                tile_capacity: None,
            }),
            R0SourcePolicy::Materialized => {
                for capacity in R0_PROTOTYPE_TILE_CAPACITIES {
                    configurations.push(R0MeasurementConfigV1 {
                        configuration_id: format!(
                            "r0pb-config/{}/cap{capacity}",
                            symbol.candidate_id
                        ),
                        candidate_id: symbol.candidate_id.clone(),
                        tile_capacity: Some(capacity),
                    });
                }
            }
        }
    }

    validate_unique(
        "candidate id",
        symbols.iter().map(|row| row.candidate_id.as_str()),
    )?;
    validate_unique(
        "kernel symbol",
        symbols.iter().map(|row| row.symbol.as_str()),
    )?;
    validate_unique(
        "configuration id",
        configurations
            .iter()
            .map(|row| row.configuration_id.as_str()),
    )?;
    validate_unique(
        "translation unit",
        translation_units.iter().map(|row| row.source_path.as_str()),
    )?;

    let manifest = R0PrototypeManifestV1 {
        schema_version: R0_PROTOTYPE_MANIFEST_VERSION,
        translation_units,
        symbols,
        configurations,
    };
    if manifest.translation_units.len() != 30
        || manifest.symbols.len() != 245
        || manifest.configurations.len() != 425
    {
        return Err(R0PrototypeManifestError(format!(
            "prototype manifest count mismatch: translation_units={} symbols={} configurations={}",
            manifest.translation_units.len(),
            manifest.symbols.len(),
            manifest.configurations.len()
        )));
    }
    Ok(manifest)
}

pub fn render_r0_prototype_generated_files(
) -> Result<Vec<R0GeneratedFile>, R0PrototypeManifestError> {
    render_r0_prototype_generated_files_for_merge_policy(R0SectionedShapeMergePolicy::Merged)
}

pub fn render_r0_prototype_generated_files_for_merge_policy(
    merge_policy: R0SectionedShapeMergePolicy,
) -> Result<Vec<R0GeneratedFile>, R0PrototypeManifestError> {
    let manifest = build_r0_prototype_manifest()?;
    let sectioned_manifest = build_r0_sectioned_manifest_v4_for_merge_policy(merge_policy)?;
    let mut manifest_json = serde_json::to_vec_pretty(&manifest).map_err(|error| {
        R0PrototypeManifestError(format!("serialize prototype manifest: {error}"))
    })?;
    manifest_json.push(b'\n');
    let manifest_sha256 = sha256_bytes(&manifest_json)?;
    let mut sectioned_manifest_json =
        serde_json::to_vec_pretty(&sectioned_manifest).map_err(|error| {
            R0PrototypeManifestError(format!("serialize sectioned manifest: {error}"))
        })?;
    sectioned_manifest_json.push(b'\n');
    let sectioned_manifest_sha256 = sha256_bytes(&sectioned_manifest_json)?;

    let mut files = vec![R0GeneratedFile {
        relative_path: "artifacts/windowed_r0_prototype_manifest_v1.json".to_owned(),
        contents: manifest_json,
    }];
    files.push(R0GeneratedFile {
        relative_path: "artifacts/windowed_r0_prototype_capacity_v1.json".to_owned(),
        contents: crate::r0_prototype_encoding::render_r0_prototype_capacity_json()
            .map_err(R0PrototypeManifestError)?,
    });
    files.push(R0GeneratedFile {
        relative_path: "src/generated/r0_prototype_registry.rs".to_owned(),
        contents: render_rust_registry(&manifest, &manifest_sha256).into_bytes(),
    });
    files.push(R0GeneratedFile {
        relative_path: "artifacts/windowed_r0_sectioned_manifest_v4.json".to_owned(),
        contents: sectioned_manifest_json,
    });
    files.push(R0GeneratedFile {
        relative_path: "src/generated/r0_sectioned_registry.rs".to_owned(),
        contents: render_sectioned_rust_registry(
            &sectioned_manifest,
            &sectioned_manifest_sha256,
            merge_policy,
        )
        .into_bytes(),
    });
    files.push(R0GeneratedFile {
        relative_path: "native/generated/windowed_r0_prototype_manifest.cuh".to_owned(),
        contents: render_cuda_manifest(&manifest_sha256).into_bytes(),
    });
    files.push(R0GeneratedFile {
        relative_path: "native/generated/windowed_r0_prototype_sources.cmake".to_owned(),
        contents: render_cmake_sources(&manifest, &sectioned_manifest).into_bytes(),
    });
    files.push(R0GeneratedFile {
        relative_path: "native/generated/windowed_r0_sectioned_manifest.cuh".to_owned(),
        contents: render_sectioned_cuda_manifest(&sectioned_manifest, &sectioned_manifest_sha256)
            .into_bytes(),
    });
    for unit in &manifest.translation_units {
        let source = render_translation_unit(&manifest, unit);
        files.push(R0GeneratedFile {
            relative_path: unit.source_path.clone(),
            contents: clang_format_generated_cuda(&unit.source_path, &source)?,
        });
    }
    let compiled_shapes = match merge_policy {
        R0SectionedShapeMergePolicy::Exact => R0_SECTIONED_SPECIALIZED_SHAPES.to_vec(),
        R0SectionedShapeMergePolicy::Merged => R0_SECTIONED_COMPILED_SHAPES_V4.to_vec(),
        R0SectionedShapeMergePolicy::UnionBank => R0_SECTIONED_UNION_SHAPES_V1.to_vec(),
    };
    let symbol_shapes = match merge_policy {
        R0SectionedShapeMergePolicy::UnionBank => {
            compiled_shapes.into_iter().map(Some).collect::<Vec<_>>()
        }
        R0SectionedShapeMergePolicy::Exact | R0SectionedShapeMergePolicy::Merged => {
            core::iter::once(None)
                .chain(compiled_shapes.into_iter().map(Some))
                .collect()
        }
    };
    for shape_bits in symbol_shapes {
        let shape_tag = sectioned_shape_tag(shape_bits);
        let relative_path = format!("native/generated/r0_sectioned_{shape_tag}.cu");
        let source = render_sectioned_translation_unit(&sectioned_manifest, shape_bits);
        files.push(R0GeneratedFile {
            relative_path: relative_path.clone(),
            contents: clang_format_generated_cuda(&relative_path, &source)?,
        });
    }
    files.sort_by(|left, right| left.relative_path.cmp(&right.relative_path));
    validate_unique(
        "generated path",
        files.iter().map(|file| file.relative_path.as_str()),
    )?;
    let expected_files = match merge_policy {
        R0SectionedShapeMergePolicy::Exact => 53,
        R0SectionedShapeMergePolicy::Merged => 51,
        R0SectionedShapeMergePolicy::UnionBank => 71,
    };
    if files.len() != expected_files {
        return Err(R0PrototypeManifestError(format!(
            "generated file count mismatch: expected {expected_files}, got {}",
            files.len()
        )));
    }
    Ok(files)
}

pub fn sync_r0_prototype_generated_files(
    crate_root: &Path,
    mode: R0GeneratedMode,
) -> Result<R0GeneratedSync, R0PrototypeManifestError> {
    sync_r0_prototype_generated_files_for_merge_policy(
        crate_root,
        mode,
        R0SectionedShapeMergePolicy::Merged,
    )
}

pub fn sync_r0_prototype_generated_files_for_merge_policy(
    crate_root: &Path,
    mode: R0GeneratedMode,
    merge_policy: R0SectionedShapeMergePolicy,
) -> Result<R0GeneratedSync, R0PrototypeManifestError> {
    let files = render_r0_prototype_generated_files_for_merge_policy(merge_policy)?;
    for file in &files {
        let relative = checked_relative_path(&file.relative_path)?;
        let destination = crate_root.join(relative);
        match mode {
            R0GeneratedMode::Write => atomic_write(&destination, &file.contents)?,
            R0GeneratedMode::Check => {
                let actual = fs::read(&destination).map_err(|error| {
                    R0PrototypeManifestError(format!(
                        "read generated file {}: {error}",
                        destination.display()
                    ))
                })?;
                if actual != file.contents {
                    return Err(R0PrototypeManifestError(format!(
                        "generated file {} differs from generated bytes",
                        destination.display()
                    )));
                }
            }
        }
    }
    let manifest = files
        .iter()
        .find(|file| file.relative_path == "artifacts/windowed_r0_prototype_manifest_v1.json")
        .ok_or_else(|| R0PrototypeManifestError("generated manifest is absent".to_owned()))?;
    Ok(R0GeneratedSync {
        files: files.len(),
        manifest_sha256: sha256_bytes(&manifest.contents)?,
    })
}

pub fn parse_r0_prototype_generator_mode<I, S>(
    args: I,
) -> Result<R0GeneratedMode, R0PrototypeManifestError>
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    let args = args
        .into_iter()
        .map(|value| value.as_ref().to_owned())
        .collect::<Vec<_>>();
    match args.as_slice() {
        [value] if value == "--write" => Ok(R0GeneratedMode::Write),
        [value] if value == "--check" => Ok(R0GeneratedMode::Check),
        _ => Err(R0PrototypeManifestError(
            "expected exactly one of --write or --check".to_owned(),
        )),
    }
}

fn checked_relative_path(value: &str) -> Result<&Path, R0PrototypeManifestError> {
    let path = Path::new(value);
    if value.is_empty()
        || path.is_absolute()
        || path
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(R0PrototypeManifestError(format!(
            "generated path is not a normalized relative path: {value:?}"
        )));
    }
    Ok(path)
}

fn atomic_write(path: &Path, bytes: &[u8]) -> Result<(), R0PrototypeManifestError> {
    let parent = path.parent().ok_or_else(|| {
        R0PrototypeManifestError(format!("generated path has no parent: {}", path.display()))
    })?;
    fs::create_dir_all(parent).map_err(|error| {
        R0PrototypeManifestError(format!("create {}: {error}", parent.display()))
    })?;
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| {
            R0PrototypeManifestError(format!(
                "generated path has invalid name: {}",
                path.display()
            ))
        })?;
    let counter = GENERATED_TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temporary = parent.join(format!(".{file_name}.tmp-{}-{counter}", std::process::id()));
    let write_result = (|| {
        let mut file = OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(&temporary)
            .map_err(|error| {
                R0PrototypeManifestError(format!(
                    "create temporary generated file {}: {error}",
                    temporary.display()
                ))
            })?;
        file.write_all(bytes).map_err(|error| {
            R0PrototypeManifestError(format!(
                "write temporary generated file {}: {error}",
                temporary.display()
            ))
        })?;
        file.sync_all().map_err(|error| {
            R0PrototypeManifestError(format!(
                "sync temporary generated file {}: {error}",
                temporary.display()
            ))
        })?;
        fs::rename(&temporary, path).map_err(|error| {
            R0PrototypeManifestError(format!(
                "publish generated file {}: {error}",
                path.display()
            ))
        })?;
        Ok(())
    })();
    if write_result.is_err() {
        let _ = fs::remove_file(&temporary);
    }
    write_result
}

fn rust_descriptor_binding(
    encoding: R0ProgramEncoding,
    source: R0SourcePolicy,
) -> (&'static str, &'static str, &'static str) {
    match (encoding, source) {
        (R0ProgramEncoding::CurrentFixedSlot, R0SourcePolicy::Ordinary) => (
            "R0PbCurrentFixedSlotOrdinary",
            "R0VmDesc",
            "CurrentOrdinary",
        ),
        (R0ProgramEncoding::CompactR0Port, R0SourcePolicy::Ordinary) => (
            "R0PbCompactR0PortOrdinary",
            "R0CompactOrdinaryDesc",
            "CompactOrdinary",
        ),
        (R0ProgramEncoding::SplitFixedSlot, R0SourcePolicy::Ordinary) => (
            "R0PbSplitFixedSlotOrdinary",
            "R0SplitSlotOrdinaryDesc",
            "SplitSlotOrdinary",
        ),
        (R0ProgramEncoding::SplitFixedDirect, R0SourcePolicy::Ordinary) => (
            "R0PbSplitFixedDirectOrdinary",
            "R0SplitDirectOrdinaryDesc",
            "SplitDirectOrdinary",
        ),
        (R0ProgramEncoding::HomogeneousSlot, R0SourcePolicy::Ordinary) => (
            "R0PbHomogeneousSlotOrdinary",
            "R0HomogeneousSlotOrdinaryDesc",
            "HomogeneousSlotOrdinary",
        ),
        (R0ProgramEncoding::HomogeneousDirect, R0SourcePolicy::Ordinary) => (
            "R0PbHomogeneousDirectOrdinary",
            "R0HomogeneousDirectOrdinaryDesc",
            "HomogeneousDirectOrdinary",
        ),
        (R0ProgramEncoding::GroupedSlot, R0SourcePolicy::Ordinary) => (
            "R0PbGroupedSlotOrdinary",
            "R0GroupedSlotOrdinaryDesc",
            "GroupedSlotOrdinary",
        ),
        (R0ProgramEncoding::GroupedDirect, R0SourcePolicy::Ordinary) => (
            "R0PbGroupedDirectOrdinary",
            "R0GroupedDirectOrdinaryDesc",
            "GroupedDirectOrdinary",
        ),
        (R0ProgramEncoding::CurrentFixedSlot, R0SourcePolicy::Materialized) => (
            "R0PbCurrentFixedSlotMaterialized",
            "R0CurrentMaterializedDesc",
            "CurrentMaterialized",
        ),
        (R0ProgramEncoding::CompactR0Port, R0SourcePolicy::Materialized) => (
            "R0PbCompactR0PortMaterialized",
            "R0CompactMaterializedDesc",
            "CompactMaterialized",
        ),
        (R0ProgramEncoding::SplitFixedSlot, R0SourcePolicy::Materialized) => (
            "R0PbSplitFixedSlotMaterialized",
            "R0SplitSlotMaterializedDesc",
            "SplitSlotMaterialized",
        ),
        (R0ProgramEncoding::SplitFixedDirect, R0SourcePolicy::Materialized) => (
            "R0PbSplitFixedDirectMaterialized",
            "R0SplitDirectMaterializedDesc",
            "SplitDirectMaterialized",
        ),
        (R0ProgramEncoding::HomogeneousSlot, R0SourcePolicy::Materialized) => (
            "R0PbHomogeneousSlotMaterialized",
            "R0HomogeneousSlotMaterializedDesc",
            "HomogeneousSlotMaterialized",
        ),
        (R0ProgramEncoding::HomogeneousDirect, R0SourcePolicy::Materialized) => (
            "R0PbHomogeneousDirectMaterialized",
            "R0HomogeneousDirectMaterializedDesc",
            "HomogeneousDirectMaterialized",
        ),
        (R0ProgramEncoding::GroupedSlot, R0SourcePolicy::Materialized) => (
            "R0PbGroupedSlotMaterialized",
            "R0GroupedSlotMaterializedDesc",
            "GroupedSlotMaterialized",
        ),
        (R0ProgramEncoding::GroupedDirect, R0SourcePolicy::Materialized) => (
            "R0PbGroupedDirectMaterialized",
            "R0GroupedDirectMaterializedDesc",
            "GroupedDirectMaterialized",
        ),
    }
}

fn render_rust_registry(manifest: &R0PrototypeManifestV1, manifest_sha256: &str) -> String {
    let mut output =
        String::from("// @generated by generate_windowed_r0_prototype_bank; do not edit.\n\n");
    output.push_str(
        concat!(
            "use era_cudart::execution::{CudaLaunchConfig, KernelFunction};\n",
            "use era_cudart::result::{CudaResult, CudaResultWrap};\n",
            "use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};\n",
            "use era_cudart_sys::{cudaFuncSetAttribute, CudaError, CudaFuncAttribute};\n\n",
            "use crate::r0_abi::R0VmDesc;\n",
            "use crate::r0_prototype_abi::{\n",
            "    R0CompactMaterializedDesc, R0CompactOrdinaryDesc, R0CurrentMaterializedDesc,\n",
            "    R0GroupedDirectMaterializedDesc, R0GroupedDirectOrdinaryDesc,\n",
            "    R0GroupedSlotMaterializedDesc, R0GroupedSlotOrdinaryDesc,\n",
            "    R0HomogeneousDirectMaterializedDesc, R0HomogeneousDirectOrdinaryDesc,\n",
            "    R0HomogeneousSlotMaterializedDesc, R0HomogeneousSlotOrdinaryDesc,\n",
            "    R0PrototypePayload, R0SplitDirectMaterializedDesc, R0SplitDirectOrdinaryDesc,\n",
            "    R0SplitSlotMaterializedDesc, R0SplitSlotOrdinaryDesc,\n",
            "};\n",
            "use crate::r0_prototype_manifest::R0CandidateSymbolV1;\n\n",
        ),
    );
    output.push_str(&format!(
        "pub const R0_PROTOTYPE_MANIFEST_SHA256: &str = {manifest_sha256:?};\n\n"
    ));
    output.push_str("pub const R0_PROTOTYPE_CANDIDATE_IDS: [&str; 245] = [\n");
    for symbol in &manifest.symbols {
        output.push_str(&format!("    {:?},\n", symbol.candidate_id));
    }
    output.push_str("];\n\n");
    output.push_str("pub const R0_PROTOTYPE_CONFIGURATION_IDS: [&str; 425] = [\n");
    for configuration in &manifest.configurations {
        output.push_str(&format!("    {:?},\n", configuration.configuration_id));
    }
    output.push_str("];\n\n");

    for encoding in R0ProgramEncoding::ALL {
        for source in [R0SourcePolicy::Ordinary, R0SourcePolicy::Materialized] {
            let (signature, descriptor, _) = rust_descriptor_binding(encoding, source);
            output.push_str(&format!(
                "#[rustfmt::skip]\ncuda_kernel_signature_arguments_and_function!({signature}, desc: {descriptor},);\n"
            ));
        }
    }
    output.push('\n');
    for candidate in &manifest.symbols {
        output.push_str(&format!(
            "// R0PB-FFI candidate={} symbol={} descriptor={} geometry={} source={}\n",
            candidate.candidate_id,
            candidate.symbol,
            candidate.descriptor_kind,
            candidate.geometry.as_str(),
            candidate.source_policy.as_str(),
        ));
        if candidate.lineage == R0Lineage::Template {
            let (_, descriptor, _) =
                rust_descriptor_binding(candidate.encoding, candidate.source_policy);
            output.push_str(&format!(
                "#[rustfmt::skip]\ncuda_kernel_declaration!({}(desc: {descriptor},));\n",
                candidate.symbol
            ));
        }
    }
    output.push_str(concat!(
        "\nfn exact_candidate(\n",
        "    candidate: &R0CandidateSymbolV1,\n",
        "    symbol: &str,\n",
        "    encoding: &str,\n",
        "    inner: &str,\n",
        "    outer: &str,\n",
        "    geometry: &str,\n",
        "    source: &str,\n",
        "    lineage: &str,\n",
        "    translation_unit: &str,\n",
        "    descriptor_kind: &str,\n",
        ") -> bool {\n",
        "    candidate.symbol == symbol\n",
        "        && candidate.encoding.as_str() == encoding\n",
        "        && candidate.inner.as_str() == inner\n",
        "        && candidate.outer.as_str() == outer\n",
        "        && candidate.geometry.as_str() == geometry\n",
        "        && candidate.source_policy.as_str() == source\n",
        "        && candidate.lineage.as_str() == lineage\n",
        "        && candidate.translation_unit == translation_unit\n",
        "        && candidate.descriptor_kind == descriptor_kind\n",
        "}\n\n",
        "#[rustfmt::skip]\n",
        "pub(super) fn template_candidate_is_exact(candidate: &R0CandidateSymbolV1) -> bool {\n",
        "    match candidate.candidate_id.as_str() {\n",
    ));
    for candidate in manifest
        .symbols
        .iter()
        .filter(|candidate| candidate.lineage == R0Lineage::Template)
    {
        output.push_str(&format!(
            concat!(
                "        {:?} => exact_candidate(candidate, {:?}, {:?}, {:?}, {:?}, {:?}, {:?}, {:?}, {:?}, {:?}),\n"
            ),
            candidate.candidate_id,
            candidate.symbol,
            candidate.encoding.as_str(),
            candidate.inner.as_str(),
            candidate.outer.as_str(),
            candidate.geometry.as_str(),
            candidate.source_policy.as_str(),
            candidate.lineage.as_str(),
            candidate.translation_unit,
            candidate.descriptor_kind,
        ));
    }
    output.push_str(concat!(
        "        _ => false,\n",
        "    }\n",
        "}\n\n",
        "#[rustfmt::skip]\n",
        "pub(super) fn launch_template(\n",
        "    candidate: &R0CandidateSymbolV1,\n",
        "    payload: &R0PrototypePayload,\n",
        "    config: &CudaLaunchConfig<'_>,\n",
        ") -> CudaResult<()> {\n",
        "    match candidate.candidate_id.as_str() {\n",
    ));
    for candidate in manifest
        .symbols
        .iter()
        .filter(|candidate| candidate.lineage == R0Lineage::Template)
    {
        let (signature, _, payload) =
            rust_descriptor_binding(candidate.encoding, candidate.source_policy);
        output.push_str(&format!(
            concat!(
                "        {:?} if exact_candidate(candidate, {:?}, {:?}, {:?}, {:?}, {:?}, {:?}, {:?}, {:?}, {:?}) => {{\n",
                "            let R0PrototypePayload::{payload}(desc) = payload else {{ return Err(CudaError::ErrorInvalidValue); }};\n",
                "            let args = {signature}Arguments::new(*desc);\n",
                "            {signature}Function({}).launch(config, &args)\n",
                "        }}\n"
            ),
            candidate.candidate_id,
            candidate.symbol,
            candidate.encoding.as_str(),
            candidate.inner.as_str(),
            candidate.outer.as_str(),
            candidate.geometry.as_str(),
            candidate.source_policy.as_str(),
            candidate.lineage.as_str(),
            candidate.translation_unit,
            candidate.descriptor_kind,
            candidate.symbol,
            payload = payload,
            signature = signature,
        ));
    }
    output.push_str(
        concat!(
            "        _ => Err(CudaError::ErrorInvalidValue),\n",
            "    }\n",
            "}\n\n",
            "#[rustfmt::skip]\n",
            "pub(super) fn configure_materialized(\n",
            "    candidate: &R0CandidateSymbolV1,\n",
            "    dynamic_shared_bytes: u32,\n",
            ") -> CudaResult<()> {\n",
            "    let bytes = i32::try_from(dynamic_shared_bytes).map_err(|_| CudaError::ErrorInvalidValue)?;\n",
            "    let function = match candidate.candidate_id.as_str() {\n",
        ),
    );
    for candidate in manifest.symbols.iter().filter(|candidate| {
        candidate.lineage == R0Lineage::Template
            && candidate.source_policy == R0SourcePolicy::Materialized
    }) {
        let (signature, _, _) =
            rust_descriptor_binding(candidate.encoding, candidate.source_policy);
        output.push_str(&format!(
            concat!(
                "        {:?} if exact_candidate(candidate, {:?}, {:?}, {:?}, {:?}, {:?}, {:?}, {:?}, {:?}, {:?}) => {signature}Function({}).as_ptr(),\n"
            ),
            candidate.candidate_id,
            candidate.symbol,
            candidate.encoding.as_str(),
            candidate.inner.as_str(),
            candidate.outer.as_str(),
            candidate.geometry.as_str(),
            candidate.source_policy.as_str(),
            candidate.lineage.as_str(),
            candidate.translation_unit,
            candidate.descriptor_kind,
            candidate.symbol,
            signature = signature,
        ));
    }
    output.push_str(
        concat!(
            "        _ => return Err(CudaError::ErrorInvalidValue),\n",
            "    };\n",
            "    unsafe { cudaFuncSetAttribute(function, CudaFuncAttribute::MaxDynamicSharedMemorySize, bytes) }.wrap()\n",
            "}\n",
        ),
    );
    output
}

fn sectioned_shape_tag(shape_bits: Option<u16>) -> String {
    shape_bits
        .map(|bits| format!("shape_{bits:03x}"))
        .unwrap_or_else(|| "universal".to_owned())
}

fn render_sectioned_rust_registry(
    manifest: &R0SectionedManifestV1,
    manifest_sha256: &str,
    merge_policy: R0SectionedShapeMergePolicy,
) -> String {
    let mut output = String::from(concat!(
        "// @generated by generate_windowed_r0_prototype_bank; do not edit.\n\n",
        "use era_cudart::execution::{CudaLaunchConfig, KernelFunction};\n",
        "use era_cudart::result::{CudaResult, CudaResultWrap};\n",
        "use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};\n",
        "use era_cudart_sys::CudaError;\n\n",
        "use crate::r0_prototype_abi::R0GroupedSlotOrdinaryDesc;\n",
        "use crate::r0_prototype_manifest::{R0SectionedOwnership, R0SectionedSymbolV1};\n\n",
    ));
    output.push_str(&format!(
        "pub const R0_SECTIONED_MANIFEST_SHA256: &str = {manifest_sha256:?};\n\n"
    ));
    output.push_str(&format!(
        "pub const R0_SECTIONED_SHAPE_MERGE_POLICY: &str = {:?};\n\n",
        merge_policy.as_str(),
    ));
    output.push_str(&format!(
        "pub const R0_SECTIONED_CANDIDATE_IDS: [&str; {}] = [\n",
        manifest.symbols.len()
    ));
    for symbol in &manifest.symbols {
        output.push_str(&format!("    {:?},\n", symbol.candidate_id));
    }
    output.push_str("] ;\n\n");
    output.push_str(
        "#[rustfmt::skip]\ncuda_kernel_signature_arguments_and_function!(R0SectionedSignature, desc: R0GroupedSlotOrdinaryDesc,);\n\n",
    );
    for symbol in &manifest.symbols {
        output.push_str(&format!(
            "// R0-SECTIONED-FFI candidate={} symbol={} shape={:?} geometry={}\n",
            symbol.candidate_id,
            symbol.symbol,
            symbol.shape_bits,
            symbol.geometry.as_str(),
        ));
        output.push_str(&format!(
            "#[rustfmt::skip]\ncuda_kernel_declaration!({}(desc: R0GroupedSlotOrdinaryDesc,));\n",
            symbol.symbol
        ));
    }
    output.push_str(concat!(
        "\nfn exact_sectioned(\n",
        "    candidate: &R0SectionedSymbolV1,\n",
        "    symbol: &str,\n",
        "    shape_bits: Option<u16>,\n",
        "    geometry: &str,\n",
        "    min_blocks: Option<u32>,\n",
        "    ownership: R0SectionedOwnership,\n",
        "    translation_unit: &str,\n",
        ") -> bool {\n",
        "    candidate.symbol == symbol\n",
        "        && candidate.shape_bits == shape_bits\n",
        "        && candidate.geometry.as_str() == geometry\n",
        "        && candidate.min_blocks == min_blocks\n",
        "        && candidate.ownership == ownership\n",
        "        && candidate.translation_unit == translation_unit\n",
        "        && candidate.descriptor_kind == \"r0_grouped_slot_ordinary\"\n",
        "}\n\n",
        "#[rustfmt::skip]\n",
        "pub(super) fn sectioned_symbol_is_exact(candidate: &R0SectionedSymbolV1) -> bool {\n",
        "    match candidate.candidate_id.as_str() {\n",
    ));
    for symbol in &manifest.symbols {
        output.push_str(&format!(
            "        {:?} => exact_sectioned(candidate, {:?}, {:?}, {:?}, {:?}, R0SectionedOwnership::{:?}, {:?}),\n",
            symbol.candidate_id,
            symbol.symbol,
            symbol.shape_bits,
            symbol.geometry.as_str(),
            symbol.min_blocks,
            symbol.ownership,
            symbol.translation_unit,
        ));
    }
    output.push_str(concat!(
        "        _ => false,\n",
        "    }\n",
        "}\n\n",
        "#[rustfmt::skip]\n",
        "pub(super) fn launch_sectioned(\n",
        "    candidate: &R0SectionedSymbolV1,\n",
        "    desc: R0GroupedSlotOrdinaryDesc,\n",
        "    config: &CudaLaunchConfig<'_>,\n",
        ") -> CudaResult<()> {\n",
        "    let args = R0SectionedSignatureArguments::new(desc);\n",
        "    match candidate.candidate_id.as_str() {\n",
    ));
    for symbol in &manifest.symbols {
        output.push_str(&format!(
            "        {:?} if exact_sectioned(candidate, {:?}, {:?}, {:?}, {:?}, R0SectionedOwnership::{:?}, {:?}) => R0SectionedSignatureFunction({}).launch(config, &args),\n",
            symbol.candidate_id,
            symbol.symbol,
            symbol.shape_bits,
            symbol.geometry.as_str(),
            symbol.min_blocks,
            symbol.ownership,
            symbol.translation_unit,
            symbol.symbol,
        ));
    }
    output.push_str(concat!(
        "        _ => Err(CudaError::ErrorInvalidValue),\n",
        "    }\n",
        "}\n",
    ));
    output
}

fn render_sectioned_cuda_manifest(
    manifest: &R0SectionedManifestV1,
    manifest_sha256: &str,
) -> String {
    format!(
        concat!(
            "// @generated by generate_windowed_r0_prototype_bank; do not edit.\n",
            "#pragma once\n\n",
            "namespace airbender::gkr_windowed_bench {{\n",
            "inline constexpr char R0_SECTIONED_MANIFEST_SHA256[] = \"{}\";\n",
            "inline constexpr unsigned R0_SECTIONED_SYMBOL_COUNT = {};\n",
            "}} // namespace airbender::gkr_windowed_bench\n"
        ),
        manifest_sha256,
        manifest.symbols.len(),
    )
}

fn render_sectioned_translation_unit(
    manifest: &R0SectionedManifestV1,
    shape_bits: Option<u16>,
) -> String {
    let shape_tag = sectioned_shape_tag(shape_bits);
    let compiled_shape = shape_bits.unwrap_or(manifest.universal_shape);
    let mut output = String::from(concat!(
        "// @generated by generate_windowed_r0_prototype_bank; do not edit.\n",
        "#include \"../windowed_r0_prototype_dedicated_control.cuh\"\n",
        "#include \"windowed_r0_sectioned_manifest.cuh\"\n\n",
        "namespace airbender::gkr_windowed_bench {\n\n",
    ));
    for symbol in manifest
        .symbols
        .iter()
        .filter(|symbol| symbol.shape_bits == shape_bits)
    {
        let invocation = match (symbol.geometry, symbol.min_blocks) {
            (R0SectionedGeometry::Wide9, Some(min_blocks)) => format!(
                "AB_R0PB_DEFINE_SECTIONED_WIDE9_BOUNDED_KERNEL({}, 0x{compiled_shape:03x}, {min_blocks});\n",
                symbol.symbol,
            ),
            (R0SectionedGeometry::Split3, None) => format!(
                "AB_R0PB_DEFINE_SECTIONED_SPLIT3_KERNEL({}, 0x{compiled_shape:03x});\n",
                symbol.symbol
            ),
            (R0SectionedGeometry::Split3, Some(min_blocks)) => format!(
                "AB_R0PB_DEFINE_SECTIONED_SPLIT3_BOUNDED_KERNEL({}, 0x{compiled_shape:03x}, {min_blocks});\n",
                symbol.symbol
            ),
            (R0SectionedGeometry::Serial3Low, None) => format!(
                "AB_R0PB_DEFINE_SECTIONED_SERIAL3_LOW_KERNEL({}, 0x{compiled_shape:03x});\n",
                symbol.symbol
            ),
            (R0SectionedGeometry::Serial3Low, Some(min_blocks)) => format!(
                "AB_R0PB_DEFINE_SECTIONED_SERIAL3_LOW_BOUNDED_KERNEL({}, 0x{compiled_shape:03x}, {min_blocks});\n",
                symbol.symbol
            ),
            _ => unreachable!("validated sectioned schema-v2 candidate"),
        };
        output.push_str(&invocation);
    }
    output.push_str(&format!(
        "\nstatic_assert(R0_SECTIONED_SYMBOL_COUNT == {}, \"{shape_tag} sectioned manifest mismatch\");\n",
        manifest.symbols.len()
    ));
    output.push_str("\n} // namespace airbender::gkr_windowed_bench\n");
    output
}

fn render_cuda_manifest(manifest_sha256: &str) -> String {
    format!(
        concat!(
            "// @generated by generate_windowed_r0_prototype_bank; do not edit.\n",
            "#pragma once\n\n",
            "namespace airbender::gkr_windowed_bench {{\n",
            "inline constexpr char R0_PROTOTYPE_MANIFEST_SHA256[] = \"{}\";\n",
            "inline constexpr unsigned R0_PROTOTYPE_SYMBOL_COUNT = 245;\n",
            "inline constexpr unsigned R0_PROTOTYPE_CONFIGURATION_COUNT = 425;\n",
            "}} // namespace airbender::gkr_windowed_bench\n\n",
            "#define AB_R0PB_ENCODING_CURRENT_FIXED_SLOT 0\n",
            "#define AB_R0PB_ENCODING_COMPACT_R0_PORT 1\n",
            "#define AB_R0PB_ENCODING_SPLIT_FIXED_SLOT 2\n",
            "#define AB_R0PB_ENCODING_SPLIT_FIXED_DIRECT 3\n",
            "#define AB_R0PB_ENCODING_HOMOGENEOUS_SLOT 4\n",
            "#define AB_R0PB_ENCODING_HOMOGENEOUS_DIRECT 5\n",
            "#define AB_R0PB_ENCODING_GROUPED_SLOT 6\n",
            "#define AB_R0PB_ENCODING_GROUPED_DIRECT 7\n",
            "#define AB_R0PB_INNER_CANONICAL 0\n",
            "#define AB_R0PB_INNER_U64 1\n",
            "#define AB_R0PB_OUTER_CANONICAL 0\n",
            "#define AB_R0PB_OUTER_U64 1\n",
            "#define AB_R0PB_OUTER_U96 2\n"
        ),
        manifest_sha256
    )
}

fn render_cmake_sources(
    manifest: &R0PrototypeManifestV1,
    sectioned_manifest: &R0SectionedManifestV1,
) -> String {
    let mut output = String::from(
        "# @generated by generate_windowed_r0_prototype_bank; do not edit.\nset(GPU_GKR_WINDOWED_R0_PROTOTYPE_SOURCES\n",
    );
    for unit in &manifest.translation_units {
        let file_name = unit
            .source_path
            .rsplit('/')
            .next()
            .expect("generated translation-unit path has a file name");
        output.push_str(&format!(
            "        ${{CMAKE_CURRENT_LIST_DIR}}/{file_name}\n"
        ));
    }
    let sectioned_units = sectioned_manifest
        .symbols
        .iter()
        .map(|symbol| symbol.translation_unit.as_str())
        .collect::<BTreeSet<_>>();
    for source_path in sectioned_units {
        let file_name = Path::new(source_path)
            .file_name()
            .and_then(|name| name.to_str())
            .expect("sectioned translation-unit path has a file name");
        output.push_str(&format!(
            "        ${{CMAKE_CURRENT_LIST_DIR}}/{file_name}\n"
        ));
    }
    output.push_str(")\n");
    output
}

fn render_translation_unit(manifest: &R0PrototypeManifestV1, unit: &R0TranslationUnitV1) -> String {
    let header = if unit.encoding == R0ProgramEncoding::GroupedSlot
        && unit.inner == R0InnerFold::U64
        && unit.outer == R0OuterFold::U96
    {
        "windowed_r0_prototype_dedicated_control.cuh"
    } else {
        "windowed_r0_prototype_kernel.cuh"
    };
    let mut output = format!(
        concat!(
            "// @generated by generate_windowed_r0_prototype_bank; do not edit.\n",
            "#include \"../{}\"\n\n",
            "namespace airbender::gkr_windowed_bench {{\n\n",
            "using r0pb_cursor = r0pb_{}_cursor;\n",
            "using r0pb_inner = r0pb_inner_{};\n",
            "using r0pb_outer = r0pb_outer_{};\n\n"
        ),
        header,
        unit.encoding.as_str(),
        unit.inner.as_str(),
        unit.outer.as_str()
    );
    let mut owned = manifest
        .symbols
        .iter()
        .filter(|symbol| symbol.translation_unit == unit.source_path)
        .collect::<Vec<_>>();
    owned.sort_by(|left, right| left.candidate_id.cmp(&right.candidate_id));
    for symbol in owned {
        if unit.encoding == R0ProgramEncoding::GroupedSlot
            && unit.inner == R0InnerFold::U64
            && unit.outer == R0OuterFold::U96
            && symbol.geometry == R0Geometry::Cta96Partitioned
            && symbol.source_policy == R0SourcePolicy::Ordinary
        {
            output.push_str(&format!(
                "AB_R0PB_DEFINE_DEDICATED_GROUPED_U64_U96_PARTITIONED_KERNEL({});\n",
                symbol.symbol
            ));
            continue;
        }
        let macro_name = match symbol.source_policy {
            R0SourcePolicy::Ordinary => "AB_R0PB_DEFINE_ORDINARY_KERNEL",
            R0SourcePolicy::Materialized => "AB_R0PB_DEFINE_MATERIALIZED_KERNEL",
        };
        output.push_str(&format!(
            "{macro_name}({}, r0pb_cursor, r0pb_inner, r0pb_outer, r0pb_{}_geometry);\n",
            symbol.symbol,
            symbol.geometry.as_str()
        ));
    }
    output.push_str("\n} // namespace airbender::gkr_windowed_bench\n");
    output
}

fn clang_format_generated_cuda(
    relative_path: &str,
    source: &str,
) -> Result<Vec<u8>, R0PrototypeManifestError> {
    let assumed_filename = Path::new("gpu/gkr_windowed_bench").join(relative_path);
    let mut child = Command::new("clang-format")
        .arg(format!("--assume-filename={}", assumed_filename.display()))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| R0PrototypeManifestError(format!("run clang-format: {error}")))?;
    child
        .stdin
        .take()
        .ok_or_else(|| R0PrototypeManifestError("open clang-format stdin".to_owned()))?
        .write_all(source.as_bytes())
        .map_err(|error| R0PrototypeManifestError(format!("write clang-format stdin: {error}")))?;
    let output = child
        .wait_with_output()
        .map_err(|error| R0PrototypeManifestError(format!("wait for clang-format: {error}")))?;
    if !output.status.success() {
        return Err(R0PrototypeManifestError(format!(
            "clang-format failed for {relative_path}: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        )));
    }
    Ok(output.stdout)
}

fn sha256_bytes(bytes: &[u8]) -> Result<String, R0PrototypeManifestError> {
    let mut child = Command::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|error| R0PrototypeManifestError(format!("run sha256sum: {error}")))?;
    child
        .stdin
        .as_mut()
        .ok_or_else(|| R0PrototypeManifestError("open sha256sum stdin".to_owned()))?
        .write_all(bytes)
        .map_err(|error| R0PrototypeManifestError(format!("write sha256sum stdin: {error}")))?;
    let output = child
        .wait_with_output()
        .map_err(|error| R0PrototypeManifestError(format!("wait for sha256sum: {error}")))?;
    if !output.status.success() {
        return Err(R0PrototypeManifestError("sha256sum failed".to_owned()));
    }
    let text = String::from_utf8(output.stdout)
        .map_err(|error| R0PrototypeManifestError(format!("sha256sum output: {error}")))?;
    let hash = text.split_whitespace().next().unwrap_or_default();
    if hash.len() != 64
        || !hash
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(R0PrototypeManifestError(format!(
            "sha256sum returned noncanonical hash: {hash:?}"
        )));
    }
    Ok(hash.to_owned())
}

fn candidate_symbol(
    encoding: R0ProgramEncoding,
    inner: R0InnerFold,
    outer: R0OuterFold,
    geometry: R0Geometry,
    source_policy: R0SourcePolicy,
    lineage: R0Lineage,
    translation_unit: String,
) -> R0CandidateSymbolV1 {
    let candidate_id = format!(
        "r0pb/{}/{}/{}/{}/{}/{}",
        encoding.as_str(),
        inner.as_str(),
        outer.as_str(),
        geometry.as_str(),
        source_policy.as_str(),
        lineage.as_str()
    );
    let symbol = if lineage == R0Lineage::Reference {
        reference_symbol(geometry).to_owned()
    } else {
        format!(
            "ab_gkr_windowed_r0pb_{}_{}_{}_{}_{}_kernel",
            encoding.as_str(),
            inner.as_str(),
            outer.as_str(),
            geometry.as_str(),
            source_policy.as_str()
        )
    };
    let descriptor_kind = match (encoding, source_policy) {
        (R0ProgramEncoding::CurrentFixedSlot, R0SourcePolicy::Ordinary) => "r0_vm_desc".to_owned(),
        (_, R0SourcePolicy::Ordinary) => {
            format!("r0_{}_ordinary_desc", encoding.as_str())
        }
        (_, R0SourcePolicy::Materialized) => {
            format!("r0_{}_materialized_desc", encoding.as_str())
        }
    };
    R0CandidateSymbolV1 {
        candidate_id,
        symbol,
        encoding,
        inner,
        outer,
        geometry,
        source_policy,
        lineage,
        translation_unit,
        descriptor_kind,
    }
}

fn reference_symbol(geometry: R0Geometry) -> &'static str {
    match geometry {
        R0Geometry::Cta288Pair => "ab_gkr_windowed_r0_cta288_pair_kernel",
        R0Geometry::Cta96Partitioned => "ab_gkr_windowed_r0_cta96_partitioned_kernel",
        R0Geometry::Cta96X0Major => "ab_gkr_windowed_r0_cta96_x0_major_kernel",
        R0Geometry::Cta96X1Major => "ab_gkr_windowed_r0_cta96_x1_major_kernel",
        R0Geometry::Cta96X2Major => "ab_gkr_windowed_r0_cta96_x2_major_kernel",
    }
}

fn validate_unique<'a>(
    name: &str,
    values: impl Iterator<Item = &'a str>,
) -> Result<(), R0PrototypeManifestError> {
    let mut seen = BTreeSet::new();
    for value in values {
        if !seen.insert(value) {
            return Err(R0PrototypeManifestError(format!(
                "duplicate {name}: {value}"
            )));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::fs;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    use crate::r0_geometry::R0Geometry;

    use super::{
        build_r0_prototype_manifest, build_r0_sectioned_manifest, build_r0_sectioned_manifest_v2,
        build_r0_sectioned_manifest_v3, build_r0_sectioned_manifest_v4,
        build_r0_sectioned_manifest_v4_for_merge_policy, parse_r0_prototype_generator_mode,
        r0_sectioned_compatible_compiled_shapes, render_r0_prototype_generated_files,
        render_r0_prototype_generated_files_for_merge_policy, render_sectioned_cuda_manifest,
        render_sectioned_translation_unit, resolve_r0_sectioned_compiled_shape,
        sectioned_owned_partitions, sync_r0_prototype_generated_files,
        validate_r0_sectioned_manifest, validate_r0_sectioned_manifest_v2,
        validate_r0_sectioned_manifest_v3, validate_r0_sectioned_manifest_v4, R0GeneratedMode,
        R0InnerFold, R0Lineage, R0OuterFold, R0ProgramEncoding, R0PrototypeManifestV1,
        R0SectionedGeometry, R0SectionedOwnership, R0SectionedShapeMergePolicy, R0SourcePolicy,
        R0_SECTIONED_COMPILED_SHAPES_V4, R0_SECTIONED_SPECIALIZED_SHAPES,
        R0_SECTIONED_UNION_SHAPES_V1,
    };

    #[test]
    fn cpu_union_bank_closes_all_observed_shapes_and_plans_the_literal_corpus_domain() {
        let expected = [
            0x001, 0x020, 0x021, 0x1b1, 0x1b7, 0x3f7, 0x3fb, 0x3ff, 0x460, 0x461, 0x470, 0x471,
            0x4f6, 0x4f7, 0x5f1, 0x5f7, 0x7f7, 0x7fb, 0x7ff, 0x9bf, 0xbfb, 0xbff, 0xc78, 0xc79,
            0xc7a, 0xc7b, 0xcfe, 0xcff, 0xdf9, 0xdfb, 0xdff, 0xffb, 0xfff,
        ];
        assert_eq!(R0_SECTIONED_UNION_SHAPES_V1, expected);

        let manifest =
            build_r0_sectioned_manifest_v4_for_merge_policy(R0SectionedShapeMergePolicy::UnionBank)
                .unwrap();
        assert_eq!(manifest.symbols.len(), 66);
        assert!(manifest.symbols.iter().all(|row| row.shape_bits.is_some()));
        assert_eq!(
            manifest
                .symbols
                .iter()
                .filter_map(|row| row.shape_bits)
                .collect::<BTreeSet<_>>(),
            expected.into_iter().collect(),
        );
        assert!(manifest
            .shape_dispatch
            .iter()
            .all(|row| row.input_shape == row.compiled_shape));

        let populations = [
            (0x001, 1usize),
            (0x020, 9),
            (0x1b1, 1),
            (0x1b7, 2),
            (0x3f7, 2),
            (0x3fb, 1),
            (0x460, 14),
            (0x470, 19),
            (0x4f6, 1),
            (0x9bf, 1),
            (0xbfb, 3),
            (0xbff, 1),
            (0xc78, 1),
            (0xc7a, 1),
        ];
        assert_eq!(
            populations.iter().map(|(_, count)| count).sum::<usize>(),
            57
        );
        let timed_arms = populations
            .iter()
            .map(|(shape, count)| {
                r0_sectioned_compatible_compiled_shapes(&manifest, *shape)
                    .unwrap()
                    .len()
                    * count
                    * 2
            })
            .sum::<usize>();
        assert_eq!(timed_arms, 2_212);
    }

    #[test]
    fn cpu_union_bank_generation_emits_one_unit_and_two_symbols_per_union_mask() {
        let files = render_r0_prototype_generated_files_for_merge_policy(
            R0SectionedShapeMergePolicy::UnionBank,
        )
        .unwrap();
        assert_eq!(files.len(), 71);
        let paths = files
            .iter()
            .map(|file| file.relative_path.as_str())
            .collect::<BTreeSet<_>>();
        assert!(!paths.contains("native/generated/r0_sectioned_universal.cu"));
        assert_eq!(
            paths
                .iter()
                .filter(|path| path.starts_with("native/generated/r0_sectioned_shape_"))
                .count(),
            33,
        );
        let registry = files
            .iter()
            .find(|file| file.relative_path == "src/generated/r0_sectioned_registry.rs")
            .unwrap()
            .text()
            .unwrap();
        assert!(registry.contains("R0_SECTIONED_SHAPE_MERGE_POLICY: &str = \"union_bank\""));
        assert!(registry.contains("R0_SECTIONED_CANDIDATE_IDS: [&str; 66]"));
        for shape in ["021", "3ff", "7fb", "fff"] {
            assert!(
                paths.contains(format!("native/generated/r0_sectioned_shape_{shape}.cu").as_str())
            );
        }
    }

    #[test]
    fn cpu_sectioned_shape_merge_policy_parser_accepts_only_the_three_generated_banks() {
        assert_eq!(
            R0SectionedShapeMergePolicy::parse("exact").unwrap(),
            R0SectionedShapeMergePolicy::Exact
        );
        assert_eq!(
            R0SectionedShapeMergePolicy::parse("merged").unwrap(),
            R0SectionedShapeMergePolicy::Merged
        );
        assert_eq!(
            R0SectionedShapeMergePolicy::parse("union_bank").unwrap(),
            R0SectionedShapeMergePolicy::UnionBank
        );
        for invalid in ["union", "UnionBank", "", "exact,merged"] {
            assert!(R0SectionedShapeMergePolicy::parse(invalid).is_err());
        }
    }

    #[test]
    fn cpu_sectioned_v4_exact_control_keeps_all_shapes_and_merged_policy_aliases_only_supersets() {
        let exact =
            build_r0_sectioned_manifest_v4_for_merge_policy(R0SectionedShapeMergePolicy::Exact)
                .unwrap();
        assert_eq!(exact.symbols.len(), 30);
        assert_eq!(exact.shape_dispatch.len(), 14);
        assert!(exact
            .shape_dispatch
            .iter()
            .all(|row| row.input_shape == row.compiled_shape));
        assert_eq!(
            exact
                .symbols
                .iter()
                .filter_map(|row| row.shape_bits)
                .collect::<BTreeSet<_>>(),
            R0_SECTIONED_SPECIALIZED_SHAPES.into_iter().collect(),
        );
        for shape in [0x3fb, 0x9bf, 0xbff, 0xc78, 0xc7a] {
            assert_eq!(
                resolve_r0_sectioned_compiled_shape(&exact, shape).unwrap(),
                shape
            );
            for min_blocks in [Some(3), Some(4)] {
                assert!(exact
                    .symbols
                    .iter()
                    .any(|row| { row.shape_bits == Some(shape) && row.min_blocks == min_blocks }));
            }
        }

        let merged =
            build_r0_sectioned_manifest_v4_for_merge_policy(R0SectionedShapeMergePolicy::Merged)
                .unwrap();
        assert_eq!(merged, build_r0_sectioned_manifest_v4().unwrap());
        assert_eq!(merged.symbols.len(), 26);
        assert_eq!(
            resolve_r0_sectioned_compiled_shape(&merged, 0x3fb).unwrap(),
            0x3fb
        );
        assert_eq!(
            resolve_r0_sectioned_compiled_shape(&merged, 0x9bf).unwrap(),
            0xbff
        );
        assert_eq!(
            resolve_r0_sectioned_compiled_shape(&merged, 0xc78).unwrap(),
            0xc7a
        );
    }

    #[test]
    fn cpu_exact_control_generation_adds_only_the_two_retired_shape_units() {
        let merged = render_r0_prototype_generated_files_for_merge_policy(
            R0SectionedShapeMergePolicy::Merged,
        )
        .unwrap();
        let exact = render_r0_prototype_generated_files_for_merge_policy(
            R0SectionedShapeMergePolicy::Exact,
        )
        .unwrap();
        assert_eq!(merged.len(), 51);
        assert_eq!(exact.len(), 53);

        let exact_paths = exact
            .iter()
            .map(|file| file.relative_path.as_str())
            .collect::<BTreeSet<_>>();
        let merged_paths = merged
            .iter()
            .map(|file| file.relative_path.as_str())
            .collect::<BTreeSet<_>>();
        assert_eq!(
            exact_paths
                .difference(&merged_paths)
                .copied()
                .collect::<Vec<_>>(),
            vec![
                "native/generated/r0_sectioned_shape_9bf.cu",
                "native/generated/r0_sectioned_shape_c78.cu",
            ],
        );

        let registry = exact
            .iter()
            .find(|file| file.relative_path == "src/generated/r0_sectioned_registry.rs")
            .unwrap()
            .text()
            .unwrap();
        assert!(registry.contains("R0_SECTIONED_SHAPE_MERGE_POLICY: &str = \"exact\""));
        assert!(registry.contains("R0_SECTIONED_CANDIDATE_IDS: [&str; 30]"));
        let sources = exact
            .iter()
            .find(|file| {
                file.relative_path == "native/generated/windowed_r0_prototype_sources.cmake"
            })
            .unwrap()
            .text()
            .unwrap();
        for shape in ["3fb", "9bf", "c78"] {
            assert!(sources.contains(&format!("r0_sectioned_shape_{shape}.cu")));
        }
        let merged_sources = merged
            .iter()
            .find(|file| {
                file.relative_path == "native/generated/windowed_r0_prototype_sources.cmake"
            })
            .unwrap()
            .text()
            .unwrap();
        assert!(merged_sources.contains("r0_sectioned_shape_3fb.cu"));
        assert!(!merged_sources.contains("r0_sectioned_shape_9bf.cu"));
        assert!(!merged_sources.contains("r0_sectioned_shape_c78.cu"));
    }

    #[test]
    fn cpu_sectioned_v4_retires_split_and_resolves_exact_superset_aliases() {
        let manifest = build_r0_sectioned_manifest_v4().unwrap();
        assert_eq!(manifest.schema_version, 4);
        assert_eq!(manifest.specialized_shapes, R0_SECTIONED_SPECIALIZED_SHAPES);
        assert_eq!(manifest.symbols.len(), 26);
        assert_eq!(manifest.shape_dispatch.len(), 14);
        assert!(manifest.symbols.iter().all(|row| {
            row.geometry == R0SectionedGeometry::Wide9
                && [Some(3), Some(4)].contains(&row.min_blocks)
        }));
        assert_eq!(
            manifest
                .symbols
                .iter()
                .filter_map(|row| row.shape_bits)
                .collect::<std::collections::BTreeSet<_>>(),
            R0_SECTIONED_COMPILED_SHAPES_V4.into_iter().collect(),
        );

        for (input, compiled) in [
            (0x001, 0x001),
            (0x3fb, 0x3fb),
            (0x9bf, 0xbff),
            (0xbff, 0xbff),
            (0xc78, 0xc7a),
            (0xc7a, 0xc7a),
        ] {
            assert_eq!(
                resolve_r0_sectioned_compiled_shape(&manifest, input).unwrap(),
                compiled,
            );
            assert_eq!(input & !compiled, 0, "{input:#05x} -> {compiled:#05x}");
        }

        let mut missing = manifest.clone();
        missing.shape_dispatch.pop();
        assert!(validate_r0_sectioned_manifest_v4(&missing).is_err());

        let mut unsafe_alias = manifest.clone();
        unsafe_alias
            .shape_dispatch
            .iter_mut()
            .find(|row| row.input_shape == 0x3fb)
            .unwrap()
            .compiled_shape = 0x020;
        assert!(validate_r0_sectioned_manifest_v4(&unsafe_alias).is_err());
        assert!(resolve_r0_sectioned_compiled_shape(&unsafe_alias, 0x3fb).is_err());
    }

    #[test]
    fn cpu_historical_sectioned_schemas_reject_v4_dispatch_metadata() {
        let dispatch = super::R0SectionedShapeDispatchV4 {
            input_shape: 0x3fb,
            compiled_shape: 0xbff,
        };
        let mut v1 = build_r0_sectioned_manifest().unwrap();
        v1.shape_dispatch.push(dispatch.clone());
        assert!(validate_r0_sectioned_manifest(&v1).is_err());

        let mut v2 = build_r0_sectioned_manifest_v2().unwrap();
        v2.shape_dispatch.push(dispatch.clone());
        assert!(validate_r0_sectioned_manifest_v2(&v2).is_err());

        let mut v3 = build_r0_sectioned_manifest_v3().unwrap();
        v3.shape_dispatch.push(dispatch);
        assert!(validate_r0_sectioned_manifest_v3(&v3).is_err());
    }

    #[test]
    fn cpu_sectioned_v3_adds_wide_b4_and_exact_240_symbol_domain() {
        let manifest = build_r0_sectioned_manifest_v3().unwrap();
        assert_eq!(manifest.schema_version, 3);
        assert_eq!(manifest.symbols.len(), 240);
        for shape in
            core::iter::once(None).chain(R0_SECTIONED_SPECIALIZED_SHAPES.into_iter().map(Some))
        {
            let rows = manifest
                .symbols
                .iter()
                .filter(|row| row.shape_bits == shape)
                .collect::<Vec<_>>();
            assert_eq!(rows.len(), 16);
            assert_eq!(
                rows.iter()
                    .filter(|row| row.geometry == R0SectionedGeometry::Wide9)
                    .map(|row| row.min_blocks)
                    .collect::<Vec<_>>(),
                [Some(3), Some(4)],
            );
            for geometry in [R0SectionedGeometry::Split3, R0SectionedGeometry::Serial3Low] {
                assert_eq!(
                    rows.iter()
                        .filter(|row| row.geometry == geometry)
                        .map(|row| row.min_blocks)
                        .collect::<Vec<_>>(),
                    [
                        None,
                        Some(7),
                        Some(8),
                        Some(9),
                        Some(10),
                        Some(12),
                        Some(16)
                    ],
                );
            }
            assert!(rows
                .iter()
                .all(|row| row.geometry != R0SectionedGeometry::Serial3High));
        }

        let mut bad_wide = manifest.clone();
        bad_wide
            .symbols
            .iter_mut()
            .find(|row| row.geometry == R0SectionedGeometry::Wide9)
            .unwrap()
            .min_blocks = Some(5);
        assert!(validate_r0_sectioned_manifest_v3(&bad_wide).is_err());
    }

    #[test]
    fn cpu_sectioned_launch_bound_manifest_has_exact_225_symbol_domain() {
        let manifest = build_r0_sectioned_manifest_v2().unwrap();
        assert_eq!(manifest.schema_version, 2);
        assert_eq!(manifest.symbols.len(), 225);
        for shape in
            core::iter::once(None).chain(R0_SECTIONED_SPECIALIZED_SHAPES.into_iter().map(Some))
        {
            let rows = manifest
                .symbols
                .iter()
                .filter(|row| row.shape_bits == shape)
                .collect::<Vec<_>>();
            assert_eq!(rows.len(), 15);
            assert_eq!(
                rows.iter()
                    .filter(|row| row.geometry == R0SectionedGeometry::Wide9)
                    .map(|row| row.min_blocks)
                    .collect::<Vec<_>>(),
                [Some(3)],
            );
            for geometry in [R0SectionedGeometry::Split3, R0SectionedGeometry::Serial3Low] {
                assert_eq!(
                    rows.iter()
                        .filter(|row| row.geometry == geometry)
                        .map(|row| row.min_blocks)
                        .collect::<Vec<_>>(),
                    [
                        None,
                        Some(7),
                        Some(8),
                        Some(9),
                        Some(10),
                        Some(12),
                        Some(16),
                    ],
                );
            }
            assert!(rows
                .iter()
                .all(|row| row.geometry != R0SectionedGeometry::Serial3High));
        }

        let mut bad_split_bound = manifest.clone();
        bad_split_bound
            .symbols
            .iter_mut()
            .find(|row| row.geometry == R0SectionedGeometry::Split3)
            .unwrap()
            .min_blocks = Some(3);
        assert!(validate_r0_sectioned_manifest_v2(&bad_split_bound).is_err());

        let mut missing_wide_bound = manifest.clone();
        missing_wide_bound
            .symbols
            .iter_mut()
            .find(|row| row.geometry == R0SectionedGeometry::Wide9)
            .unwrap()
            .min_blocks = None;
        assert!(validate_r0_sectioned_manifest_v2(&missing_wide_bound).is_err());

        let mut duplicate_key = manifest.clone();
        let mut duplicate = duplicate_key.symbols[0].clone();
        duplicate.candidate_id.push_str("-duplicate-id");
        duplicate.symbol.push_str("_duplicate_symbol");
        duplicate_key.symbols.push(duplicate);
        assert!(validate_r0_sectioned_manifest_v2(&duplicate_key).is_err());

        let mut wrong_schema = manifest;
        wrong_schema.schema_version = 1;
        assert!(validate_r0_sectioned_manifest_v2(&wrong_schema).is_err());
    }

    #[test]
    fn cpu_sectioned_v1_artifact_is_byte_exact_and_unbounded() {
        let manifest = build_r0_sectioned_manifest().unwrap();
        assert!(manifest.symbols.iter().all(|row| row.min_blocks.is_none()));
        let mut expected = serde_json::to_vec_pretty(&manifest).unwrap();
        expected.push(b'\n');
        let actual = fs::read(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("artifacts/windowed_r0_sectioned_manifest_v1.json"),
        )
        .unwrap();
        assert_eq!(actual, expected);

        let mut bounded_v1 = manifest;
        bounded_v1.symbols[0].min_blocks = Some(3);
        assert!(validate_r0_sectioned_manifest(&bounded_v1).is_err());
    }

    #[test]
    fn cpu_sectioned_geometries_have_exact_literal_ownership() {
        let selector_triplets = [
            vec![vec![0, 1, 2]],
            vec![vec![3, 4, 5]],
            vec![vec![6, 7, 8]],
            vec![vec![9, 10, 11]],
            vec![vec![12, 13, 14]],
            vec![vec![15, 16, 17]],
            vec![vec![18, 19, 20]],
            vec![vec![21, 22, 23]],
            vec![vec![24, 25, 26]],
        ];
        for geometry in [R0SectionedGeometry::Wide9, R0SectionedGeometry::Split3] {
            for (owner, expected) in selector_triplets.iter().enumerate() {
                assert_eq!(
                    sectioned_owned_partitions(geometry, owner as u32).unwrap(),
                    *expected,
                    "{geometry:?} owner {owner}",
                );
            }
        }

        let serial_low = [
            vec![vec![0, 1, 2], vec![3, 4, 5], vec![6, 7, 8]],
            vec![vec![9, 10, 11], vec![12, 13, 14], vec![15, 16, 17]],
            vec![vec![18, 19, 20], vec![21, 22, 23], vec![24, 25, 26]],
        ];
        let serial_high = [
            vec![(0u8..=8).collect::<Vec<_>>()],
            vec![(9u8..=17).collect::<Vec<_>>()],
            vec![(18u8..=26).collect::<Vec<_>>()],
        ];
        for owner in 0..3 {
            assert_eq!(
                sectioned_owned_partitions(R0SectionedGeometry::Serial3Low, owner).unwrap(),
                serial_low[owner as usize],
            );
            assert_eq!(
                sectioned_owned_partitions(R0SectionedGeometry::Serial3High, owner).unwrap(),
                serial_high[owner as usize],
            );
        }

        for geometry in R0SectionedGeometry::ALL {
            let mut seen = [0u8; 27];
            for owner in geometry.owners() {
                for partition in sectioned_owned_partitions(geometry, owner).unwrap() {
                    for cell in partition {
                        seen[cell as usize] += 1;
                    }
                }
            }
            assert_eq!(seen, [1; 27], "{geometry:?}");
        }
    }

    #[test]
    fn cpu_sectioned_manifest_pins_real_shapes_and_rejects_axis_swap() {
        let manifest = build_r0_sectioned_manifest().unwrap();
        assert_eq!(manifest.schema_version, 1);
        assert_eq!(
            manifest.specialized_shapes,
            [
                1, 32, 433, 439, 1_015, 1_019, 1_120, 1_136, 1_270, 2_495, 3_067, 3_071, 3_192,
                3_194,
            ],
        );
        assert_eq!(manifest.symbols.len(), 60);
        assert_eq!(
            manifest
                .symbols
                .iter()
                .filter(|row| row.shape_bits.is_none())
                .count(),
            4,
        );
        for geometry in R0SectionedGeometry::ALL {
            assert_eq!(
                manifest
                    .symbols
                    .iter()
                    .filter(|row| row.geometry == geometry)
                    .count(),
                15,
            );
        }

        let mut swapped = manifest.clone();
        let serial = swapped
            .symbols
            .iter_mut()
            .find(|row| row.geometry == R0SectionedGeometry::Serial3Low)
            .unwrap();
        serial.ownership = R0SectionedOwnership::FixedX1;
        let error = validate_r0_sectioned_manifest(&swapped)
            .unwrap_err()
            .to_string();
        assert!(error.contains("ownership"), "{error}");
    }

    #[test]
    fn cpu_generated_outputs_append_the_sectioned_family() {
        let files = render_r0_prototype_generated_files().unwrap();
        let sectioned_manifest = files
            .iter()
            .find(|file| file.relative_path == "artifacts/windowed_r0_sectioned_manifest_v4.json")
            .expect("sectioned manifest");
        assert_eq!(
            serde_json::from_slice::<super::R0SectionedManifestV1>(&sectioned_manifest.contents,)
                .unwrap(),
            build_r0_sectioned_manifest_v4().unwrap(),
        );
        assert!(files
            .iter()
            .all(|file| file.relative_path != "artifacts/windowed_r0_sectioned_manifest_v1.json"));
        let registry = files
            .iter()
            .find(|file| file.relative_path == "src/generated/r0_sectioned_registry.rs")
            .expect("sectioned Rust registry")
            .text()
            .unwrap();
        assert!(registry.contains("R0_SECTIONED_CANDIDATE_IDS: [&str; 26]"));
        assert!(registry.contains("ab_gkr_windowed_r0_sectioned_universal_wide9_b3_kernel"));
        assert!(registry.contains("ab_gkr_windowed_r0_sectioned_universal_wide9_b4_kernel"));
        assert!(!registry.contains("split3"));
        assert!(!registry.contains("serial3_low"));
        assert!(!registry.contains("serial3_high"));
        assert!(!registry.contains("/home/"));
        assert_eq!(
            files
                .iter()
                .filter(|file| {
                    file.relative_path
                        .starts_with("native/generated/r0_sectioned_")
                        && file.relative_path.ends_with(".cu")
                })
                .count(),
            13,
        );
    }

    #[test]
    fn cpu_sectioned_v3_artifact_is_byte_exact_after_v4_retirement() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("artifacts/windowed_r0_sectioned_manifest_v3.json");
        let actual = fs::read(path).unwrap();
        let mut expected =
            serde_json::to_vec_pretty(&build_r0_sectioned_manifest_v3().unwrap()).unwrap();
        expected.push(b'\n');
        assert_eq!(actual, expected);
    }

    #[test]
    fn cpu_generated_sectioned_v4_has_only_two_wide_entrypoints_per_compiled_shape() {
        let manifest = build_r0_sectioned_manifest_v4().unwrap();
        let rendered_header = render_sectioned_cuda_manifest(&manifest, "fixture-sha");
        assert!(rendered_header.contains("R0_SECTIONED_SYMBOL_COUNT = 26"));
        for shape in
            core::iter::once(None).chain(R0_SECTIONED_COMPILED_SHAPES_V4.into_iter().map(Some))
        {
            let unit = render_sectioned_translation_unit(&manifest, shape);
            assert_eq!(unit.matches("AB_R0PB_DEFINE_SECTIONED_").count(), 2);
            assert_eq!(unit.matches("WIDE9_BOUNDED_KERNEL").count(), 2);
            assert!(!unit.contains("SPLIT3"));
            assert!(!unit.contains("SERIAL3"));
            assert!(unit.contains(", 3);"));
            assert!(unit.contains(", 4);"));
            assert!(unit.contains("R0_SECTIONED_SYMBOL_COUNT == 26"));
        }
    }

    #[test]
    fn cpu_generated_sectioned_sweep_has_exact_bounded_entrypoints_and_counts() {
        let manifest = build_r0_sectioned_manifest_v3().unwrap();
        let rendered_header = render_sectioned_cuda_manifest(&manifest, "fixture-sha");
        assert!(rendered_header.contains("R0_SECTIONED_SYMBOL_COUNT = 240"));
        for shape in
            core::iter::once(None).chain(R0_SECTIONED_SPECIALIZED_SHAPES.into_iter().map(Some))
        {
            let unit = render_sectioned_translation_unit(&manifest, shape);
            assert_eq!(unit.matches("AB_R0PB_DEFINE_SECTIONED_").count(), 16);
            assert!(!unit.contains("SERIAL3_HIGH"));
            assert_eq!(unit.matches("WIDE9_BOUNDED_KERNEL").count(), 2);
            assert!(unit.contains(", 3);"));
            assert!(unit.contains(", 4);"));
            for bound in [7, 8, 9, 10, 12, 16] {
                assert!(unit.contains("SPLIT3_BOUNDED_KERNEL"));
                assert!(unit.contains("SERIAL3_LOW_BOUNDED_KERNEL"));
                assert!(unit.contains(&format!(", {bound});")));
            }
            assert!(unit.contains("R0_SECTIONED_SYMBOL_COUNT == 240"));
        }

        let canary = fs::read_to_string(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("native/windowed_r0_prototype_canary.cu"),
        )
        .unwrap();
        assert!(canary.contains("AB_R0PB_DEFINE_SECTIONED_SERIAL3_HIGH_KERNEL"));
        for bound in [7, 8, 9, 10, 12, 16] {
            assert!(canary.contains("SPLIT3_BOUNDED_KERNEL"));
            assert!(canary.contains(&format!(", {bound});")));
        }
    }

    #[test]
    fn cpu_sectioned_v2_artifact_is_byte_exact() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("artifacts/windowed_r0_sectioned_manifest_v2.json");
        let actual = fs::read(path).unwrap();
        let mut expected =
            serde_json::to_vec_pretty(&build_r0_sectioned_manifest_v2().unwrap()).unwrap();
        expected.push(b'\n');
        assert_eq!(actual, expected);
    }

    #[test]
    fn cpu_manifest_has_exact_legal_cross_product_and_counts() {
        let manifest = build_r0_prototype_manifest().unwrap();

        assert_eq!(manifest.schema_version, 1);
        assert_eq!(manifest.translation_units.len(), 30);
        assert_eq!(manifest.symbols.len(), 245);
        assert_eq!(manifest.configurations.len(), 425);

        let symbol_ids = manifest
            .symbols
            .iter()
            .map(|row| row.candidate_id.as_str())
            .collect::<BTreeSet<_>>();
        let symbol_names = manifest
            .symbols
            .iter()
            .map(|row| row.symbol.as_str())
            .collect::<BTreeSet<_>>();
        let configuration_ids = manifest
            .configurations
            .iter()
            .map(|row| row.configuration_id.as_str())
            .collect::<BTreeSet<_>>();
        assert_eq!(symbol_ids.len(), 245);
        assert_eq!(symbol_names.len(), 245);
        assert_eq!(configuration_ids.len(), 425);

        let references = manifest
            .symbols
            .iter()
            .filter(|row| row.lineage == R0Lineage::Reference)
            .collect::<Vec<_>>();
        assert_eq!(references.len(), 5);
        assert_eq!(
            references
                .iter()
                .map(|row| row.geometry.as_str())
                .collect::<BTreeSet<_>>(),
            R0Geometry::ALL
                .into_iter()
                .map(R0Geometry::as_str)
                .collect()
        );
        assert!(references.iter().all(|row| {
            row.encoding == R0ProgramEncoding::CurrentFixedSlot
                && row.inner == R0InnerFold::Canonical
                && row.outer == R0OuterFold::Canonical
                && row.source_policy == R0SourcePolicy::Ordinary
        }));

        let template_ordinary = manifest
            .symbols
            .iter()
            .filter(|row| {
                row.lineage == R0Lineage::Template && row.source_policy == R0SourcePolicy::Ordinary
            })
            .count();
        let template_materialized = manifest
            .symbols
            .iter()
            .filter(|row| {
                row.lineage == R0Lineage::Template
                    && row.source_policy == R0SourcePolicy::Materialized
            })
            .count();
        assert_eq!(template_ordinary, 150);
        assert_eq!(template_materialized, 90);

        let ordinary_configurations = manifest
            .configurations
            .iter()
            .filter(|row| row.tile_capacity.is_none())
            .count();
        let materialized_configurations = manifest
            .configurations
            .iter()
            .filter(|row| row.tile_capacity.is_some())
            .count();
        assert_eq!(ordinary_configurations, 155);
        assert_eq!(materialized_configurations, 270);
    }

    #[test]
    fn cpu_inner_u64_exists_only_for_grouped_encodings() {
        let manifest = build_r0_prototype_manifest().unwrap();
        let inner_u64 = manifest
            .translation_units
            .iter()
            .filter(|row| row.inner == R0InnerFold::U64)
            .collect::<Vec<_>>();

        assert_eq!(inner_u64.len(), 6);
        assert!(inner_u64.iter().all(|row| matches!(
            row.encoding,
            R0ProgramEncoding::GroupedSlot | R0ProgramEncoding::GroupedDirect
        )));
        assert_eq!(
            inner_u64
                .iter()
                .map(|row| (row.encoding, row.outer))
                .collect::<BTreeSet<_>>(),
            [
                (R0ProgramEncoding::GroupedSlot, R0OuterFold::Canonical),
                (R0ProgramEncoding::GroupedSlot, R0OuterFold::U64),
                (R0ProgramEncoding::GroupedSlot, R0OuterFold::U96),
                (R0ProgramEncoding::GroupedDirect, R0OuterFold::Canonical),
                (R0ProgramEncoding::GroupedDirect, R0OuterFold::U64),
                (R0ProgramEncoding::GroupedDirect, R0OuterFold::U96),
            ]
            .into_iter()
            .collect()
        );
    }

    #[test]
    fn cpu_materialized_symbols_have_exact_geometries_and_runtime_capacities() {
        let manifest = build_r0_prototype_manifest().unwrap();
        let materialized_geometries = manifest
            .symbols
            .iter()
            .filter(|row| row.source_policy == R0SourcePolicy::Materialized)
            .map(|row| row.geometry.as_str())
            .collect::<BTreeSet<_>>();
        assert_eq!(
            materialized_geometries,
            [
                R0Geometry::Cta288Pair.as_str(),
                R0Geometry::Cta96Partitioned.as_str(),
                R0Geometry::Cta96X2Major.as_str(),
            ]
            .into_iter()
            .collect()
        );

        for symbol in manifest
            .symbols
            .iter()
            .filter(|row| row.source_policy == R0SourcePolicy::Materialized)
        {
            let capacities = manifest
                .configurations
                .iter()
                .filter(|row| row.candidate_id == symbol.candidate_id)
                .map(|row| row.tile_capacity.unwrap())
                .collect::<Vec<_>>();
            assert_eq!(capacities, [8, 16, 32]);
        }
    }

    #[test]
    fn cpu_each_translation_unit_owns_eight_template_symbols() {
        let manifest = build_r0_prototype_manifest().unwrap();
        for unit in &manifest.translation_units {
            let owned = manifest
                .symbols
                .iter()
                .filter(|row| row.translation_unit == unit.source_path)
                .collect::<Vec<_>>();
            assert_eq!(owned.len(), 8, "{}", unit.translation_unit_id);
            assert!(owned.iter().all(|row| row.lineage == R0Lineage::Template));
        }
    }

    #[test]
    fn cpu_generated_outputs_are_complete_stable_and_relative() {
        let first = render_r0_prototype_generated_files().unwrap();
        let second = render_r0_prototype_generated_files().unwrap();
        assert_eq!(first, second);
        assert_eq!(first.len(), 51);

        let paths = first
            .iter()
            .map(|file| file.relative_path.as_str())
            .collect::<BTreeSet<_>>();
        assert_eq!(paths.len(), 51);
        assert!(paths.iter().all(|path| {
            !path.starts_with('/') && !path.split('/').any(|component| component == "..")
        }));
        assert!(paths.contains("artifacts/windowed_r0_prototype_manifest_v1.json"));
        assert!(paths.contains("artifacts/windowed_r0_sectioned_manifest_v4.json"));
        assert!(paths.contains("src/generated/r0_prototype_registry.rs"));
        assert!(paths.contains("src/generated/r0_sectioned_registry.rs"));
        assert!(paths.contains("native/generated/windowed_r0_prototype_manifest.cuh"));
        assert!(paths.contains("native/generated/windowed_r0_prototype_sources.cmake"));
        assert_eq!(
            paths
                .iter()
                .filter(|path| {
                    path.starts_with("native/generated/r0_prototype_") && path.ends_with(".cu")
                })
                .count(),
            30
        );

        let manifest_bytes = first
            .iter()
            .find(|file| file.relative_path == "artifacts/windowed_r0_prototype_manifest_v1.json")
            .unwrap();
        let decoded: R0PrototypeManifestV1 =
            serde_json::from_slice(&manifest_bytes.contents).unwrap();
        assert_eq!(decoded, build_r0_prototype_manifest().unwrap());

        let rust_registry = first
            .iter()
            .find(|file| file.relative_path == "src/generated/r0_prototype_registry.rs")
            .unwrap()
            .text()
            .unwrap();
        assert!(rust_registry.contains("R0_PROTOTYPE_MANIFEST_SHA256"));
        assert!(rust_registry.contains("R0_PROTOTYPE_CANDIDATE_IDS: [&str; 245]"));
        assert!(rust_registry.contains("R0_PROTOTYPE_CONFIGURATION_IDS: [&str; 425]"));
        assert!(!rust_registry.contains("/home/"));

        let cuda_manifest = first
            .iter()
            .find(|file| {
                file.relative_path == "native/generated/windowed_r0_prototype_manifest.cuh"
            })
            .unwrap()
            .text()
            .unwrap();
        assert!(cuda_manifest.contains("R0_PROTOTYPE_MANIFEST_SHA256"));
        assert!(cuda_manifest.contains("AB_R0PB_ENCODING_GROUPED_DIRECT"));
        assert!(!cuda_manifest.contains("/home/"));
    }

    #[test]
    fn cpu_grouped_u64_u96_partitioned_control_uses_the_dedicated_executor() {
        let files = render_r0_prototype_generated_files().unwrap();
        let translation_unit = files
            .iter()
            .find(|file| {
                file.relative_path == "native/generated/r0_prototype_grouped_slot_u64_u96.cu"
            })
            .unwrap()
            .text()
            .unwrap();
        let symbol = "ab_gkr_windowed_r0pb_grouped_slot_u64_u96_cta96_partitioned_ordinary_kernel";

        assert!(translation_unit.contains(&format!(
            "AB_R0PB_DEFINE_DEDICATED_GROUPED_U64_U96_PARTITIONED_KERNEL({symbol});"
        )));
        assert!(!translation_unit.contains(&format!("AB_R0PB_DEFINE_ORDINARY_KERNEL({symbol},")));
    }

    #[test]
    fn cpu_generated_write_and_check_are_atomic_and_fail_on_tamper() {
        let root = temporary_root("write-check");
        fs::create_dir_all(&root).unwrap();

        let write = sync_r0_prototype_generated_files(&root, R0GeneratedMode::Write).unwrap();
        assert_eq!(write.files, 51);
        let checked = sync_r0_prototype_generated_files(&root, R0GeneratedMode::Check).unwrap();
        assert_eq!(checked, write);

        let manifest_path = root.join("artifacts/windowed_r0_prototype_manifest_v1.json");
        fs::write(&manifest_path, b"tampered\n").unwrap();
        let error = sync_r0_prototype_generated_files(&root, R0GeneratedMode::Check)
            .unwrap_err()
            .to_string();
        assert!(error.contains("differs from generated bytes"), "{error}");

        sync_r0_prototype_generated_files(&root, R0GeneratedMode::Write).unwrap();
        sync_r0_prototype_generated_files(&root, R0GeneratedMode::Check).unwrap();
        let temporary_files = walk_files(&root)
            .into_iter()
            .filter(|path| path.to_string_lossy().contains(".tmp-"))
            .collect::<Vec<_>>();
        assert!(temporary_files.is_empty(), "{temporary_files:?}");

        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn cpu_generator_mode_requires_exactly_write_or_check() {
        assert_eq!(
            parse_r0_prototype_generator_mode(["--write"]).unwrap(),
            R0GeneratedMode::Write
        );
        assert_eq!(
            parse_r0_prototype_generator_mode(["--check"]).unwrap(),
            R0GeneratedMode::Check
        );
        for args in [vec![], vec!["--write", "--check"], vec!["--unknown"]] {
            let error = parse_r0_prototype_generator_mode(args).unwrap_err();
            assert!(error
                .to_string()
                .contains("expected exactly one of --write or --check"));
        }
    }

    fn temporary_root(label: &str) -> PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        std::env::temp_dir().join(format!(
            "windowed-r0-prototype-{label}-{}-{nonce}",
            std::process::id()
        ))
    }

    fn walk_files(root: &std::path::Path) -> Vec<PathBuf> {
        let mut pending = vec![root.to_owned()];
        let mut files = Vec::new();
        while let Some(path) = pending.pop() {
            for entry in fs::read_dir(path).unwrap() {
                let entry = entry.unwrap();
                if entry.file_type().unwrap().is_dir() {
                    pending.push(entry.path());
                } else {
                    files.push(entry.path());
                }
            }
        }
        files
    }
}
