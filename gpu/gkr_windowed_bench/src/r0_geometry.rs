use core::mem::size_of;
use core::ops::Range;

use serde::{Deserialize, Serialize};

use crate::abi::E4;
use crate::geometry::{build_lean_allocation_plan, GeometryError};
use crate::r0_abi::{validate_r0_coordinate_capacities, R0AbiError, R0VmDesc};
use crate::r0_artifact::FrozenR0Coordinate;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum R0Geometry {
    Cta288Pair,
    Cta96Partitioned,
    Cta96X0Major,
    Cta96X1Major,
    Cta96X2Major,
}

impl R0Geometry {
    pub const ALL: [Self; 5] = [
        Self::Cta288Pair,
        Self::Cta96Partitioned,
        Self::Cta96X0Major,
        Self::Cta96X1Major,
        Self::Cta96X2Major,
    ];

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Cta288Pair => "cta288_pair",
            Self::Cta96Partitioned => "cta96_partitioned",
            Self::Cta96X0Major => "cta96_x0_major",
            Self::Cta96X1Major => "cta96_x1_major",
            Self::Cta96X2Major => "cta96_x2_major",
        }
    }

    pub const fn owners_for_one_row_tile(self) -> Range<u32> {
        match self {
            Self::Cta288Pair | Self::Cta96Partitioned => 0..9,
            Self::Cta96X0Major | Self::Cta96X1Major | Self::Cta96X2Major => 0..3,
        }
    }

    pub fn launch_plan(self, log_trace: u32) -> Result<R0LaunchPlan, R0GeometryError> {
        if !(3..=27).contains(&log_trace) {
            return Err(R0GeometryError::UnsupportedLogTrace(log_trace));
        }
        let log_rows = log_trace - 3;
        let surviving_rows = 1u32
            .checked_shl(log_rows)
            .ok_or(R0GeometryError::Overflow("surviving rows"))?;
        let row_tiles = surviving_rows
            .checked_add(31)
            .ok_or(R0GeometryError::Overflow("row tiles"))?
            / 32;
        let (grid_x, block_x) = match self {
            Self::Cta288Pair => (row_tiles, 288),
            Self::Cta96Partitioned => (
                row_tiles
                    .checked_mul(3)
                    .ok_or(R0GeometryError::Overflow("partitioned grid"))?,
                96,
            ),
            Self::Cta96X0Major | Self::Cta96X1Major | Self::Cta96X2Major => (row_tiles, 96),
        };
        Ok(R0LaunchPlan {
            geometry: self,
            grid: [grid_x, 1, 1],
            block: [block_x, 1, 1],
            row_tiles,
            partial_rows: row_tiles,
        })
    }
}

impl core::fmt::Display for R0Geometry {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(self.as_str())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct R0LaunchPlan {
    pub geometry: R0Geometry,
    pub grid: [u32; 3],
    pub block: [u32; 3],
    pub row_tiles: u32,
    pub partial_rows: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0LaunchMetadata {
    pub geometry: R0Geometry,
    pub symbol: String,
    pub grid: [u32; 3],
    pub block: [u32; 3],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0MemoryPreflight {
    pub source_backing_bytes: Vec<u64>,
    pub eq_low_bytes: u64,
    pub eq_high_bytes: u64,
    pub partial_bytes: u64,
    pub final_bytes: u64,
    pub coefficient_bytes: u64,
    pub descriptor_bytes: u64,
    pub runtime_bytes: u64,
    pub requested_bytes: u64,
    pub source_slots: u32,
    pub device_free_bytes: Option<u64>,
    pub device_total_bytes: Option<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R0GeometryError {
    UnsupportedLogTrace(u32),
    InvalidOwner { geometry: R0Geometry, owner: u32 },
    InvalidPartitionedOwner { block_in_tile: u32, warp: u32 },
    Overflow(&'static str),
    Geometry(GeometryError),
    Abi(R0AbiError),
}

impl core::fmt::Display for R0GeometryError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for R0GeometryError {}

impl From<GeometryError> for R0GeometryError {
    fn from(error: GeometryError) -> Self {
        Self::Geometry(error)
    }
}

impl From<R0AbiError> for R0GeometryError {
    fn from(error: R0AbiError) -> Self {
        Self::Abi(error)
    }
}

pub fn partitioned_row_owner(block: u32) -> Result<(u32, u32), R0GeometryError> {
    Ok((block / 3, block % 3))
}

pub fn partitioned_selector(block_in_tile: u32, warp: u32) -> Result<u32, R0GeometryError> {
    if block_in_tile >= 3 || warp >= 3 {
        return Err(R0GeometryError::InvalidPartitionedOwner {
            block_in_tile,
            warp,
        });
    }
    Ok(3 * block_in_tile + warp)
}

pub fn owned_cells(geometry: R0Geometry, owner: u32) -> Result<Vec<u8>, R0GeometryError> {
    if !geometry.owners_for_one_row_tile().contains(&owner) {
        return Err(R0GeometryError::InvalidOwner { geometry, owner });
    }
    let cells = match geometry {
        R0Geometry::Cta288Pair | R0Geometry::Cta96Partitioned => {
            let x0 = owner / 3;
            let x1 = owner % 3;
            (0..3).map(|x2| tensor_index(x0, x1, x2)).collect()
        }
        R0Geometry::Cta96X0Major => (0..3)
            .flat_map(|x1| (0..3).map(move |x2| tensor_index(owner, x1, x2)))
            .collect(),
        R0Geometry::Cta96X1Major => (0..3)
            .flat_map(|x0| (0..3).map(move |x2| tensor_index(x0, owner, x2)))
            .collect(),
        R0Geometry::Cta96X2Major => (0..3)
            .flat_map(|x0| (0..3).map(move |x1| tensor_index(x0, x1, owner)))
            .collect(),
    };
    Ok(cells)
}

fn tensor_index(x0: u32, x1: u32, x2: u32) -> u8 {
    (9 * x0 + 3 * x1 + x2) as u8
}

impl R0MemoryPreflight {
    pub fn for_coordinate(
        coordinate: &FrozenR0Coordinate,
        log_trace: u32,
        runtime_bytes: u64,
        device_memory: Option<(u64, u64)>,
    ) -> Result<Self, R0GeometryError> {
        validate_r0_coordinate_capacities(coordinate)?;
        let launch = R0Geometry::Cta288Pair.launch_plan(log_trace)?;
        let source_plan = build_lean_allocation_plan(&coordinate.binding, log_trace)?;
        if source_plan.num_blocks != launch.row_tiles {
            return Err(R0GeometryError::Overflow("row-tile plan mismatch"));
        }
        let source_backing_bytes = source_plan
            .backings
            .iter()
            .map(|backing| {
                u64::try_from(backing.bytes)
                    .map_err(|_| R0GeometryError::Overflow("source backing bytes"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let eq_low_bytes = checked_element_bytes(
            u64::try_from(source_plan.eq_low_elements)
                .map_err(|_| R0GeometryError::Overflow("low equality elements"))?,
            "low equality bytes",
        )?;
        let eq_high_elements =
            source_plan
                .eq_sizes
                .high
                .into_iter()
                .try_fold(0u64, |sum, bits| {
                    let elements = if bits == 0 {
                        0
                    } else {
                        1u64.checked_shl(bits)
                            .ok_or(R0GeometryError::Overflow("high equality elements"))?
                    };
                    sum.checked_add(elements)
                        .ok_or(R0GeometryError::Overflow("high equality elements"))
                })?;
        let eq_high_bytes = checked_element_bytes(eq_high_elements, "high equality bytes")?;
        let partial_bytes = checked_element_bytes(
            u64::from(launch.partial_rows)
                .checked_mul(27)
                .ok_or(R0GeometryError::Overflow("partial elements"))?,
            "partial bytes",
        )?;
        let final_bytes = checked_element_bytes(27, "final bytes")?;
        let coefficient_bytes = checked_element_bytes(
            u64::try_from(coordinate.recipes.len())
                .map_err(|_| R0GeometryError::Overflow("coefficient elements"))?,
            "coefficient bytes",
        )?;
        let descriptor_bytes = size_of::<R0VmDesc>() as u64;
        let requested_bytes = source_backing_bytes
            .iter()
            .copied()
            .chain([
                eq_low_bytes,
                eq_high_bytes,
                partial_bytes,
                final_bytes,
                coefficient_bytes,
                descriptor_bytes,
                runtime_bytes,
            ])
            .try_fold(0u64, |sum, bytes| {
                sum.checked_add(bytes)
                    .ok_or(R0GeometryError::Overflow("requested bytes"))
            })?;
        let source_slots = u32::try_from(coordinate.binding.source_slots.len())
            .map_err(|_| R0GeometryError::Overflow("source slot count"))?;
        Ok(Self {
            source_backing_bytes,
            eq_low_bytes,
            eq_high_bytes,
            partial_bytes,
            final_bytes,
            coefficient_bytes,
            descriptor_bytes,
            runtime_bytes,
            requested_bytes,
            source_slots,
            device_free_bytes: device_memory.map(|memory| memory.0),
            device_total_bytes: device_memory.map(|memory| memory.1),
        })
    }
}

fn checked_element_bytes(elements: u64, resource: &'static str) -> Result<u64, R0GeometryError> {
    elements
        .checked_mul(size_of::<E4>() as u64)
        .ok_or(R0GeometryError::Overflow(resource))
}

#[cfg(test)]
mod tests {
    use crate::r0_artifact::{decode_r0_bundle, R0_CORPUS_BYTES};

    use super::*;

    fn expected_pair_cells(selector: u32) -> Vec<u8> {
        let x0 = selector / 3;
        let x1 = selector % 3;
        (0..3).map(|x2| (9 * x0 + 3 * x1 + x2) as u8).collect()
    }

    #[test]
    fn cpu_every_geometry_owns_each_tensor_cell_once() {
        for geometry in R0Geometry::ALL {
            let mut seen = [0u8; 27];
            for owner in geometry.owners_for_one_row_tile() {
                for cell in owned_cells(geometry, owner).unwrap() {
                    seen[cell as usize] += 1;
                }
            }
            assert_eq!(seen, [1; 27], "{geometry:?}");
        }
    }

    #[test]
    fn cpu_pair_geometries_triplet_x2() {
        for geometry in [R0Geometry::Cta288Pair, R0Geometry::Cta96Partitioned] {
            for selector in 0..9 {
                assert_eq!(
                    owned_cells(geometry, selector).unwrap(),
                    expected_pair_cells(selector),
                    "{geometry:?} selector {selector}",
                );
            }
        }
    }

    #[test]
    fn cpu_axis_major_geometries_pin_fixed_triplet_and_enumerated_axes() {
        for fixed in 0..3 {
            let x0_major = (0..3)
                .flat_map(|x1| (0..3).map(move |x2| (9 * fixed + 3 * x1 + x2) as u8))
                .collect::<Vec<_>>();
            assert_eq!(
                owned_cells(R0Geometry::Cta96X0Major, fixed).unwrap(),
                x0_major,
            );

            let x1_major = (0..3)
                .flat_map(|x0| (0..3).map(move |x2| (9 * x0 + 3 * fixed + x2) as u8))
                .collect::<Vec<_>>();
            assert_eq!(
                owned_cells(R0Geometry::Cta96X1Major, fixed).unwrap(),
                x1_major,
            );

            let x2_major = (0..3)
                .flat_map(|x0| (0..3).map(move |x1| (9 * x0 + 3 * x1 + fixed) as u8))
                .collect::<Vec<_>>();
            assert_eq!(
                owned_cells(R0Geometry::Cta96X2Major, fixed).unwrap(),
                x2_major,
            );
        }
    }

    #[test]
    fn cpu_r0_launch_plans_pin_grid_block_and_partial_rows() {
        let pair = R0Geometry::Cta288Pair.launch_plan(9).unwrap();
        assert_eq!(pair.grid, [2, 1, 1]);
        assert_eq!(pair.block, [288, 1, 1]);
        assert_eq!(pair.row_tiles, 2);
        assert_eq!(pair.partial_rows, 2);

        let partitioned = R0Geometry::Cta96Partitioned.launch_plan(9).unwrap();
        assert_eq!(partitioned.grid, [6, 1, 1]);
        assert_eq!(partitioned.block, [96, 1, 1]);
        assert_eq!(partitioned.row_tiles, 2);
        assert_eq!(partitioned.partial_rows, 2);
        assert_eq!(partitioned_row_owner(5).unwrap(), (1, 2));
        for block_in_tile in 0..3 {
            for warp in 0..3 {
                assert_eq!(
                    partitioned_selector(block_in_tile, warp).unwrap(),
                    3 * block_in_tile + warp,
                );
            }
        }
        assert!(partitioned_selector(3, 0).is_err());
        assert!(partitioned_selector(0, 3).is_err());

        for geometry in [
            R0Geometry::Cta96X0Major,
            R0Geometry::Cta96X1Major,
            R0Geometry::Cta96X2Major,
        ] {
            let plan = geometry.launch_plan(9).unwrap();
            assert_eq!(plan.grid, [2, 1, 1]);
            assert_eq!(plan.block, [96, 1, 1]);
            assert_eq!(plan.partial_rows, 2);
        }
        assert!(R0Geometry::Cta288Pair.launch_plan(2).is_err());
        assert!(R0Geometry::Cta288Pair.launch_plan(28).is_err());
    }

    #[test]
    fn cpu_r0_memory_preflight_extends_the_shared_lean_binding_plan() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let coordinate = &bundle.coordinates[0];
        let lean = crate::geometry::build_lean_allocation_plan(&coordinate.binding, 9).unwrap();
        let preflight =
            R0MemoryPreflight::for_coordinate(coordinate, 9, 4_096, Some((1_000_000, 2_000_000)))
                .unwrap();
        assert_eq!(
            preflight.source_backing_bytes,
            lean.backings
                .iter()
                .map(|backing| backing.bytes as u64)
                .collect::<Vec<_>>(),
        );
        assert_eq!(
            preflight.source_slots as usize,
            coordinate.binding.source_slots.len()
        );
        assert_eq!(preflight.partial_bytes, 2 * 27 * 16);
        assert_eq!(preflight.final_bytes, 27 * 16);
        assert_eq!(
            preflight.coefficient_bytes,
            coordinate.recipes.len() as u64 * 16
        );
        assert_eq!(preflight.descriptor_bytes, 17_536);
        assert_eq!(preflight.runtime_bytes, 4_096);
        assert_eq!(preflight.device_free_bytes, Some(1_000_000));
        assert_eq!(preflight.device_total_bytes, Some(2_000_000));
        assert_eq!(
            preflight.requested_bytes,
            preflight.source_backing_bytes.iter().sum::<u64>()
                + preflight.eq_low_bytes
                + preflight.eq_high_bytes
                + preflight.partial_bytes
                + preflight.final_bytes
                + preflight.coefficient_bytes
                + preflight.descriptor_bytes
                + preflight.runtime_bytes,
        );
    }
}
