use std::collections::BTreeMap;

use crate::abi::{
    WindowEqSizes, ORIGIN_PROCEDURAL, ORIGIN_READ_BASE, ORIGIN_READ_EXT, WINDOW_CELLS,
};
use crate::artifact::{
    validate_artifact, ArtifactError, FrozenArtifact, FrozenField, FrozenWindowFamily,
};

#[cfg(feature = "artifact-gen")]
use gkr_eval_ir::FieldKind;
#[cfg(feature = "artifact-gen")]
use gpu_gkr_compiler::backward::{LeanSourceBinding, WindowFamily};

pub const MAX_LOG_TRACE: u32 = 27;
const EQ_GROUP_BITS: u32 = 8;

#[cfg(test)]
pub(crate) fn selector_id(block_within_tile: u32, warp: u32, warps_per_block: u32) -> u32 {
    block_within_tile * warps_per_block + warp
}

pub(crate) fn vm_grid_blocks(row_tiles: u32, warps_per_block: u32) -> u32 {
    assert!(warps_per_block != 0 && 9 % warps_per_block == 0);
    row_tiles.checked_mul(9 / warps_per_block).unwrap()
}

#[cfg(test)]
pub(crate) fn row_tile(block: u32, warps_per_block: u32) -> u32 {
    assert!(warps_per_block != 0 && 9 % warps_per_block == 0);
    block / (9 / warps_per_block)
}

#[cfg(test)]
pub(crate) fn block_within_row_tile(block: u32, warps_per_block: u32) -> u32 {
    assert!(warps_per_block != 0 && 9 % warps_per_block == 0);
    block % (9 / warps_per_block)
}

#[cfg(test)]
pub(crate) fn partial_index(row_tile: u32, selector: u32, cell: u32) -> usize {
    (row_tile * WINDOW_CELLS + 3 * selector + cell) as usize
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BackingPlan {
    pub family: FrozenWindowFamily,
    pub field: FrozenField,
    pub columns: u32,
    pub stride_elements: usize,
    pub stride_bytes: usize,
    pub bytes: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WindowPlan {
    pub family: FrozenWindowFamily,
    pub field: FrozenField,
    pub backing: Option<usize>,
    pub base_offset_bytes: usize,
    pub log2_stride: u8,
    pub origin: u8,
    pub procedural_kind: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AllocationPlan {
    pub log_trace: u32,
    pub log_rows: u32,
    pub trace_len: usize,
    pub logical_rows: u32,
    pub num_blocks: u32,
    pub eq_sizes: WindowEqSizes,
    pub eq_low_elements: usize,
    pub partial_elements: usize,
    pub final_elements: usize,
    pub backings: Vec<BackingPlan>,
    pub windows: Vec<WindowPlan>,
}

#[cfg(feature = "artifact-gen")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanBackingPlan {
    pub family: WindowFamily,
    pub field: FieldKind,
    pub columns: usize,
    pub stride_elements: usize,
    pub stride_bytes: usize,
    pub bytes: usize,
}

#[cfg(feature = "artifact-gen")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanWindowPlan {
    pub family: WindowFamily,
    pub field: FieldKind,
    pub backing: Option<usize>,
    pub base_element: usize,
    pub base_offset_bytes: usize,
    pub log2_stride: u8,
    pub origin: u8,
    pub procedural_kind: Option<u8>,
}

#[cfg(feature = "artifact-gen")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanAllocationPlan {
    pub log_trace: u32,
    pub log_rows: u32,
    pub trace_len: usize,
    pub logical_rows: u32,
    pub num_blocks: u32,
    pub eq_sizes: WindowEqSizes,
    pub eq_low_elements: usize,
    pub partial_elements: usize,
    pub final_elements: usize,
    pub backings: Vec<LeanBackingPlan>,
    pub windows: Vec<LeanWindowPlan>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GeometryError {
    Artifact(ArtifactError),
    UnsupportedLogTrace { log_trace: u32 },
    SizeOverflow { resource: &'static str },
    MissingBacking { window: usize },
    BackingFieldMismatch { window: usize },
}

impl core::fmt::Display for GeometryError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for GeometryError {}

pub fn make_eq_sizes(log_trace: u32) -> Result<WindowEqSizes, GeometryError> {
    if !(3..=MAX_LOG_TRACE).contains(&log_trace) {
        return Err(GeometryError::UnsupportedLogTrace { log_trace });
    }
    let challenge_count = log_trace - 3;
    let group_count = challenge_count.div_ceil(EQ_GROUP_BITS);
    let mut high = [0; 2];
    let mut low = 0;
    let mut consumed = 0;
    let mut high_index = 0;
    for group in 0..group_count {
        let group_size = (challenge_count - consumed).min(EQ_GROUP_BITS);
        if group + 1 == group_count {
            low = group_size;
        } else {
            high[high_index] = group_size;
            high_index += 1;
        }
        consumed += group_size;
    }
    Ok(WindowEqSizes { high, low })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StorageField {
    Base,
    Ext,
}

impl StorageField {
    const fn bytes(self) -> usize {
        match self {
            Self::Base => 4,
            Self::Ext => 16,
        }
    }
}

#[derive(Clone, Copy)]
struct BindingWindowSpec<Family> {
    family: Family,
    field: StorageField,
    first_column: usize,
    columns: usize,
    procedural_kind: Option<u8>,
}

struct GenericBackingPlan<Family> {
    family: Family,
    field: StorageField,
    columns: usize,
    stride_elements: usize,
    stride_bytes: usize,
    bytes: usize,
}

struct GenericWindowPlan<Family> {
    family: Family,
    field: StorageField,
    backing: Option<usize>,
    base_element: usize,
    base_offset_bytes: usize,
    procedural_kind: Option<u8>,
}

struct GenericBindingPlan<Family> {
    trace_len: usize,
    backings: Vec<GenericBackingPlan<Family>>,
    windows: Vec<GenericWindowPlan<Family>>,
}

fn build_binding_allocation_core<Family: Copy + Ord>(
    windows: &[BindingWindowSpec<Family>],
    log_trace: u32,
) -> Result<GenericBindingPlan<Family>, GeometryError> {
    if !(3..=MAX_LOG_TRACE).contains(&log_trace) {
        return Err(GeometryError::UnsupportedLogTrace { log_trace });
    }
    let trace_len = 1usize
        .checked_shl(log_trace)
        .ok_or(GeometryError::SizeOverflow {
            resource: "trace length",
        })?;
    let mut aggregate = BTreeMap::<Family, (StorageField, usize)>::new();
    for (window, spec) in windows.iter().enumerate() {
        if spec.procedural_kind.is_some() {
            continue;
        }
        match aggregate.entry(spec.family) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert((spec.field, spec.columns));
            }
            std::collections::btree_map::Entry::Occupied(mut entry) => {
                if entry.get().0 != spec.field {
                    return Err(GeometryError::BackingFieldMismatch { window });
                }
                entry.get_mut().1 = entry.get().1.max(spec.columns);
            }
        }
    }

    let mut backing_index = BTreeMap::new();
    let mut backings = Vec::with_capacity(aggregate.len());
    for (family, (field, columns)) in aggregate {
        let stride_bytes =
            trace_len
                .checked_mul(field.bytes())
                .ok_or(GeometryError::SizeOverflow {
                    resource: "backing stride",
                })?;
        let bytes = columns
            .checked_mul(stride_bytes)
            .ok_or(GeometryError::SizeOverflow {
                resource: "backing allocation",
            })?;
        backing_index.insert(family, backings.len());
        backings.push(GenericBackingPlan {
            family,
            field,
            columns,
            stride_elements: trace_len,
            stride_bytes,
            bytes,
        });
    }

    let mut planned_windows = Vec::with_capacity(windows.len());
    for (window, spec) in windows.iter().enumerate() {
        let (backing, base_element, base_offset_bytes) = if spec.procedural_kind.is_some() {
            (None, 0, 0)
        } else {
            let backing = backing_index
                .get(&spec.family)
                .copied()
                .ok_or(GeometryError::MissingBacking { window })?;
            let base_element =
                spec.first_column
                    .checked_mul(trace_len)
                    .ok_or(GeometryError::SizeOverflow {
                        resource: "window base element",
                    })?;
            let base_offset_bytes = spec
                .first_column
                .checked_mul(backings[backing].stride_bytes)
                .ok_or(GeometryError::SizeOverflow {
                    resource: "window base offset",
                })?;
            (Some(backing), base_element, base_offset_bytes)
        };
        planned_windows.push(GenericWindowPlan {
            family: spec.family,
            field: spec.field,
            backing,
            base_element,
            base_offset_bytes,
            procedural_kind: spec.procedural_kind,
        });
    }
    Ok(GenericBindingPlan {
        trace_len,
        backings,
        windows: planned_windows,
    })
}

pub fn build_allocation_plan(
    artifact: &FrozenArtifact,
    log_trace: u32,
) -> Result<AllocationPlan, GeometryError> {
    validate_artifact(artifact).map_err(GeometryError::Artifact)?;
    let eq_sizes = make_eq_sizes(log_trace)?;
    let specs = artifact
        .windows
        .iter()
        .map(|window| {
            let columns = window
                .columns
                .last()
                .map(|column| {
                    usize::try_from(column.column)
                        .ok()
                        .and_then(|column| column.checked_add(1))
                        .ok_or(GeometryError::SizeOverflow {
                            resource: "backing columns",
                        })
                })
                .transpose()?
                .unwrap_or(usize::try_from(window.first_column).map_err(|_| {
                    GeometryError::SizeOverflow {
                        resource: "backing columns",
                    }
                })?);
            Ok(BindingWindowSpec {
                family: window.family,
                field: match window.field {
                    FrozenField::Base => StorageField::Base,
                    FrozenField::Ext => StorageField::Ext,
                },
                first_column: window.first_column as usize,
                columns,
                procedural_kind: match window.family {
                    FrozenWindowFamily::VirtualSetup { kind } => Some(kind),
                    _ => None,
                },
            })
        })
        .collect::<Result<Vec<_>, GeometryError>>()?;
    let binding = build_binding_allocation_core(&specs, log_trace)?;
    let trace_len = binding.trace_len;
    let logical_rows = u32::try_from(trace_len / 8).map_err(|_| GeometryError::SizeOverflow {
        resource: "logical rows",
    })?;
    let num_blocks = logical_rows.div_ceil(32);

    let backings = binding
        .backings
        .into_iter()
        .map(|backing| {
            Ok(BackingPlan {
                family: backing.family,
                field: match backing.field {
                    StorageField::Base => FrozenField::Base,
                    StorageField::Ext => FrozenField::Ext,
                },
                columns: u32::try_from(backing.columns).map_err(|_| {
                    GeometryError::SizeOverflow {
                        resource: "backing columns",
                    }
                })?,
                stride_elements: backing.stride_elements,
                stride_bytes: backing.stride_bytes,
                bytes: backing.bytes,
            })
        })
        .collect::<Result<Vec<_>, GeometryError>>()?;
    let windows = binding
        .windows
        .into_iter()
        .map(|window| WindowPlan {
            family: window.family,
            field: match window.field {
                StorageField::Base => FrozenField::Base,
                StorageField::Ext => FrozenField::Ext,
            },
            backing: window.backing,
            base_offset_bytes: window.base_offset_bytes,
            log2_stride: log_trace as u8,
            origin: if window.procedural_kind.is_some() {
                ORIGIN_PROCEDURAL
            } else {
                match window.field {
                    StorageField::Base => ORIGIN_READ_BASE,
                    StorageField::Ext => ORIGIN_READ_EXT,
                }
            },
            procedural_kind: window.procedural_kind.unwrap_or(u8::MAX),
        })
        .collect();

    let partial_elements = usize::try_from(num_blocks)
        .ok()
        .and_then(|blocks| blocks.checked_mul(WINDOW_CELLS as usize))
        .ok_or(GeometryError::SizeOverflow {
            resource: "partial output",
        })?;
    let eq_low_elements = 1usize
        .checked_shl(eq_sizes.low)
        .ok_or(GeometryError::SizeOverflow {
            resource: "low equality table",
        })?;
    Ok(AllocationPlan {
        log_trace,
        log_rows: log_trace - 3,
        trace_len,
        logical_rows,
        num_blocks,
        eq_sizes,
        eq_low_elements,
        partial_elements,
        final_elements: WINDOW_CELLS as usize,
        backings,
        windows,
    })
}

#[cfg(feature = "artifact-gen")]
pub fn build_lean_allocation_plan(
    binding: &LeanSourceBinding,
    log_trace: u32,
) -> Result<LeanAllocationPlan, GeometryError> {
    let eq_sizes = make_eq_sizes(log_trace)?;
    let specs = binding
        .windows
        .iter()
        .map(|window| {
            let columns =
                window
                    .columns
                    .iter()
                    .try_fold(window.first_column, |highest, column| {
                        column
                            .column
                            .checked_add(1)
                            .map(|end| highest.max(end))
                            .ok_or(GeometryError::SizeOverflow {
                                resource: "backing columns",
                            })
                    })?;
            Ok(BindingWindowSpec {
                family: window.family,
                field: match window.backing_field() {
                    FieldKind::Base => StorageField::Base,
                    FieldKind::Ext => StorageField::Ext,
                },
                first_column: window.first_column,
                columns,
                procedural_kind: window.procedural_kind(),
            })
        })
        .collect::<Result<Vec<_>, GeometryError>>()?;
    let plan = build_binding_allocation_core(&specs, log_trace)?;
    let logical_rows =
        u32::try_from(plan.trace_len / 8).map_err(|_| GeometryError::SizeOverflow {
            resource: "logical rows",
        })?;
    let num_blocks = logical_rows.div_ceil(32);
    let partial_elements = usize::try_from(num_blocks)
        .ok()
        .and_then(|blocks| blocks.checked_mul(WINDOW_CELLS as usize))
        .ok_or(GeometryError::SizeOverflow {
            resource: "partial output",
        })?;
    let eq_low_elements = 1usize
        .checked_shl(eq_sizes.low)
        .ok_or(GeometryError::SizeOverflow {
            resource: "low equality table",
        })?;
    Ok(LeanAllocationPlan {
        log_trace,
        log_rows: log_trace - 3,
        trace_len: plan.trace_len,
        logical_rows,
        num_blocks,
        eq_sizes,
        eq_low_elements,
        partial_elements,
        final_elements: WINDOW_CELLS as usize,
        backings: plan
            .backings
            .into_iter()
            .map(|backing| LeanBackingPlan {
                family: backing.family,
                field: match backing.field {
                    StorageField::Base => FieldKind::Base,
                    StorageField::Ext => FieldKind::Ext,
                },
                columns: backing.columns,
                stride_elements: backing.stride_elements,
                stride_bytes: backing.stride_bytes,
                bytes: backing.bytes,
            })
            .collect(),
        windows: plan
            .windows
            .into_iter()
            .map(|window| LeanWindowPlan {
                family: window.family,
                field: match window.field {
                    StorageField::Base => FieldKind::Base,
                    StorageField::Ext => FieldKind::Ext,
                },
                backing: window.backing,
                base_element: window.base_element,
                base_offset_bytes: window.base_offset_bytes,
                log2_stride: log_trace as u8,
                origin: if window.procedural_kind.is_some() {
                    ORIGIN_PROCEDURAL
                } else {
                    match window.field {
                        StorageField::Base => ORIGIN_READ_BASE,
                        StorageField::Ext => ORIGIN_READ_EXT,
                    }
                },
                procedural_kind: window.procedural_kind,
            })
            .collect(),
    })
}

#[cfg(test)]
pub(crate) mod tests {
    use crate::abi::WindowInstruction;
    use crate::artifact::{
        FrozenArtifact, FrozenBoundColumn, FrozenField, FrozenSourceSlot, FrozenWindow,
        FrozenWindowFamily, WindowClass, ARTIFACT_MAGIC, ARTIFACT_VERSION, SOURCE_NONE,
    };

    use super::*;

    pub(crate) fn geometry_fixture() -> FrozenArtifact {
        FrozenArtifact {
            magic: ARTIFACT_MAGIC,
            version: ARTIFACT_VERSION,
            layer: 0,
            term_count: 1,
            record_count: 1,
            coefficient_count: 2,
            c_init_coeff: None,
            program: vec![WindowInstruction {
                term_class: WindowClass::LinearBf as u16,
                factor: 0,
                source_a: 0,
                source_b: SOURCE_NONE,
            }],
            immediates: Vec::new(),
            windows: vec![
                FrozenWindow {
                    family: FrozenWindowFamily::BaseLayerMemory,
                    first_column: 0,
                    field: FrozenField::Base,
                    columns: vec![FrozenBoundColumn {
                        column: 0,
                        source: 0,
                    }],
                },
                FrozenWindow {
                    family: FrozenWindowFamily::BaseLayerMemory,
                    first_column: 128,
                    field: FrozenField::Base,
                    columns: vec![FrozenBoundColumn {
                        column: 130,
                        source: 1,
                    }],
                },
                FrozenWindow {
                    family: FrozenWindowFamily::LayerOutput {
                        layer: 0,
                        ext: true,
                    },
                    first_column: 0,
                    field: FrozenField::Ext,
                    columns: vec![FrozenBoundColumn {
                        column: 3,
                        source: 2,
                    }],
                },
                FrozenWindow {
                    family: FrozenWindowFamily::VirtualSetup { kind: 1 },
                    first_column: 0,
                    field: FrozenField::Base,
                    columns: vec![FrozenBoundColumn {
                        column: 0,
                        source: 3,
                    }],
                },
            ],
            source_slots: vec![
                FrozenSourceSlot {
                    window: 0,
                    column: 0,
                },
                FrozenSourceSlot {
                    window: 1,
                    column: 2,
                },
                FrozenSourceSlot {
                    window: 2,
                    column: 3,
                },
                FrozenSourceSlot {
                    window: 3,
                    column: 0,
                },
            ],
        }
    }

    #[test]
    fn selector_partition_is_bijective_for_nine_and_three_warp_blocks() {
        for warps in [9, 3] {
            let blocks_per_tile = 9 / warps;
            let mut ids = Vec::new();
            for block in 0..blocks_per_tile {
                for warp in 0..warps {
                    ids.push(selector_id(block, warp, warps));
                }
            }
            ids.sort_unstable();
            assert_eq!(ids, (0..9).collect::<Vec<_>>());
        }
    }

    #[test]
    fn partitioned_grid_triples_vm_blocks_but_not_partial_rows() {
        assert_eq!(vm_grid_blocks(17, 9), 17);
        assert_eq!(vm_grid_blocks(17, 3), 51);
        assert_eq!(partial_index(4, 8, 2), 4 * 27 + 8 * 3 + 2);
    }

    #[test]
    fn partitioned_tail_row_uses_the_original_row_tile() {
        assert_eq!(row_tile(50, 3), 16);
        assert_eq!(block_within_row_tile(50, 3), 2);
    }

    #[test]
    fn trace_geometry_uses_three_bound_bits() {
        let plan = build_allocation_plan(&geometry_fixture(), 8).unwrap();
        assert_eq!(plan.trace_len, 256);
        assert_eq!(plan.log_rows, 5);
        assert_eq!(plan.logical_rows, 32);
        assert_eq!(plan.num_blocks, 1);
        assert_eq!(plan.partial_elements, 27);
        assert_eq!(plan.final_elements, 27);
    }

    #[test]
    fn direct_window_offsets_support_packed_load_alignment_at_minimum_trace() {
        let plan = build_allocation_plan(&geometry_fixture(), 3).unwrap();
        for window in plan
            .windows
            .iter()
            .filter(|window| window.backing.is_some())
        {
            assert_eq!(window.base_offset_bytes % 32, 0);
        }
    }

    #[test]
    fn unsupported_trace_sizes_are_rejected() {
        assert!(matches!(
            build_allocation_plan(&geometry_fixture(), 2),
            Err(GeometryError::UnsupportedLogTrace { .. })
        ));
        assert!(matches!(
            build_allocation_plan(&geometry_fixture(), 28),
            Err(GeometryError::UnsupportedLogTrace { .. })
        ));
    }

    #[test]
    fn factored_eq_sizes_cover_only_suffix_bits() {
        assert_eq!(
            make_eq_sizes(3).unwrap(),
            WindowEqSizes {
                high: [0, 0],
                low: 0
            }
        );
        assert_eq!(
            make_eq_sizes(11).unwrap(),
            WindowEqSizes {
                high: [0, 0],
                low: 8
            }
        );
        assert_eq!(
            make_eq_sizes(12).unwrap(),
            WindowEqSizes {
                high: [8, 0],
                low: 1
            }
        );
        assert_eq!(
            make_eq_sizes(20).unwrap(),
            WindowEqSizes {
                high: [8, 8],
                low: 1
            }
        );
        assert!(make_eq_sizes(28).is_err());
    }

    #[test]
    fn shared_families_share_allocations_but_keep_window_offsets() {
        let plan = build_allocation_plan(&geometry_fixture(), 8).unwrap();
        assert_eq!(plan.backings.len(), 2);
        let base = &plan.backings[0];
        assert_eq!(base.family, FrozenWindowFamily::BaseLayerMemory);
        assert_eq!(base.columns, 131);
        assert_eq!(base.stride_elements, 256);
        assert_eq!(base.stride_bytes, 1024);
        assert_eq!(base.bytes, 131 * 1024);
        assert_eq!(plan.windows[0].backing, Some(0));
        assert_eq!(plan.windows[1].backing, Some(0));
        assert_eq!(plan.windows[1].base_offset_bytes, 128 * 1024);

        let ext = &plan.backings[1];
        assert_eq!(ext.columns, 4);
        assert_eq!(ext.stride_bytes, 4096);
        assert_eq!(ext.bytes, 4 * 4096);
        assert_eq!(
            plan.windows[3].family,
            FrozenWindowFamily::VirtualSetup { kind: 1 }
        );
        assert_eq!(plan.windows[3].backing, None);
        assert_eq!(plan.windows[3].base_offset_bytes, 0);
    }

    #[cfg(feature = "artifact-gen")]
    #[test]
    fn lean_allocation_uses_the_highest_column_independent_of_input_order() {
        use gpu_gkr_compiler::backward::{
            LeanBoundColumn, LeanBoundWindow, LeanSourceBinding, WindowFamily,
        };

        let binding = LeanSourceBinding {
            windows: vec![LeanBoundWindow {
                family: WindowFamily::BaseLayerMemory,
                first_column: 0,
                columns: vec![
                    LeanBoundColumn {
                        column: 5,
                        source: 0,
                    },
                    LeanBoundColumn {
                        column: 2,
                        source: 1,
                    },
                ],
            }],
            source_slots: Vec::new(),
        };

        let plan = build_lean_allocation_plan(&binding, 3).unwrap();
        assert_eq!(plan.backings.len(), 1);
        assert_eq!(plan.backings[0].columns, 6);
    }
}
