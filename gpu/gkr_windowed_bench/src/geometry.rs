use std::collections::BTreeMap;

use crate::abi::{
    WindowEqSizes, ORIGIN_PROCEDURAL, ORIGIN_READ_BASE, ORIGIN_READ_EXT, WINDOW_CELLS,
};
use crate::artifact::{
    validate_artifact, ArtifactError, FrozenArtifact, FrozenField, FrozenWindowFamily,
};

pub const MAX_LOG_TRACE: u32 = 27;
const EQ_GROUP_BITS: u32 = 8;

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GeometryError {
    Artifact(ArtifactError),
    UnsupportedLogTrace { log_trace: u32 },
    SizeOverflow { resource: &'static str },
    MissingBacking { window: usize },
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

pub fn build_allocation_plan(
    artifact: &FrozenArtifact,
    log_trace: u32,
) -> Result<AllocationPlan, GeometryError> {
    validate_artifact(artifact).map_err(GeometryError::Artifact)?;
    let eq_sizes = make_eq_sizes(log_trace)?;
    let trace_len = 1usize
        .checked_shl(log_trace)
        .ok_or(GeometryError::SizeOverflow {
            resource: "trace length",
        })?;
    let logical_rows = u32::try_from(trace_len / 8).map_err(|_| GeometryError::SizeOverflow {
        resource: "logical rows",
    })?;
    let num_blocks = logical_rows.div_ceil(32);

    let mut aggregate = BTreeMap::<FrozenWindowFamily, (FrozenField, u32)>::new();
    for window in &artifact.windows {
        if window.family.is_procedural() {
            continue;
        }
        let columns = window
            .columns
            .last()
            .map(|column| column.column + 1)
            .unwrap_or(window.first_column);
        aggregate
            .entry(window.family)
            .and_modify(|(_, maximum)| *maximum = (*maximum).max(columns))
            .or_insert((window.field, columns));
    }

    let mut backing_index = BTreeMap::new();
    let mut backings = Vec::with_capacity(aggregate.len());
    for (family, (field, columns)) in aggregate {
        let field_bytes = match field {
            FrozenField::Base => 4,
            FrozenField::Ext => 16,
        };
        let stride_bytes =
            trace_len
                .checked_mul(field_bytes)
                .ok_or(GeometryError::SizeOverflow {
                    resource: "backing stride",
                })?;
        let bytes = usize::try_from(columns)
            .ok()
            .and_then(|columns| columns.checked_mul(stride_bytes))
            .ok_or(GeometryError::SizeOverflow {
                resource: "backing allocation",
            })?;
        backing_index.insert(family, backings.len());
        backings.push(BackingPlan {
            family,
            field,
            columns,
            stride_elements: trace_len,
            stride_bytes,
            bytes,
        });
    }

    let mut windows = Vec::with_capacity(artifact.windows.len());
    for (window_index, window) in artifact.windows.iter().enumerate() {
        if let FrozenWindowFamily::VirtualSetup { kind } = window.family {
            windows.push(WindowPlan {
                family: window.family,
                field: window.field,
                backing: None,
                base_offset_bytes: 0,
                log2_stride: log_trace as u8,
                origin: ORIGIN_PROCEDURAL,
                procedural_kind: kind,
            });
            continue;
        }
        let index =
            backing_index
                .get(&window.family)
                .copied()
                .ok_or(GeometryError::MissingBacking {
                    window: window_index,
                })?;
        let base_offset_bytes = usize::try_from(window.first_column)
            .ok()
            .and_then(|column| column.checked_mul(backings[index].stride_bytes))
            .ok_or(GeometryError::SizeOverflow {
                resource: "window base offset",
            })?;
        let origin = match window.field {
            FrozenField::Base => ORIGIN_READ_BASE,
            FrozenField::Ext => ORIGIN_READ_EXT,
        };
        windows.push(WindowPlan {
            family: window.family,
            field: window.field,
            backing: Some(index),
            base_offset_bytes,
            log2_stride: log_trace as u8,
            origin,
            procedural_kind: u8::MAX,
        });
    }

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
}
