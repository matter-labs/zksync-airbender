use core::mem::{align_of, offset_of, size_of};

use gpu_gkr_compiler::GpuResourceProfile;
use serde::{Deserialize, Serialize};

use crate::abi::{WindowEqSizes, E4};
use crate::r0_artifact::{
    pack_r0_source, validate_r0_coordinate, FrozenR0Coordinate, R0ArtifactError,
};

pub const R0_RECORD_WORDS: usize = 4;
pub const R0_RECORD_CAPACITY: usize = 1_791;
pub const R0_PROGRAM_WORDS: usize = 7_164;
pub const R0_SOURCE_SLOTS: usize = 1_062;
pub const R0_WINDOW_CAPACITY: usize = 64;
pub const R0_WINDOW_COLUMN_CAPACITY: usize = 128;
// The canonical R0 corpus uses at most 1,138 recipes.  The sectioned executor
// additionally stores four resolved basis products per extracted linear-E4
// core; its checked maximum is 1,665, with 63 spare entries for format growth.
pub const R0_COEFFICIENT_CAPACITY: usize = 1_728;
pub const R0_IMMEDIATE_CAPACITY: usize = 512;
pub const R0_PROJECTION_CAPACITY: usize = 1_731;
pub const R0_EQ_HIGH_ELEMENTS: usize = 512;
pub const R0_HISTORICAL_COEFFICIENT_ELEMENTS: usize = 80;
pub const R0_HISTORICAL_EQ_HIGH_ELEMENTS: usize = 512;
pub const R0_CONSTANT_FOOTPRINT_BYTES: usize = (R0_HISTORICAL_COEFFICIENT_ELEMENTS
    + R0_HISTORICAL_EQ_HIGH_ELEMENTS
    + R0_COEFFICIENT_CAPACITY
    + R0_EQ_HIGH_ELEMENTS)
    * size_of::<E4>();
pub const CUDA_CONSTANT_MEMORY_CEILING_BYTES: usize = 65_536;
pub const KERNEL_ARGUMENT_CEILING_BYTES: usize = crate::abi::KERNEL_ARGUMENT_CEILING_BYTES;
pub const R0_COEFFICIENT_ONE: u32 = 0;
pub const R0_COEFFICIENT_NEG_ONE: u32 = 1;
pub const R0_COEFFICIENT_BANK_BIAS: u32 = 2;
pub const R0_CLASS_C0_LINEAR_BF: u8 = 0;
pub const R0_CLASS_C0_LINEAR_E4: u8 = 1;
pub const R0_CLASS_C2_PRODUCT_BF_BF: u8 = 2;
pub const R0_CLASS_C2_PRODUCT_BF_E4: u8 = 3;
pub const R0_CLASS_C2_PRODUCT_E4_E4: u8 = 4;
pub const R0_SOURCE_WINDOW_BITS: u32 = 6;
pub const R0_SOURCE_COLUMN_BITS: u32 = 7;
pub const R0_SOURCE_WINDOW_MASK: u16 = (1 << R0_SOURCE_WINDOW_BITS) - 1;
pub const R0_SOURCE_COLUMN_MASK: u16 = (1 << R0_SOURCE_COLUMN_BITS) - 1;

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct R0WindowAddr {
    pub base: *const u8,
    pub log2_stride: u8,
    pub origin: u8,
    pub procedural_kind: u8,
    pub reserved: [u8; 5],
}

impl Default for R0WindowAddr {
    fn default() -> Self {
        Self {
            base: core::ptr::null(),
            log2_stride: 0,
            origin: 0,
            procedural_kind: 0,
            reserved: [0; 5],
        }
    }
}

impl R0WindowAddr {
    pub fn is_zero(&self) -> bool {
        self.base.is_null()
            && self.log2_stride == 0
            && self.origin == 0
            && self.procedural_kind == 0
            && self.reserved == [0; 5]
    }
}

#[repr(C, align(16))]
#[derive(Clone, Copy, Debug)]
pub struct R0VmDesc {
    pub window_bases: [R0WindowAddr; R0_WINDOW_CAPACITY],
    pub program: [u16; R0_PROGRAM_WORDS],
    pub eq_low: *const E4,
    pub partials: *mut E4,
    pub log_rows: u32,
    pub record_count: u32,
    pub source_count: u32,
    pub window_count: u32,
    pub banked_coefficient_count: u32,
    pub c_init: u32,
    pub eq_sizes: WindowEqSizes,
    pub source_slots: [u16; R0_SOURCE_SLOTS],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum R0CoefficientRef {
    One,
    NegOne,
    Banked(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R0AbiError {
    Capacity {
        resource: &'static str,
        required: usize,
        capacity: usize,
    },
    InvalidLogTrace(u32),
    InvalidEqSizes {
        log_trace: u32,
        expected: WindowEqSizes,
        actual: WindowEqSizes,
    },
    CInitPresent,
    ProgramMisaligned,
    RecordCountMismatch,
    WindowCountMismatch {
        binding: usize,
        addresses: usize,
    },
    InvalidWindowAddress {
        window: usize,
    },
    InvalidBinding {
        source: usize,
    },
    InvalidClass {
        record: usize,
        class: u8,
    },
    InvalidCoefficient {
        record: usize,
        coefficient: u32,
    },
    InvalidSource {
        record: usize,
        source: u16,
    },
    InvalidArity {
        record: usize,
    },
    ReservedWordNonZero {
        record: usize,
    },
    Artifact(R0ArtifactError),
    NativeProbeUnavailable,
}

impl core::fmt::Display for R0AbiError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for R0AbiError {}

pub fn classify_r0_coefficient(
    coefficient: u32,
    banked_coefficient_count: usize,
) -> Result<R0CoefficientRef, R0AbiError> {
    match coefficient {
        R0_COEFFICIENT_ONE => Ok(R0CoefficientRef::One),
        R0_COEFFICIENT_NEG_ONE => Ok(R0CoefficientRef::NegOne),
        _ => {
            let index = coefficient
                .checked_sub(R0_COEFFICIENT_BANK_BIAS)
                .and_then(|index| usize::try_from(index).ok())
                .filter(|index| *index < banked_coefficient_count)
                .ok_or(R0AbiError::InvalidCoefficient {
                    record: usize::MAX,
                    coefficient,
                })?;
            Ok(R0CoefficientRef::Banked(index))
        }
    }
}

pub fn validate_r0_coordinate_capacities(
    coordinate: &FrozenR0Coordinate,
) -> Result<(), R0AbiError> {
    validate_r0_coordinate(coordinate).map_err(R0AbiError::Artifact)
}

impl R0VmDesc {
    #[allow(clippy::too_many_arguments)]
    pub fn from_coordinate(
        coordinate: &FrozenR0Coordinate,
        window_bases: &[R0WindowAddr],
        log_trace: u32,
        eq_low: *const E4,
        partials: *mut E4,
        eq_sizes: WindowEqSizes,
        banked_coefficient_count: usize,
    ) -> Result<Self, R0AbiError> {
        validate_r0_coordinate_capacities(coordinate)?;
        if !(3..=27).contains(&log_trace) {
            return Err(R0AbiError::InvalidLogTrace(log_trace));
        }
        let expected_eq_sizes = crate::geometry::make_eq_sizes(log_trace)
            .map_err(|_| R0AbiError::InvalidLogTrace(log_trace))?;
        if eq_sizes != expected_eq_sizes {
            return Err(R0AbiError::InvalidEqSizes {
                log_trace,
                expected: expected_eq_sizes,
                actual: eq_sizes,
            });
        }
        if window_bases.len() != coordinate.binding.windows.len() {
            return Err(R0AbiError::WindowCountMismatch {
                binding: coordinate.binding.windows.len(),
                addresses: window_bases.len(),
            });
        }
        if let Some((window, _)) = window_bases
            .iter()
            .enumerate()
            .find(|(_, address)| address.reserved != [0; 5])
        {
            return Err(R0AbiError::InvalidWindowAddress { window });
        }
        if banked_coefficient_count != coordinate.recipes.len() {
            return Err(R0AbiError::Capacity {
                resource: "staged coefficients",
                required: banked_coefficient_count,
                capacity: coordinate.recipes.len(),
            });
        }

        let mut desc = Self {
            window_bases: [R0WindowAddr::default(); R0_WINDOW_CAPACITY],
            program: [0; R0_PROGRAM_WORDS],
            eq_low,
            partials,
            log_rows: log_trace - 3,
            record_count: coordinate.term_count,
            source_count: coordinate.binding.source_slots.len() as u32,
            window_count: coordinate.binding.windows.len() as u32,
            banked_coefficient_count: banked_coefficient_count as u32,
            c_init: crate::abi::C_INIT_NONE,
            eq_sizes,
            source_slots: [0; R0_SOURCE_SLOTS],
        };
        desc.window_bases[..window_bases.len()].copy_from_slice(window_bases);
        desc.program[..coordinate.program_words.len()].copy_from_slice(&coordinate.program_words);
        for (destination, source) in desc
            .source_slots
            .iter_mut()
            .zip(&coordinate.binding.source_slots)
        {
            *destination = pack_r0_source(source.window, source.column)
                .map_err(|_| R0AbiError::InvalidBinding { source: 0 })?;
        }
        Ok(desc)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct R0AbiLayout {
    pub window_addr_size: u64,
    pub window_addr_align: u64,
    pub window_addr_base: u64,
    pub window_addr_log2_stride: u64,
    pub window_addr_origin: u64,
    pub window_addr_procedural_kind: u64,
    pub window_addr_reserved: u64,
    pub eq_sizes_size: u64,
    pub eq_sizes_align: u64,
    pub eq_sizes_high: u64,
    pub eq_sizes_low: u64,
    pub vm_desc_size: u64,
    pub vm_desc_align: u64,
    pub vm_desc_window_bases: u64,
    pub vm_desc_program: u64,
    pub vm_desc_eq_low: u64,
    pub vm_desc_partials: u64,
    pub vm_desc_log_rows: u64,
    pub vm_desc_record_count: u64,
    pub vm_desc_source_count: u64,
    pub vm_desc_window_count: u64,
    pub vm_desc_banked_coefficient_count: u64,
    pub vm_desc_c_init: u64,
    pub vm_desc_eq_sizes: u64,
    pub vm_desc_source_slots: u64,
}

pub fn rust_r0_abi_layout() -> R0AbiLayout {
    R0AbiLayout {
        window_addr_size: size_of::<R0WindowAddr>() as u64,
        window_addr_align: align_of::<R0WindowAddr>() as u64,
        window_addr_base: offset_of!(R0WindowAddr, base) as u64,
        window_addr_log2_stride: offset_of!(R0WindowAddr, log2_stride) as u64,
        window_addr_origin: offset_of!(R0WindowAddr, origin) as u64,
        window_addr_procedural_kind: offset_of!(R0WindowAddr, procedural_kind) as u64,
        window_addr_reserved: offset_of!(R0WindowAddr, reserved) as u64,
        eq_sizes_size: size_of::<WindowEqSizes>() as u64,
        eq_sizes_align: align_of::<WindowEqSizes>() as u64,
        eq_sizes_high: offset_of!(WindowEqSizes, high) as u64,
        eq_sizes_low: offset_of!(WindowEqSizes, low) as u64,
        vm_desc_size: size_of::<R0VmDesc>() as u64,
        vm_desc_align: align_of::<R0VmDesc>() as u64,
        vm_desc_window_bases: offset_of!(R0VmDesc, window_bases) as u64,
        vm_desc_program: offset_of!(R0VmDesc, program) as u64,
        vm_desc_eq_low: offset_of!(R0VmDesc, eq_low) as u64,
        vm_desc_partials: offset_of!(R0VmDesc, partials) as u64,
        vm_desc_log_rows: offset_of!(R0VmDesc, log_rows) as u64,
        vm_desc_record_count: offset_of!(R0VmDesc, record_count) as u64,
        vm_desc_source_count: offset_of!(R0VmDesc, source_count) as u64,
        vm_desc_window_count: offset_of!(R0VmDesc, window_count) as u64,
        vm_desc_banked_coefficient_count: offset_of!(R0VmDesc, banked_coefficient_count) as u64,
        vm_desc_c_init: offset_of!(R0VmDesc, c_init) as u64,
        vm_desc_eq_sizes: offset_of!(R0VmDesc, eq_sizes) as u64,
        vm_desc_source_slots: offset_of!(R0VmDesc, source_slots) as u64,
    }
}

#[cfg(not(no_cuda))]
unsafe extern "C" {
    fn ab_gkr_windowed_r0_abi_probe(layout: *mut R0AbiLayout);
}

pub fn native_r0_abi_layout() -> Result<R0AbiLayout, R0AbiError> {
    #[cfg(not(no_cuda))]
    {
        let mut layout = R0AbiLayout::default();
        unsafe { ab_gkr_windowed_r0_abi_probe(&mut layout) };
        Ok(layout)
    }
    #[cfg(no_cuda)]
    {
        Err(R0AbiError::NativeProbeUnavailable)
    }
}

const _: () = {
    let profile = GpuResourceProfile::production().r0;
    assert!(size_of::<usize>() == 8);
    assert!(profile.max_records == R0_RECORD_CAPACITY);
    assert!(profile.max_program_words == R0_PROGRAM_WORDS);
    assert!(profile.max_sources == R0_SOURCE_SLOTS);
    assert!(profile.max_source_windows == R0_WINDOW_CAPACITY);
    assert!(profile.source_window_columns == R0_WINDOW_COLUMN_CAPACITY);
    assert!(profile.max_coefficient_recipes <= R0_COEFFICIENT_CAPACITY);
    assert!(profile.max_immediates == R0_IMMEDIATE_CAPACITY);
    assert!(profile.max_projections == R0_PROJECTION_CAPACITY);
    assert!(size_of::<R0WindowAddr>() == 16);
    assert!(align_of::<R0WindowAddr>() == 8);
    assert!(offset_of!(R0WindowAddr, base) == 0);
    assert!(offset_of!(R0WindowAddr, log2_stride) == 8);
    assert!(offset_of!(R0WindowAddr, origin) == 9);
    assert!(offset_of!(R0WindowAddr, procedural_kind) == 10);
    assert!(offset_of!(R0WindowAddr, reserved) == 11);
    assert!(size_of::<R0VmDesc>() == 17_536);
    assert!(align_of::<R0VmDesc>() == 16);
    assert!(size_of::<R0VmDesc>() <= KERNEL_ARGUMENT_CEILING_BYTES);
    assert!(offset_of!(R0VmDesc, window_bases) == 0);
    assert!(offset_of!(R0VmDesc, program) == 1_024);
    assert!(offset_of!(R0VmDesc, eq_low) == 15_352);
    assert!(offset_of!(R0VmDesc, partials) == 15_360);
    assert!(offset_of!(R0VmDesc, log_rows) == 15_368);
    assert!(offset_of!(R0VmDesc, record_count) == 15_372);
    assert!(offset_of!(R0VmDesc, source_count) == 15_376);
    assert!(offset_of!(R0VmDesc, window_count) == 15_380);
    assert!(offset_of!(R0VmDesc, banked_coefficient_count) == 15_384);
    assert!(offset_of!(R0VmDesc, c_init) == 15_388);
    assert!(offset_of!(R0VmDesc, eq_sizes) == 15_392);
    assert!(offset_of!(R0VmDesc, source_slots) == 15_404);
    assert!(R0_CONSTANT_FOOTPRINT_BYTES == 45_312);
    assert!(R0_CONSTANT_FOOTPRINT_BYTES <= CUDA_CONSTANT_MEMORY_CEILING_BYTES);
    assert!(R0_SOURCE_WINDOW_MASK == 0x3f);
    assert!(R0_SOURCE_COLUMN_MASK == 0x7f);
    assert!(R0_COEFFICIENT_BANK_BIAS != crate::abi::C_INIT_NONE);
};

#[cfg(test)]
mod tests {
    use core::mem::{offset_of, size_of};

    use crate::abi::C_INIT_NONE;
    use crate::geometry::make_eq_sizes;
    use crate::r0_artifact::{
        decode_r0_bundle, r0_coordinate_payload_sha256, FrozenR0Coordinate, R0_CORPUS_BYTES,
    };
    use crate::r0_geometry::R0MemoryPreflight;

    use super::*;

    #[test]
    fn cpu_r0_descriptor_capacity_and_offsets_fit_cuda() {
        assert_eq!(R0_PROGRAM_WORDS, 7_164);
        assert_eq!(R0_SOURCE_SLOTS, 1_062);
        assert_eq!(size_of::<R0WindowAddr>(), 16);
        assert_eq!(size_of::<R0VmDesc>(), 17_536);
        assert!(size_of::<R0VmDesc>() <= KERNEL_ARGUMENT_CEILING_BYTES);
        assert_eq!(offset_of!(R0VmDesc, program), 1_024);
        assert_eq!(offset_of!(R0VmDesc, program) % 16, 0);
        assert_eq!(offset_of!(R0VmDesc, source_slots) % 2, 0);
    }

    #[test]
    fn cpu_r0_descriptor_builder_zero_fills_tails_and_keeps_c_init_absent() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let coordinate = &bundle.coordinates[0];
        let windows = vec![R0WindowAddr::default(); coordinate.binding.windows.len()];
        let desc = R0VmDesc::from_coordinate(
            coordinate,
            &windows,
            3,
            core::ptr::null(),
            core::ptr::null_mut(),
            make_eq_sizes(3).unwrap(),
            coordinate.recipes.len(),
        )
        .unwrap();

        assert_eq!(
            &desc.program[..coordinate.program_words.len()],
            coordinate.program_words.as_slice(),
        );
        assert!(desc.program[coordinate.program_words.len()..]
            .iter()
            .all(|word| *word == 0));
        assert!(desc.source_slots[coordinate.binding.source_slots.len()..]
            .iter()
            .all(|source| *source == 0));
        assert!(desc.window_bases[coordinate.binding.windows.len()..]
            .iter()
            .all(R0WindowAddr::is_zero));
        assert_eq!(desc.c_init, C_INIT_NONE);
        assert_eq!(desc.log_rows, 0);
        assert_eq!(desc.record_count, coordinate.term_count);
        assert_eq!(
            desc.source_count as usize,
            coordinate.binding.source_slots.len()
        );
        assert_eq!(desc.window_count as usize, coordinate.binding.windows.len());
    }

    #[test]
    fn cpu_r0_descriptor_rejects_present_c_init_and_every_declared_overflow() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let coordinate = &bundle.coordinates[0];
        let build = |coordinate: &crate::r0_artifact::FrozenR0Coordinate| {
            let windows = vec![R0WindowAddr::default(); coordinate.binding.windows.len()];
            R0VmDesc::from_coordinate(
                coordinate,
                &windows,
                3,
                core::ptr::null(),
                core::ptr::null_mut(),
                make_eq_sizes(3).unwrap(),
                coordinate.recipes.len(),
            )
        };

        let mut bad = coordinate.clone();
        bad.c_init = Some(0);
        assert!(matches!(
            build(&bad),
            Err(R0AbiError::Artifact(R0ArtifactError::CInitPresent))
        ));

        let mut bad = coordinate.clone();
        bad.shape.projections = (R0_PROJECTION_CAPACITY + 1) as u32;
        assert!(matches!(
            build(&bad),
            Err(R0AbiError::Artifact(R0ArtifactError::CapacityOverflow))
        ));

        let mut bad = coordinate.clone();
        bad.program_words.resize(R0_PROGRAM_WORDS + 4, 0);
        assert!(matches!(
            build(&bad),
            Err(R0AbiError::Artifact(R0ArtifactError::CapacityOverflow))
        ));

        let mut bad = coordinate.clone();
        bad.binding
            .source_slots
            .resize(R0_SOURCE_SLOTS + 1, bad.binding.source_slots[0].clone());
        assert!(matches!(
            build(&bad),
            Err(R0AbiError::Artifact(R0ArtifactError::CapacityOverflow))
        ));
    }

    fn checked_boundary_acceptance(coordinate: &FrozenR0Coordinate) -> (bool, bool) {
        let windows = vec![R0WindowAddr::default(); coordinate.binding.windows.len()];
        let descriptor_accepted = R0VmDesc::from_coordinate(
            coordinate,
            &windows,
            3,
            core::ptr::null(),
            core::ptr::null_mut(),
            make_eq_sizes(3).unwrap(),
            coordinate.recipes.len(),
        )
        .is_ok();
        let preflight_accepted = R0MemoryPreflight::for_coordinate(coordinate, 3, 0, None).is_ok();
        (descriptor_accepted, preflight_accepted)
    }

    fn rehash(coordinate: &mut FrozenR0Coordinate) {
        coordinate.payload_sha256 = r0_coordinate_payload_sha256(coordinate).unwrap();
    }

    #[test]
    fn cpu_checked_boundaries_reject_every_rehashed_frozen_shape_mutation() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let coordinate = &bundle.coordinates[0];
        let mutations: [(&str, fn(&mut FrozenR0Coordinate)); 10] = [
            ("records", |row| row.shape.records += 1),
            ("projections", |row| row.shape.projections += 1),
            ("bf_atoms", |row| row.shape.bf_atoms += 1),
            ("e4_atoms", |row| row.shape.e4_atoms += 1),
            ("source_uses", |row| row.shape.source_uses += 1),
            ("unique_sources", |row| row.shape.unique_sources += 1),
            ("windows", |row| row.shape.windows += 1),
            ("max_relative_column", |row| {
                row.shape.max_relative_column = if row.shape.max_relative_column == 0 {
                    1
                } else {
                    row.shape.max_relative_column - 1
                };
            }),
            ("coefficient_recipes", |row| {
                row.shape.coefficient_recipes += 1;
            }),
            ("immediates", |row| row.shape.immediates += 1),
        ];
        let mut accepted = Vec::new();
        for (name, mutate) in mutations {
            let mut bad = coordinate.clone();
            mutate(&mut bad);
            rehash(&mut bad);
            let (descriptor, preflight) = checked_boundary_acceptance(&bad);
            if descriptor {
                accepted.push(format!("{name}:descriptor"));
            }
            if preflight {
                accepted.push(format!("{name}:preflight"));
            }
        }
        assert!(accepted.is_empty(), "accepted mutations: {accepted:?}");
    }

    #[test]
    fn cpu_checked_boundaries_reject_rehashed_noncanonical_bindings() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let coordinate = bundle
            .coordinates
            .iter()
            .find(|row| {
                row.binding.windows.len() >= 2
                    && row.binding.windows.iter().any(|window| {
                        window.columns.last().is_some_and(|column| {
                            column.column + 1 < window.first_column + R0_WINDOW_COLUMN_CAPACITY
                        })
                    })
            })
            .unwrap();
        let mut mutations = Vec::new();

        let mut window_order = coordinate.clone();
        window_order.binding.windows.swap(0, 1);
        for slot in &mut window_order.binding.source_slots {
            slot.window = match slot.window {
                0 => 1,
                1 => 0,
                other => other,
            };
        }
        rehash(&mut window_order);
        mutations.push(("window_order", window_order));

        let mut column_order = coordinate.clone();
        let window = column_order
            .binding
            .windows
            .iter_mut()
            .find(|window| !window.columns.is_empty())
            .unwrap();
        window.columns.push(window.columns.last().unwrap().clone());
        rehash(&mut column_order);
        mutations.push(("column_order", column_order));

        let mut aliased_source = coordinate.clone();
        let window = aliased_source
            .binding
            .windows
            .iter_mut()
            .find(|window| {
                window.columns.last().is_some_and(|column| {
                    column.column + 1 < window.first_column + R0_WINDOW_COLUMN_CAPACITY
                })
            })
            .unwrap();
        let alias = window.columns[0].source;
        let next_column = window.columns.last().unwrap().column + 1;
        window
            .columns
            .push(gpu_gkr_compiler::backward::LeanBoundColumn {
                column: next_column,
                source: alias,
            });
        rehash(&mut aliased_source);
        mutations.push(("aliased_source", aliased_source));

        let mut accepted = Vec::new();
        for (name, bad) in mutations {
            let (descriptor, preflight) = checked_boundary_acceptance(&bad);
            if descriptor {
                accepted.push(format!("{name}:descriptor"));
            }
            if preflight {
                accepted.push(format!("{name}:preflight"));
            }
        }
        assert!(accepted.is_empty(), "accepted mutations: {accepted:?}");
    }

    #[test]
    fn cpu_r0_descriptor_rejects_equality_sizes_for_another_log() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        let coordinate = &bundle.coordinates[0];
        let windows = vec![R0WindowAddr::default(); coordinate.binding.windows.len()];
        assert!(matches!(
            R0VmDesc::from_coordinate(
                coordinate,
                &windows,
                12,
                core::ptr::null(),
                core::ptr::null_mut(),
                make_eq_sizes(11).unwrap(),
                coordinate.recipes.len(),
            ),
            Err(R0AbiError::InvalidEqSizes { log_trace: 12, .. })
        ));
    }

    #[test]
    fn cpu_r0_coefficient_ids_keep_literals_bank_and_c_init_namespaces_distinct() {
        assert_eq!(
            classify_r0_coefficient(0, 1).unwrap(),
            R0CoefficientRef::One,
        );
        assert_eq!(
            classify_r0_coefficient(1, 1).unwrap(),
            R0CoefficientRef::NegOne,
        );
        assert_eq!(
            classify_r0_coefficient(2, 1).unwrap(),
            R0CoefficientRef::Banked(0),
        );
        assert!(classify_r0_coefficient(3, 1).is_err());
        assert!(classify_r0_coefficient(C_INIT_NONE, R0_COEFFICIENT_CAPACITY).is_err());
    }

    #[test]
    fn cpu_compiler_profile_and_measured_corpus_fit_every_r0_capacity() {
        let bundle = decode_r0_bundle(R0_CORPUS_BYTES).unwrap();
        assert!(!bundle.coordinates.is_empty());
        for coordinate in &bundle.coordinates {
            validate_r0_coordinate_capacities(coordinate).unwrap();
            assert!(coordinate.program_words.len() <= R0_PROGRAM_WORDS);
            assert!(coordinate.binding.source_slots.len() <= R0_SOURCE_SLOTS);
            assert!(coordinate.binding.windows.len() <= R0_WINDOW_CAPACITY);
            assert!(coordinate.recipes.len() <= R0_COEFFICIENT_CAPACITY);
            assert!(coordinate.immediates.len() <= R0_IMMEDIATE_CAPACITY);
            assert!(coordinate.shape.projections as usize <= R0_PROJECTION_CAPACITY);
        }
    }

    #[cfg(not(no_cuda))]
    #[test]
    fn cpu_rust_and_native_r0_abi_layouts_match_field_for_field() {
        assert_eq!(native_r0_abi_layout().unwrap(), rust_r0_abi_layout());
    }
}
