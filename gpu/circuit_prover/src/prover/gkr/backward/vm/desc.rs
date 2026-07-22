use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};

use gkr_eval_isa::bwd::compile::BwdCompiledLayer;
use gkr_eval_isa::bwd::source::{BwdSpecial, OriginLeaf};
use gkr_eval_isa::fwd::encode::decode;
use gkr_eval_isa::fwd::isa::{DstLine, Instr, LdcSub, OperandField, OperandLine, Program};
use gkr_eval_isa::fwd::source::virtual_setup_kind_code;

use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::{flat::FLAT_CONST_MAX, GkrEqSizes};
use crate::prover::gkr::forward::vm::desc::{
    ARG_DERIVED_E4_CAP as FWD_VM_ARG_DERIVED_E4_CAP, CONST_CAP as FWD_VM_BF_CONSTANT_CAP,
    CONST_DERIVED_E4_CAP as FWD_VM_CONST_DERIVED_E4_CAP,
};

pub(crate) const BWD_VM_PROGRAM_CAP: usize = 1_744;
pub(crate) const BWD_VM_SOURCE_WINDOW_CAP: usize = 4;
pub(crate) const BWD_VM_SPECIAL_CAP: usize = 147;
pub(crate) const BWD_VM_COEFFICIENT_CAP: usize = 145;
pub(crate) const BWD_VM_CELL_CAP: usize = 18;

// The add/sub census uses no plain BF or ArgDerivedE4 entries, but those two
// ISA channels remain part of the shared evaluator contract. Reuse the exact
// established forward-VM ABI banks instead of inventing a new capacity.
pub(crate) const BWD_VM_BF_CONSTANT_CAP: usize = FWD_VM_BF_CONSTANT_CAP;
pub(crate) const BWD_VM_ARG_DERIVED_E4_CAP: usize = FWD_VM_ARG_DERIVED_E4_CAP;
// ConstDerivedE4 values use the already-defined forward constant-memory bank.
pub(crate) const BWD_VM_CONST_DERIVED_E4_CAP: usize = FWD_VM_CONST_DERIVED_E4_CAP;

pub(crate) const BWD_VM_SPECIAL_KIND_COEFFICIENT: u32 = 0;
pub(crate) const BWD_VM_SPECIAL_KIND_ACC_INIT: u32 = 1;
pub(crate) const BWD_VM_SPECIAL_KIND_VIRTUAL_SETUP: u32 = 2;
pub(crate) const BWD_VM_SPECIAL_KIND_BITS: u32 = 2;
pub(crate) const BWD_VM_SPECIAL_KIND_MASK: u32 = (1 << BWD_VM_SPECIAL_KIND_BITS) - 1;
pub(crate) const BWD_VM_SPECIAL_PAYLOAD_SHIFT: u32 = BWD_VM_SPECIAL_KIND_BITS;
pub(crate) const BWD_VM_SPECIAL_PAYLOAD_MASK: u32 = u32::MAX >> BWD_VM_SPECIAL_KIND_BITS;

pub(crate) const BWD_VM_ORIGIN_FIELD_BASE: u8 = OperandField::Base as u8;
pub(crate) const BWD_VM_ORIGIN_FIELD_EXT: u8 = OperandField::Ext as u8;

pub(crate) const BWD_VM_VIRTUAL_RANGE_CHECK_16_BITS: u32 = 0;
pub(crate) const BWD_VM_VIRTUAL_RANGE_CHECK_TIMESTAMP: u32 = 1;
pub(crate) const BWD_VM_VIRTUAL_INITS_AND_TEARDOWNS_LOW: u32 = 2;
pub(crate) const BWD_VM_VIRTUAL_INITS_AND_TEARDOWNS_HIGH: u32 = 3;

const _: () = {
    use cs::gkr_compiler::dag_ir::VirtualSetupKind::*;
    use gkr_eval_isa::fwd::source::KIND_ORDER;
    assert!(matches!(
        KIND_ORDER[BWD_VM_VIRTUAL_RANGE_CHECK_16_BITS as usize],
        RangeCheck16Bits
    ));
    assert!(matches!(
        KIND_ORDER[BWD_VM_VIRTUAL_RANGE_CHECK_TIMESTAMP as usize],
        RangeCheckTimestamp
    ));
    assert!(matches!(
        KIND_ORDER[BWD_VM_VIRTUAL_INITS_AND_TEARDOWNS_LOW as usize],
        InitsAndTeardownsLow
    ));
    assert!(matches!(
        KIND_ORDER[BWD_VM_VIRTUAL_INITS_AND_TEARDOWNS_HIGH as usize],
        InitsAndTeardownsHigh
    ));
};

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(crate) struct BwdVmSourceWindow {
    pub read_base: *const u8,
    pub publish_base: *mut u8,
    pub read_stride_bytes: u32,
    pub publish_stride_bytes: u32,
    pub backing_depth: u8,
    pub target_depth: u8,
    pub origin_field: u8,
    pub materialize: u8,
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct BwdVmSpecial {
    packed: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SpecialLoweringError {
    MissingCoefficientSlot,
    UnexpectedCoefficientSlot,
    CoefficientSlotOutOfRange(u32),
    WrongVirtualSetupField {
        expected: OperandField,
        actual: OperandField,
    },
    ReadFoldSource,
}

impl BwdVmSpecial {
    pub(crate) fn from_special(
        special: &BwdSpecial,
        field: OperandField,
        coefficient_slot: Option<u32>,
    ) -> Result<Self, SpecialLoweringError> {
        let (kind, payload) = match special {
            BwdSpecial::Coefficient { .. } => (
                BWD_VM_SPECIAL_KIND_COEFFICIENT,
                checked_coefficient_slot(coefficient_slot)?,
            ),
            BwdSpecial::AccInit => (
                BWD_VM_SPECIAL_KIND_ACC_INIT,
                checked_coefficient_slot(coefficient_slot)?,
            ),
            BwdSpecial::VirtualSetup { kind } => {
                check_no_coefficient_slot(coefficient_slot)?;
                check_virtual_setup_field(OperandField::Base, field)?;
                (
                    BWD_VM_SPECIAL_KIND_VIRTUAL_SETUP,
                    virtual_setup_kind_code(kind),
                )
            }
            BwdSpecial::FoldSource {
                origin: OriginLeaf::VirtualSetup { kind },
            } => {
                check_no_coefficient_slot(coefficient_slot)?;
                check_virtual_setup_field(OperandField::Ext, field)?;
                (
                    BWD_VM_SPECIAL_KIND_VIRTUAL_SETUP,
                    virtual_setup_kind_code(kind),
                )
            }
            BwdSpecial::FoldSource {
                origin: OriginLeaf::Read(_),
            } => return Err(SpecialLoweringError::ReadFoldSource),
        };
        debug_assert!(kind <= BWD_VM_SPECIAL_KIND_MASK);
        debug_assert!(payload <= BWD_VM_SPECIAL_PAYLOAD_MASK);
        Ok(Self {
            packed: kind | (payload << BWD_VM_SPECIAL_PAYLOAD_SHIFT),
        })
    }

    pub(crate) const fn kind(self) -> u32 {
        self.packed & BWD_VM_SPECIAL_KIND_MASK
    }

    pub(crate) const fn payload(self) -> u32 {
        self.packed >> BWD_VM_SPECIAL_PAYLOAD_SHIFT
    }
}

fn checked_coefficient_slot(slot: Option<u32>) -> Result<u32, SpecialLoweringError> {
    let slot = slot.ok_or(SpecialLoweringError::MissingCoefficientSlot)?;
    if slot as usize >= BWD_VM_COEFFICIENT_CAP || slot as usize >= FLAT_CONST_MAX {
        return Err(SpecialLoweringError::CoefficientSlotOutOfRange(slot));
    }
    Ok(slot)
}

fn check_no_coefficient_slot(slot: Option<u32>) -> Result<(), SpecialLoweringError> {
    if slot.is_some() {
        return Err(SpecialLoweringError::UnexpectedCoefficientSlot);
    }
    Ok(())
}

fn check_virtual_setup_field(
    expected: OperandField,
    actual: OperandField,
) -> Result<(), SpecialLoweringError> {
    if actual != expected {
        return Err(SpecialLoweringError::WrongVirtualSetupField { expected, actual });
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct DescriptorCounts {
    pub(crate) program_lanes: usize,
    pub(crate) source_windows: usize,
    pub(crate) specials: usize,
    pub(crate) coefficient_slots: usize,
    pub(crate) bf_constants: usize,
    pub(crate) arg_derived_e4: usize,
    pub(crate) const_derived_e4: usize,
    pub(crate) encoded_max_cell: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DescriptorCountError {
    InvalidEncoding,
    Capacity {
        field: &'static str,
        actual: usize,
        cap: usize,
    },
    MissingSpecial(u16),
    ReadFoldSpecial(u16),
    WrongVirtualSetupField {
        desc: u16,
        expected: OperandField,
        actual: OperandField,
    },
}

pub(crate) fn descriptor_counts(
    compiled: &BwdCompiledLayer,
    encoded: &[u16],
) -> Result<DescriptorCounts, DescriptorCountError> {
    let program = decode(encoded).map_err(|_| DescriptorCountError::InvalidEncoding)?;
    let mut special_descs = BTreeMap::<u16, BTreeSet<OperandField>>::new();
    let mut coefficient_descs = BTreeSet::new();
    let mut arg_derived_e4 = 0;
    let mut const_derived_e4 = 0;
    let encoded_max_cell = Cell::new(0);

    visit_program(
        &program,
        |operand, field| match operand {
            OperandLine::Smem { cell } => {
                encoded_max_cell.set(encoded_max_cell.get().max(*cell as usize))
            }
            OperandLine::Ldc { sub, idx } => match sub {
                LdcSub::ConstDerivedE4 => {
                    const_derived_e4 = const_derived_e4.max(*idx as usize + 1)
                }
                LdcSub::ArgDerivedE4 => arg_derived_e4 = arg_derived_e4.max(*idx as usize + 1),
                LdcSub::Const | LdcSub::Special => {}
            },
            OperandLine::Special { desc } => {
                special_descs.entry(*desc).or_default().insert(field);
            }
            OperandLine::LogicalGlobal { .. }
            | OperandLine::LogicalFold { .. }
            | OperandLine::Source { .. } => {}
        },
        |dst| {
            if let DstLine::Smem { cell } = dst {
                encoded_max_cell.set(encoded_max_cell.get().max(*cell as usize));
            }
        },
    );

    for (&desc, fields) in &special_descs {
        match compiled.specials.get(desc) {
            Some(BwdSpecial::Coefficient { .. } | BwdSpecial::AccInit) => {
                coefficient_descs.insert(desc);
            }
            Some(BwdSpecial::FoldSource {
                origin: OriginLeaf::VirtualSetup { .. },
            }) => validate_special_fields(desc, fields, OperandField::Ext)?,
            Some(BwdSpecial::FoldSource {
                origin: OriginLeaf::Read(_),
            }) => return Err(DescriptorCountError::ReadFoldSpecial(desc)),
            Some(BwdSpecial::VirtualSetup { .. }) => {
                validate_special_fields(desc, fields, OperandField::Base)?
            }
            None => return Err(DescriptorCountError::MissingSpecial(desc)),
        }
    }

    let counts = DescriptorCounts {
        program_lanes: encoded.len(),
        source_windows: compiled.source_windows.len(),
        // Final source binding leaves Read-origin FoldSource entries in the
        // host table, but no encoded Special operand references them. The
        // device map contains only the still-referenced descriptor namespace.
        specials: special_descs.len(),
        coefficient_slots: coefficient_descs.len(),
        bf_constants: compiled.consts.values().len(),
        arg_derived_e4,
        const_derived_e4,
        encoded_max_cell: encoded_max_cell.get(),
    };
    check_descriptor_cap("program_lanes", counts.program_lanes, BWD_VM_PROGRAM_CAP)?;
    check_descriptor_cap(
        "source_windows",
        counts.source_windows,
        BWD_VM_SOURCE_WINDOW_CAP,
    )?;
    check_descriptor_cap("specials", counts.specials, BWD_VM_SPECIAL_CAP)?;
    check_descriptor_cap(
        "coefficient_slots",
        counts.coefficient_slots,
        BWD_VM_COEFFICIENT_CAP,
    )?;
    check_descriptor_cap("bf_constants", counts.bf_constants, BWD_VM_BF_CONSTANT_CAP)?;
    check_descriptor_cap(
        "arg_derived_e4",
        counts.arg_derived_e4,
        BWD_VM_ARG_DERIVED_E4_CAP,
    )?;
    check_descriptor_cap(
        "const_derived_e4",
        counts.const_derived_e4,
        BWD_VM_CONST_DERIVED_E4_CAP,
    )?;
    check_descriptor_cap(
        "cell_count",
        counts.encoded_max_cell.saturating_add(1),
        BWD_VM_CELL_CAP,
    )?;
    Ok(counts)
}

fn check_descriptor_cap(
    field: &'static str,
    actual: usize,
    cap: usize,
) -> Result<(), DescriptorCountError> {
    if actual > cap {
        return Err(DescriptorCountError::Capacity { field, actual, cap });
    }
    Ok(())
}

fn visit_program(
    program: &Program,
    mut operand: impl FnMut(&OperandLine, OperandField),
    mut dst: impl FnMut(&DstLine),
) {
    for instruction in &program.instrs {
        match instruction {
            Instr::Add {
                field, operands, ..
            }
            | Instr::Mul {
                field, operands, ..
            } => {
                for value in operands {
                    operand(value, *field);
                }
            }
            Instr::Fma {
                field_lhs,
                field_rhs,
                pairs,
                ..
            } => {
                for (lhs, rhs) in pairs {
                    operand(lhs, *field_lhs);
                    operand(rhs, *field_rhs);
                }
            }
            Instr::Mov {
                field,
                dst: instruction_dst,
                src,
                ..
            } => {
                if let Some(value) = src {
                    operand(value, *field);
                }
                if let Some(value) = instruction_dst {
                    dst(value);
                }
            }
        }
    }
}

fn validate_special_fields(
    desc: u16,
    fields: &BTreeSet<OperandField>,
    expected: OperandField,
) -> Result<(), DescriptorCountError> {
    if let Some(&actual) = fields.iter().find(|&&field| field != expected) {
        return Err(DescriptorCountError::WrongVirtualSetupField {
            desc,
            expected,
            actual,
        });
    }
    Ok(())
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct BwdVmDesc {
    pub arg_derived_e4: [E4; BWD_VM_ARG_DERIVED_E4_CAP],
    pub round_challenges: *const E4,
    pub eq_low: *const E4,
    pub contributions: *mut E4,
    pub source_windows: [BwdVmSourceWindow; BWD_VM_SOURCE_WINDOW_CAP],
    pub eq_sizes: GkrEqSizes,
    pub bf_constants: [BF; BWD_VM_BF_CONSTANT_CAP],
    pub specials: [BwdVmSpecial; BWD_VM_SPECIAL_CAP],
    pub n_instr: u32,
    pub program_lanes: u32,
    pub n_source_windows: u32,
    pub n_specials: u32,
    pub n_coefficients: u32,
    pub n_bf_constants: u32,
    pub n_arg_derived_e4: u32,
    pub n_const_derived_e4: u32,
    pub n_round_challenges: u32,
    pub logical_rows: u32,
    pub cell_count: u32,
    pub program: [u16; BWD_VM_PROGRAM_CAP],
}

const _: () = {
    assert!(BWD_VM_COEFFICIENT_CAP <= FLAT_CONST_MAX);
    assert!(core::mem::size_of::<BwdVmSourceWindow>() == 32);
    assert!(core::mem::align_of::<BwdVmSourceWindow>() == 8);
    assert!(core::mem::size_of::<BwdVmSpecial>() == 4);
    assert!(core::mem::align_of::<BwdVmSpecial>() == 4);
    assert!(core::mem::size_of::<BwdVmDesc>() == 4640);
    assert!(core::mem::align_of::<BwdVmDesc>() == 16);
    assert!(core::mem::size_of::<BwdVmDesc>() <= 32764);
};

#[cfg(all(test, feature = "bench"))]
mod tests {
    use cs::gkr_compiler::dag_ir::{BwdRegime, VirtualSetupKind};
    use gkr_eval_isa::bwd::source::{BwdSpecial, OriginLeaf};
    use gkr_eval_isa::fwd::isa::OperandField;

    use super::{
        descriptor_counts, BwdVmDesc, BwdVmSourceWindow, BwdVmSpecial, BWD_VM_ARG_DERIVED_E4_CAP,
        BWD_VM_BF_CONSTANT_CAP, BWD_VM_CELL_CAP, BWD_VM_COEFFICIENT_CAP,
        BWD_VM_CONST_DERIVED_E4_CAP, BWD_VM_PROGRAM_CAP, BWD_VM_SOURCE_WINDOW_CAP,
        BWD_VM_SPECIAL_CAP, BWD_VM_SPECIAL_KIND_ACC_INIT, BWD_VM_SPECIAL_KIND_COEFFICIENT,
        BWD_VM_SPECIAL_KIND_VIRTUAL_SETUP, BWD_VM_VIRTUAL_INITS_AND_TEARDOWNS_HIGH,
        BWD_VM_VIRTUAL_INITS_AND_TEARDOWNS_LOW, BWD_VM_VIRTUAL_RANGE_CHECK_16_BITS,
        BWD_VM_VIRTUAL_RANGE_CHECK_TIMESTAMP,
    };
    use crate::prover::gkr::backward::vm::compile::load_add_sub_l0_case;
    use crate::prover::gkr::forward::vm::desc::PROGRAM_CAP;

    #[test]
    fn add_sub_l0_descriptor_census_fits_the_exact_program_cap() {
        let mut max_program_lanes = 0;

        eprintln!("regime budget lanes windows specials coeffs bf arg_e4 const_e4 max_cell");
        for regime in [BwdRegime::R0, BwdRegime::Ext] {
            for budget_cells in 2..=16 {
                let case = load_add_sub_l0_case(regime, budget_cells);
                let counts = descriptor_counts(&case.compiled.compiled, &case.compiled.encoded)
                    .expect("add/sub descriptor census must lower");
                eprintln!(
                    "{:?} {:>2} {:>4} {:>3} {:>3} {:>3} {:>2} {:>2} {:>2} {:>3}",
                    regime,
                    budget_cells,
                    counts.program_lanes,
                    counts.source_windows,
                    counts.specials,
                    counts.coefficient_slots,
                    counts.bf_constants,
                    counts.arg_derived_e4,
                    counts.const_derived_e4,
                    counts.encoded_max_cell,
                );
                max_program_lanes = max_program_lanes.max(counts.program_lanes);
                assert!(counts.program_lanes <= PROGRAM_CAP);
            }
        }

        assert_eq!(max_program_lanes, 1_744);
        assert_eq!(BWD_VM_PROGRAM_CAP, 1_744);
        let _ = core::mem::size_of::<BwdVmDesc>();
    }

    #[test]
    fn add_sub_l0_descriptor_census_pins_every_cap() {
        let mut maxima = super::DescriptorCounts::default();
        for regime in [BwdRegime::R0, BwdRegime::Ext] {
            for budget_cells in 2..=16 {
                let case = load_add_sub_l0_case(regime, budget_cells);
                let counts = descriptor_counts(&case.compiled.compiled, &case.compiled.encoded)
                    .expect("add/sub descriptor census must lower");
                maxima.program_lanes = maxima.program_lanes.max(counts.program_lanes);
                maxima.source_windows = maxima.source_windows.max(counts.source_windows);
                maxima.specials = maxima.specials.max(counts.specials);
                maxima.coefficient_slots = maxima.coefficient_slots.max(counts.coefficient_slots);
                maxima.bf_constants = maxima.bf_constants.max(counts.bf_constants);
                maxima.arg_derived_e4 = maxima.arg_derived_e4.max(counts.arg_derived_e4);
                maxima.const_derived_e4 = maxima.const_derived_e4.max(counts.const_derived_e4);
                maxima.encoded_max_cell = maxima.encoded_max_cell.max(counts.encoded_max_cell);
            }
        }

        assert_eq!(maxima.program_lanes, BWD_VM_PROGRAM_CAP);
        assert_eq!(maxima.source_windows, BWD_VM_SOURCE_WINDOW_CAP);
        assert_eq!(maxima.specials, BWD_VM_SPECIAL_CAP);
        assert_eq!(maxima.coefficient_slots, BWD_VM_COEFFICIENT_CAP);
        assert_eq!(maxima.bf_constants, 0);
        assert_eq!(maxima.arg_derived_e4, 0);
        assert_eq!(maxima.const_derived_e4, 1);
        assert_eq!(maxima.encoded_max_cell + 1, BWD_VM_CELL_CAP);
        assert_eq!(BWD_VM_BF_CONSTANT_CAP, 40);
        assert_eq!(BWD_VM_ARG_DERIVED_E4_CAP, 12);
        assert_eq!(BWD_VM_CONST_DERIVED_E4_CAP, 8);
    }

    #[test]
    fn source_window_layout_matches_the_semantic_record() {
        use core::mem::{align_of, offset_of, size_of};

        assert_eq!(size_of::<BwdVmSourceWindow>(), 32);
        assert_eq!(align_of::<BwdVmSourceWindow>(), 8);
        assert_eq!(offset_of!(BwdVmSourceWindow, read_base), 0);
        assert_eq!(offset_of!(BwdVmSourceWindow, publish_base), 8);
        assert_eq!(offset_of!(BwdVmSourceWindow, read_stride_bytes), 16);
        assert_eq!(offset_of!(BwdVmSourceWindow, publish_stride_bytes), 20);
        assert_eq!(offset_of!(BwdVmSourceWindow, backing_depth), 24);
        assert_eq!(offset_of!(BwdVmSourceWindow, target_depth), 25);
        assert_eq!(offset_of!(BwdVmSourceWindow, origin_field), 26);
        assert_eq!(offset_of!(BwdVmSourceWindow, materialize), 27);
    }

    #[test]
    fn special_record_maps_only_the_three_required_kinds() {
        use core::mem::{align_of, offset_of, size_of};

        assert_eq!(size_of::<BwdVmSpecial>(), 4);
        assert_eq!(align_of::<BwdVmSpecial>(), 4);
        assert_eq!(offset_of!(BwdVmSpecial, packed), 0);

        let coefficient = BwdVmSpecial::from_special(
            &BwdSpecial::Coefficient { fragment: 17 },
            OperandField::Ext,
            Some(23),
        )
        .unwrap();
        assert_eq!(coefficient.kind(), BWD_VM_SPECIAL_KIND_COEFFICIENT);
        assert_eq!(coefficient.payload(), 23);

        let acc_init =
            BwdVmSpecial::from_special(&BwdSpecial::AccInit, OperandField::Ext, Some(19)).unwrap();
        assert_eq!(acc_init.kind(), BWD_VM_SPECIAL_KIND_ACC_INIT);
        assert_eq!(acc_init.payload(), 19);

        for (kind, payload) in [
            (
                VirtualSetupKind::RangeCheck16Bits,
                BWD_VM_VIRTUAL_RANGE_CHECK_16_BITS,
            ),
            (
                VirtualSetupKind::RangeCheckTimestamp,
                BWD_VM_VIRTUAL_RANGE_CHECK_TIMESTAMP,
            ),
            (
                VirtualSetupKind::InitsAndTeardownsLow,
                BWD_VM_VIRTUAL_INITS_AND_TEARDOWNS_LOW,
            ),
            (
                VirtualSetupKind::InitsAndTeardownsHigh,
                BWD_VM_VIRTUAL_INITS_AND_TEARDOWNS_HIGH,
            ),
        ] {
            for (special, field) in [
                (
                    BwdSpecial::VirtualSetup { kind: kind.clone() },
                    OperandField::Base,
                ),
                (
                    BwdSpecial::FoldSource {
                        origin: OriginLeaf::VirtualSetup { kind },
                    },
                    OperandField::Ext,
                ),
            ] {
                let packed = BwdVmSpecial::from_special(&special, field, None).unwrap();
                assert_eq!(packed.kind(), BWD_VM_SPECIAL_KIND_VIRTUAL_SETUP);
                assert_eq!(packed.payload(), payload);
            }
        }
    }

    #[test]
    fn special_record_rejects_wrong_virtual_setup_forms() {
        use cs::gkr_compiler::dag_ir::ReadPlace;

        assert!(BwdVmSpecial::from_special(
            &BwdSpecial::VirtualSetup {
                kind: VirtualSetupKind::RangeCheckTimestamp,
            },
            OperandField::Ext,
            None,
        )
        .is_err());
        assert!(BwdVmSpecial::from_special(
            &BwdSpecial::FoldSource {
                origin: OriginLeaf::VirtualSetup {
                    kind: VirtualSetupKind::RangeCheckTimestamp,
                },
            },
            OperandField::Base,
            None,
        )
        .is_err());
        assert!(BwdVmSpecial::from_special(
            &BwdSpecial::FoldSource {
                origin: OriginLeaf::Read(ReadPlace::BaseLayerMemory { column: 0 }),
            },
            OperandField::Base,
            None,
        )
        .is_err());
    }

    #[test]
    fn descriptor_layout_is_pinned_field_for_field() {
        use core::mem::{align_of, offset_of, size_of};

        assert_eq!(offset_of!(BwdVmDesc, arg_derived_e4), 0);
        assert_eq!(offset_of!(BwdVmDesc, round_challenges), 192);
        assert_eq!(offset_of!(BwdVmDesc, eq_low), 200);
        assert_eq!(offset_of!(BwdVmDesc, contributions), 208);
        assert_eq!(offset_of!(BwdVmDesc, source_windows), 216);
        assert_eq!(offset_of!(BwdVmDesc, eq_sizes), 344);
        assert_eq!(offset_of!(BwdVmDesc, bf_constants), 356);
        assert_eq!(offset_of!(BwdVmDesc, specials), 516);
        assert_eq!(offset_of!(BwdVmDesc, n_instr), 1104);
        assert_eq!(offset_of!(BwdVmDesc, program_lanes), 1108);
        assert_eq!(offset_of!(BwdVmDesc, n_source_windows), 1112);
        assert_eq!(offset_of!(BwdVmDesc, n_specials), 1116);
        assert_eq!(offset_of!(BwdVmDesc, n_coefficients), 1120);
        assert_eq!(offset_of!(BwdVmDesc, n_bf_constants), 1124);
        assert_eq!(offset_of!(BwdVmDesc, n_arg_derived_e4), 1128);
        assert_eq!(offset_of!(BwdVmDesc, n_const_derived_e4), 1132);
        assert_eq!(offset_of!(BwdVmDesc, n_round_challenges), 1136);
        assert_eq!(offset_of!(BwdVmDesc, logical_rows), 1140);
        assert_eq!(offset_of!(BwdVmDesc, cell_count), 1144);
        assert_eq!(offset_of!(BwdVmDesc, program), 1148);
        assert_eq!(size_of::<BwdVmDesc>(), 4640);
        assert_eq!(align_of::<BwdVmDesc>(), 16);
        assert!(size_of::<BwdVmDesc>() <= 32764);
    }
}
