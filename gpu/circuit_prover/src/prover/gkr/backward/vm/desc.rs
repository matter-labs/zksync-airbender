use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};

use gkr_eval_isa::bwd::batch::{unpack_batch_dst, BATCH_COEFFICIENT_ONE};
use gkr_eval_isa::bwd::compile::BwdCompiledLayer;
use gkr_eval_isa::bwd::fragment::{FragmentTable, MergedRecipe};
use gkr_eval_isa::bwd::source::{BwdSpecial, OriginLeaf, VIRTUAL_SETUP_MATERIALIZE_DEPTH};
use gkr_eval_isa::fwd::encode::decode;
use gkr_eval_isa::fwd::isa::{DstLine, Instr, LdcSub, MovDir, OperandField, OperandLine, Program};
use gkr_eval_isa::fwd::source::virtual_setup_kind_code;

use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::{flat::FLAT_CONST_MAX, GkrEqSizes};
use crate::prover::gkr::forward::vm::desc::{
    ARG_DERIVED_E4_CAP as FWD_VM_ARG_DERIVED_E4_CAP, CONST_CAP as FWD_VM_BF_CONSTANT_CAP,
    CONST_DERIVED_E4_CAP as FWD_VM_CONST_DERIVED_E4_CAP,
};

pub(crate) const BWD_VM_PROGRAM_CAP: usize = 1_744;
pub(crate) const BWD_VM_SOURCE_READ_BASE: u8 = 0;
pub(crate) const BWD_VM_SOURCE_READ_EXT: u8 = 1;
pub(crate) const BWD_VM_SOURCE_VIRTUAL: u8 = 2;
pub(crate) const BWD_VM_SOURCE_WINDOW_CAP: usize = 5;
// Mirrored by BWD_VM_VIRTUAL_MATERIALIZE_DEPTH in bwd_vm.cuh.
pub(crate) const BWD_VM_VIRTUAL_MATERIALIZE_DEPTH: u8 = 3;
pub(crate) const BWD_VM_SPECIAL_CAP: usize = 147;
pub(crate) const BWD_VM_COEFFICIENT_CAP: usize = 145;
pub(crate) const BWD_VM_CELL_CAP: usize = 18;
pub(crate) const BWD_VM_BATCH_ACC_INIT_NONE: u16 = 0xffff;

// The add/sub census uses no plain BF or ArgDerivedE4 entries, but those two
// ISA channels remain part of the shared evaluator contract. Reuse the exact
// established forward-VM ABI banks instead of inventing a new capacity.
pub(crate) const BWD_VM_BF_CONSTANT_CAP: usize = FWD_VM_BF_CONSTANT_CAP;
pub(crate) const BWD_VM_ARG_DERIVED_E4_CAP: usize = FWD_VM_ARG_DERIVED_E4_CAP;
// ConstDerivedE4 values use the already-defined forward constant-memory bank.
pub(crate) const BWD_VM_CONST_DERIVED_E4_CAP: usize = FWD_VM_CONST_DERIVED_E4_CAP;

pub(crate) const BWD_VM_SPECIAL_KIND_VIRTUAL_SETUP: u32 = 2;
pub(crate) const BWD_VM_SPECIAL_KIND_BITS: u32 = 2;
pub(crate) const BWD_VM_SPECIAL_KIND_MASK: u32 = (1 << BWD_VM_SPECIAL_KIND_BITS) - 1;
pub(crate) const BWD_VM_SPECIAL_PAYLOAD_SHIFT: u32 = BWD_VM_SPECIAL_KIND_BITS;
pub(crate) const BWD_VM_SPECIAL_PAYLOAD_MASK: u32 = u32::MAX >> BWD_VM_SPECIAL_KIND_BITS;

pub(crate) const BWD_VM_VIRTUAL_RANGE_CHECK_16_BITS: u32 = 0;
pub(crate) const BWD_VM_VIRTUAL_RANGE_CHECK_TIMESTAMP: u32 = 1;
pub(crate) const BWD_VM_VIRTUAL_INITS_AND_TEARDOWNS_LOW: u32 = 2;
pub(crate) const BWD_VM_VIRTUAL_INITS_AND_TEARDOWNS_HIGH: u32 = 3;

const _: () = {
    use crate::upstream::VirtualSetupKind::*;
    use gkr_eval_isa::fwd::source::KIND_ORDER;
    assert!(KIND_ORDER.len() == 4);
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

const _: () = {
    assert!(OperandField::Base as u8 == 0);
    assert!(OperandField::Ext as u8 == 1);
    assert!(BWD_VM_VIRTUAL_MATERIALIZE_DEPTH == VIRTUAL_SETUP_MATERIALIZE_DEPTH);
    assert!(BATCH_COEFFICIENT_ONE == 0x3fff);
    assert!(BWD_VM_BATCH_ACC_INIT_NONE == u16::MAX);
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
    pub source_kind: u8,
    pub materialize: u8,
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct BwdVmSpecial {
    packed: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SpecialLoweringError {
    NonVirtualSpecial,
    WrongVirtualSetupField {
        expected: OperandField,
        actual: OperandField,
    },
    FoldSource,
}

impl BwdVmSpecial {
    pub(crate) fn from_special(
        special: &BwdSpecial,
        field: OperandField,
    ) -> Result<Self, SpecialLoweringError> {
        let (kind, payload) = match special {
            BwdSpecial::VirtualSetup { kind } => {
                check_virtual_setup_field(OperandField::Base, field)?;
                (
                    BWD_VM_SPECIAL_KIND_VIRTUAL_SETUP,
                    virtual_setup_kind_code(kind),
                )
            }
            BwdSpecial::FoldSource { .. } => return Err(SpecialLoweringError::FoldSource),
            BwdSpecial::Coefficient { .. } | BwdSpecial::AccInit => {
                return Err(SpecialLoweringError::NonVirtualSpecial)
            }
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
    pub(crate) max_logical_coefficient_desc: Option<u16>,
    pub(crate) coefficient_slots: usize,
    pub(crate) batch_acc_init: bool,
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
    UnexpectedOperandSpecial(u16),
    BatchSpecialNotCoefficient(u16),
    AccInitSpecialNotAccInit(u16),
    InvalidCoefficientFragment {
        desc: u16,
        fragment: u32,
    },
    WrongVirtualSetupField {
        desc: u16,
        expected: OperandField,
        actual: OperandField,
    },
}

pub(crate) fn descriptor_counts(
    compiled: &BwdCompiledLayer,
    fragments: &FragmentTable,
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

    for instruction in &program.instrs {
        let Instr::Mov {
            dir: MovDir::DstFromAcc,
            dst: Some(dst),
            ..
        } = instruction
        else {
            continue;
        };
        let Some(desc) = unpack_batch_dst(dst) else {
            continue;
        };
        if desc == BATCH_COEFFICIENT_ONE {
            continue;
        }
        match compiled.specials.get(desc) {
            Some(BwdSpecial::Coefficient { fragment })
                if fragments.fragments.get(*fragment as usize).is_some() =>
            {
                coefficient_descs.insert(desc);
            }
            Some(BwdSpecial::Coefficient { fragment }) => {
                return Err(DescriptorCountError::InvalidCoefficientFragment {
                    desc,
                    fragment: *fragment,
                })
            }
            Some(_) => return Err(DescriptorCountError::BatchSpecialNotCoefficient(desc)),
            None => return Err(DescriptorCountError::MissingSpecial(desc)),
        }
    }
    if let Some(desc) = compiled.acc_init_desc {
        match compiled.specials.get(desc) {
            Some(BwdSpecial::AccInit) => {}
            Some(_) => return Err(DescriptorCountError::AccInitSpecialNotAccInit(desc)),
            None => return Err(DescriptorCountError::MissingSpecial(desc)),
        }
    }

    let mut unique_recipes = Vec::<&MergedRecipe>::new();
    for &desc in &coefficient_descs {
        let BwdSpecial::Coefficient { fragment } = compiled
            .specials
            .get(desc)
            .expect("coefficient descriptors were validated above")
        else {
            unreachable!("batch coefficient set contains only fragment coefficients");
        };
        let recipe = &fragments.fragments[*fragment as usize].recipe;
        if !unique_recipes.contains(&recipe) {
            unique_recipes.push(recipe);
        }
    }
    if compiled.acc_init_desc.is_some() && !unique_recipes.contains(&&fragments.c_init) {
        unique_recipes.push(&fragments.c_init);
    }

    for (&desc, fields) in &special_descs {
        match compiled.specials.get(desc) {
            Some(BwdSpecial::FoldSource {
                origin: OriginLeaf::VirtualSetup { .. },
            }) => validate_special_fields(desc, fields, OperandField::Ext)?,
            Some(BwdSpecial::FoldSource {
                origin: OriginLeaf::Read(_),
            }) => return Err(DescriptorCountError::ReadFoldSpecial(desc)),
            Some(BwdSpecial::VirtualSetup { .. }) => {
                validate_special_fields(desc, fields, OperandField::Base)?
            }
            Some(BwdSpecial::Coefficient { .. } | BwdSpecial::AccInit) => {
                return Err(DescriptorCountError::UnexpectedOperandSpecial(desc))
            }
            None => return Err(DescriptorCountError::MissingSpecial(desc)),
        }
    }

    let virtual_source_descs = special_descs
        .keys()
        .filter(|&&desc| {
            matches!(
                compiled.specials.get(desc),
                Some(BwdSpecial::FoldSource {
                    origin: OriginLeaf::VirtualSetup { .. },
                })
            )
        })
        .count();
    let counts = DescriptorCounts {
        program_lanes: encoded.len(),
        source_windows: compiled.source_windows.len() + usize::from(virtual_source_descs != 0),
        // Final source binding leaves FoldSource entries in the host table,
        // but virtual-origin folds become one source window and Read-origin
        // folds have already become ordinary source lanes. The device special
        // map contains only the still-referenced descriptor namespace.
        specials: special_descs.len() - virtual_source_descs,
        max_logical_coefficient_desc: coefficient_descs.iter().next_back().copied(),
        coefficient_slots: unique_recipes.len(),
        batch_acc_init: compiled.acc_init_desc.is_some(),
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
    pub batch_acc_init: u16,
}

const _: () = {
    assert!(BWD_VM_COEFFICIENT_CAP <= FLAT_CONST_MAX);
    assert!(core::mem::size_of::<BwdVmSourceWindow>() == 32);
    assert!(core::mem::align_of::<BwdVmSourceWindow>() == 8);
    assert!(core::mem::size_of::<BwdVmSpecial>() == 4);
    assert!(core::mem::align_of::<BwdVmSpecial>() == 4);
    assert!(core::mem::size_of::<BwdVmDesc>() == 4672);
    assert!(core::mem::align_of::<BwdVmDesc>() == 16);
    assert!(core::mem::size_of::<BwdVmDesc>() <= 32764);
};

#[cfg(test)]
mod abi_tests {
    use core::mem::{align_of, offset_of, size_of};

    use super::BwdVmDesc;

    #[test]
    fn batch_acc_init_uses_existing_descriptor_tail_padding() {
        assert_eq!(offset_of!(BwdVmDesc, batch_acc_init), 4668);
        assert_eq!(size_of::<BwdVmDesc>(), 4672);
        assert_eq!(align_of::<BwdVmDesc>(), 16);
    }
}

#[cfg(all(test, feature = "bench"))]
mod tests {
    use cs::gkr_compiler::dag_ir::BwdRegime;
    use gkr_eval_isa::bwd::source::{BwdSpecial, OriginLeaf};
    use gkr_eval_isa::fwd::isa::OperandField;
    use gkr_eval_isa::fwd::source::KIND_ORDER;

    use super::{
        descriptor_counts, BwdVmDesc, BwdVmSourceWindow, BwdVmSpecial, BWD_VM_ARG_DERIVED_E4_CAP,
        BWD_VM_BF_CONSTANT_CAP, BWD_VM_CELL_CAP, BWD_VM_COEFFICIENT_CAP,
        BWD_VM_CONST_DERIVED_E4_CAP, BWD_VM_PROGRAM_CAP, BWD_VM_SOURCE_READ_BASE,
        BWD_VM_SOURCE_READ_EXT, BWD_VM_SOURCE_VIRTUAL, BWD_VM_SOURCE_WINDOW_CAP,
        BWD_VM_SPECIAL_CAP, BWD_VM_SPECIAL_KIND_VIRTUAL_SETUP,
        BWD_VM_VIRTUAL_INITS_AND_TEARDOWNS_HIGH, BWD_VM_VIRTUAL_INITS_AND_TEARDOWNS_LOW,
        BWD_VM_VIRTUAL_MATERIALIZE_DEPTH, BWD_VM_VIRTUAL_RANGE_CHECK_16_BITS,
        BWD_VM_VIRTUAL_RANGE_CHECK_TIMESTAMP,
    };
    use crate::prover::gkr::backward::vm::compile::load_add_sub_l0_case;
    use crate::prover::gkr::forward::vm::desc::PROGRAM_CAP;
    use crate::upstream::VirtualSetupKind;

    #[test]
    fn add_sub_l0_descriptor_census_fits_the_exact_program_cap() {
        let mut max_program_lanes = 0;

        eprintln!(
            "regime budget lanes windows virtual_specials logical_coeff_max compact_coeffs init bf arg_e4 const_e4 max_cell"
        );
        for regime in [BwdRegime::R0, BwdRegime::Ext] {
            for budget_cells in 2..=16 {
                let case = load_add_sub_l0_case(regime, budget_cells);
                let counts = descriptor_counts(
                    &case.compiled.compiled,
                    &case.distilled.fragments,
                    &case.compiled.encoded,
                )
                .expect("add/sub descriptor census must lower");
                eprintln!(
                    "{:?} {:>2} {:>4} {:>3} {:>3} {:>3?} {:>3} {:>4} {:>2} {:>2} {:>2} {:>3}",
                    regime,
                    budget_cells,
                    counts.program_lanes,
                    counts.source_windows,
                    counts.specials,
                    counts.max_logical_coefficient_desc,
                    counts.coefficient_slots,
                    if counts.batch_acc_init { "yes" } else { "no" },
                    counts.bf_constants,
                    counts.arg_derived_e4,
                    counts.const_derived_e4,
                    counts.encoded_max_cell,
                );
                max_program_lanes = max_program_lanes.max(counts.program_lanes);
                assert!(counts.program_lanes <= PROGRAM_CAP);
            }
        }

        assert_eq!(max_program_lanes, 992);
        assert_eq!(BWD_VM_PROGRAM_CAP, 1_744);
        assert!(max_program_lanes <= BWD_VM_PROGRAM_CAP);
        let _ = core::mem::size_of::<BwdVmDesc>();
    }

    #[test]
    fn add_sub_l0_descriptor_census_pins_every_cap() {
        let mut maxima = super::DescriptorCounts::default();
        for regime in [BwdRegime::R0, BwdRegime::Ext] {
            for budget_cells in 2..=16 {
                let case = load_add_sub_l0_case(regime, budget_cells);
                let counts = descriptor_counts(
                    &case.compiled.compiled,
                    &case.distilled.fragments,
                    &case.compiled.encoded,
                )
                .expect("add/sub descriptor census must lower");
                maxima.program_lanes = maxima.program_lanes.max(counts.program_lanes);
                maxima.source_windows = maxima.source_windows.max(counts.source_windows);
                maxima.specials = maxima.specials.max(counts.specials);
                maxima.max_logical_coefficient_desc = maxima
                    .max_logical_coefficient_desc
                    .max(counts.max_logical_coefficient_desc);
                maxima.coefficient_slots = maxima.coefficient_slots.max(counts.coefficient_slots);
                maxima.batch_acc_init |= counts.batch_acc_init;
                maxima.bf_constants = maxima.bf_constants.max(counts.bf_constants);
                maxima.arg_derived_e4 = maxima.arg_derived_e4.max(counts.arg_derived_e4);
                maxima.const_derived_e4 = maxima.const_derived_e4.max(counts.const_derived_e4);
                maxima.encoded_max_cell = maxima.encoded_max_cell.max(counts.encoded_max_cell);
            }
        }

        assert_eq!(maxima.program_lanes, 992);
        assert!(maxima.program_lanes <= BWD_VM_PROGRAM_CAP);
        assert_eq!(maxima.source_windows, 4);
        assert!(maxima.source_windows <= BWD_VM_SOURCE_WINDOW_CAP);
        assert_eq!(maxima.specials, 2);
        assert!(maxima.specials <= BWD_VM_SPECIAL_CAP);
        assert_eq!(maxima.max_logical_coefficient_desc, Some(203));
        assert_eq!(maxima.coefficient_slots, 91);
        assert!(maxima.coefficient_slots <= BWD_VM_COEFFICIENT_CAP);
        assert_eq!(maxima.bf_constants, 0);
        assert_eq!(maxima.arg_derived_e4, 0);
        assert_eq!(maxima.const_derived_e4, 1);
        assert_eq!(maxima.encoded_max_cell + 1, 13);
        assert!(maxima.encoded_max_cell < BWD_VM_CELL_CAP);
        assert_eq!(BWD_VM_BF_CONSTANT_CAP, 40);
        assert_eq!(BWD_VM_ARG_DERIVED_E4_CAP, 12);
        assert_eq!(BWD_VM_CONST_DERIVED_E4_CAP, 8);
        assert_eq!(core::mem::size_of::<BwdVmDesc>(), 4_672);
        assert_eq!(crate::prover::gkr::backward::flat::FLAT_CONST_MAX, 1_024);
        assert!(maxima.coefficient_slots <= crate::prover::gkr::backward::flat::FLAT_CONST_MAX);

        let counts_at = |regime, budget_cells| {
            let case = load_add_sub_l0_case(regime, budget_cells);
            descriptor_counts(
                &case.compiled.compiled,
                &case.distilled.fragments,
                &case.compiled.encoded,
            )
            .expect("maximum-realizing add/sub coordinate must lower")
        };
        let ext_c2 = counts_at(BwdRegime::Ext, 2);
        assert_eq!(
            (ext_c2.program_lanes, ext_c2.max_logical_coefficient_desc),
            (992, Some(203)),
            "add_sub L0 Ext c2 realizes the program and logical-coefficient maxima"
        );
        let r0_c2 = counts_at(BwdRegime::R0, 2);
        assert_eq!(
            (
                r0_c2.source_windows,
                r0_c2.specials,
                r0_c2.coefficient_slots,
                r0_c2.const_derived_e4,
            ),
            (4, 2, 91, 1),
            "add_sub L0 R0 c2 realizes the window, virtual-special, compact-coefficient, and \
             constant-E4 maxima"
        );
        assert_eq!(
            counts_at(BwdRegime::R0, 4).encoded_max_cell + 1,
            13,
            "add_sub L0 R0 c4 realizes the cell-count maximum"
        );
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
        assert_eq!(offset_of!(BwdVmSourceWindow, source_kind), 26);
        assert_eq!(offset_of!(BwdVmSourceWindow, materialize), 27);
    }

    #[test]
    fn special_record_maps_only_virtual_setup_recipes() {
        use core::mem::{align_of, offset_of, size_of};

        assert_eq!(KIND_ORDER.len(), 4);
        assert_eq!(BWD_VM_SOURCE_READ_BASE, 0);
        assert_eq!(BWD_VM_SOURCE_READ_EXT, 1);
        assert_eq!(BWD_VM_SOURCE_VIRTUAL, 2);
        assert_eq!(BWD_VM_VIRTUAL_MATERIALIZE_DEPTH, 3);
        assert_eq!(
            BWD_VM_VIRTUAL_MATERIALIZE_DEPTH,
            gkr_eval_isa::bwd::source::VIRTUAL_SETUP_MATERIALIZE_DEPTH
        );
        assert_eq!(size_of::<BwdVmSpecial>(), 4);
        assert_eq!(align_of::<BwdVmSpecial>(), 4);
        assert_eq!(offset_of!(BwdVmSpecial, packed), 0);

        assert!(BwdVmSpecial::from_special(
            &BwdSpecial::Coefficient { fragment: 17 },
            OperandField::Ext,
        )
        .is_err());

        assert!(BwdVmSpecial::from_special(&BwdSpecial::AccInit, OperandField::Ext).is_err());

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
            let packed =
                BwdVmSpecial::from_special(&BwdSpecial::VirtualSetup { kind }, OperandField::Base)
                    .unwrap();
            assert_eq!(packed.kind(), BWD_VM_SPECIAL_KIND_VIRTUAL_SETUP);
            assert_eq!(packed.payload(), payload);
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
        )
        .is_err());
        assert!(BwdVmSpecial::from_special(
            &BwdSpecial::FoldSource {
                origin: OriginLeaf::VirtualSetup {
                    kind: VirtualSetupKind::RangeCheckTimestamp,
                },
            },
            OperandField::Base,
        )
        .is_err());
        assert!(BwdVmSpecial::from_special(
            &BwdSpecial::FoldSource {
                origin: OriginLeaf::Read(ReadPlace::BaseLayerMemory { column: 0 }),
            },
            OperandField::Base,
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
        assert_eq!(offset_of!(BwdVmDesc, eq_sizes), 376);
        assert_eq!(offset_of!(BwdVmDesc, bf_constants), 388);
        assert_eq!(offset_of!(BwdVmDesc, specials), 548);
        assert_eq!(offset_of!(BwdVmDesc, n_instr), 1136);
        assert_eq!(offset_of!(BwdVmDesc, program_lanes), 1140);
        assert_eq!(offset_of!(BwdVmDesc, n_source_windows), 1144);
        assert_eq!(offset_of!(BwdVmDesc, n_specials), 1148);
        assert_eq!(offset_of!(BwdVmDesc, n_coefficients), 1152);
        assert_eq!(offset_of!(BwdVmDesc, n_bf_constants), 1156);
        assert_eq!(offset_of!(BwdVmDesc, n_arg_derived_e4), 1160);
        assert_eq!(offset_of!(BwdVmDesc, n_const_derived_e4), 1164);
        assert_eq!(offset_of!(BwdVmDesc, n_round_challenges), 1168);
        assert_eq!(offset_of!(BwdVmDesc, logical_rows), 1172);
        assert_eq!(offset_of!(BwdVmDesc, cell_count), 1176);
        assert_eq!(offset_of!(BwdVmDesc, program), 1180);
        assert_eq!(offset_of!(BwdVmDesc, batch_acc_init), 4668);
        assert_eq!(size_of::<BwdVmDesc>(), 4672);
        assert_eq!(align_of::<BwdVmDesc>(), 16);
        assert!(size_of::<BwdVmDesc>() <= 32764);
    }
}
