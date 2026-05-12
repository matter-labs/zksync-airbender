use super::*;
use crate::cs::circuit_trait::*;
use crate::gkr_circuits::add_sub_family::{
    add_sub_lui_auipc_mop_table_addition_fn, add_sub_lui_auipc_mop_table_driver_fn,
    apply_add_sub_lui_auipc_mop_inner, AddSubLuiAuipcMopFamilyCircuitMask,
};
use crate::gkr_circuits::binary_shifts_family::{
    apply_shift_binop_inner, shift_binop_table_addition_fn, shift_binop_table_driver_fn,
    ShiftBinaryFamilyCircuitMask,
};
use crate::gkr_circuits::jump_branch_slt_family::{
    apply_jump_branch_slt_inner, jump_branch_slt_table_addition_fn,
    jump_branch_slt_table_driver_fn, JumpSltBranchFamilyCircuitMask,
};
use crate::gkr_circuits::mem_word_only::{
    apply_mem_word_only_inner, mem_word_only_table_addition_fn, mem_word_only_table_driver_fn,
};
use crate::oracle::Placeholder;
use crate::tables::TableDriver;
use crate::constraint::{Constraint, Term};
use crate::types::{Boolean, LIMB_WIDTH};
use crate::witness_placer::*;
use field::PrimeField;

/// Unified reduced-machine flag layout (Stage 4: Families 1 + 2 + 3 + 4):
///
/// | Bit range  | Family                            | Count |
/// |------------|-----------------------------------|-------|
/// | [0..8)     | Family 1 (add_sub_lui_auipc_mop)  | 8     |
/// | [8..13)    | Family 2 (jump_branch_slt)        | 5     |
/// | [13..15)   | Family 3 (shift_binop)            | 2     |
/// | [15..17)   | Family 4 (mem_word_only)          | 2     |
///
/// Family 4 is encoded one-hot in the unified bitmask (bit 15 = LW, bit 16 = SW)
/// to match the per-sub-opcode convention used by Families 1/2/3. This diverges
/// from the Family-4 standalone encoding (1 bit = is_store) but lets the unified
/// body read the LW/SW gates directly as Booleans without committing additional
/// witness columns.
///
/// (`REDUCED_MACHINE_NUM_FLAGS = 18` in `definitions::unrolled_families` includes
/// 1 reserved bit — `mem_subword_only`'s third sub-opcode bit (`SUBWORD_ONLY_MEMORY_FAMILY_NUM_FLAGS = 3`)
///  — that the unified reduced-machine layout doesn't allocate because mem_subword isn't part of the reduced-machine family set.)
const FAMILY_1_FLAG_OFFSET: usize = 0;
const FAMILY_2_FLAG_OFFSET: usize = FAMILY_1_FLAG_OFFSET + ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS;
const FAMILY_3_FLAG_OFFSET: usize = FAMILY_2_FLAG_OFFSET + JUMP_SLT_BRANCH_FAMILY_NUM_BITS;
const FAMILY_4_FLAG_OFFSET: usize = FAMILY_3_FLAG_OFFSET + SHIFT_BINARY_FAMILY_NUM_FLAGS;

/// Family 4 occupies 2 unified flags (one-hot LW/SW), independent of the standalone
/// `WORD_ONLY_MEMORY_FAMILY_NUM_FLAGS = 1` encoding.
const UNIFIED_FAMILY_4_NUM_FLAGS: usize = 2;
const FAMILY_4_LW_BIT: usize = FAMILY_4_FLAG_OFFSET;
const FAMILY_4_SW_BIT: usize = FAMILY_4_FLAG_OFFSET + 1;

pub const UNIFIED_REDUCED_MACHINE_NUM_FLAGS: usize = ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS
    + JUMP_SLT_BRANCH_FAMILY_NUM_BITS
    + SHIFT_BINARY_FAMILY_NUM_FLAGS
    + UNIFIED_FAMILY_4_NUM_FLAGS;

pub fn unified_reduced_machine_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    add_sub_lui_auipc_mop_table_addition_fn(cs);
    jump_branch_slt_table_addition_fn(cs);
    shift_binop_table_addition_fn(cs);
    mem_word_only_table_addition_fn(cs);
}

pub fn unified_reduced_machine_table_driver_fn<F: PrimeField>(table_driver: &mut TableDriver<F>) {
    add_sub_lui_auipc_mop_table_driver_fn(table_driver);
    jump_branch_slt_table_driver_fn(table_driver);
    shift_binop_table_driver_fn(table_driver);
    mem_word_only_table_driver_fn(table_driver);
}

/// Top-level unified circuit body. Allocates a single shared set of memory accesses
/// for all reduced-machine families, then dispatches to each family's per-flag body.
/// Per-family bodies don't allocate their own accesses — they accept extracted
/// limbs/timestamps as parameters.
pub fn unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr<
    F: PrimeField,
    CS: Circuit<F>,
>(
    cs: &mut CS,
) {
    // need_funct3 = true because Family 2 (jump/branch/slt) uses funct3 to distinguish
    // branch sub-variants and Family 3 (shift_binop) uses it to select binop subtype.
    // Family 1 has funct3 = None natively but the extra column is bound to 0 by the
    // decoder lookup when Family 1 fires.
    let (input, bitmask) =
        cs.allocate_machine_state(true, false, UNIFIED_REDUCED_MACHINE_NUM_FLAGS);
    let bitmask: [_; UNIFIED_REDUCED_MACHINE_NUM_FLAGS] = bitmask.try_into().unwrap();
    let bitmask = bitmask.map(|el| Boolean::Is(el));

    apply_unified_reduced_machine_inner(cs, input, bitmask);
}

fn apply_unified_reduced_machine_inner<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    bitmask: [Boolean; UNIFIED_REDUCED_MACHINE_NUM_FLAGS],
) {
    // Slice the unified bitmask into per-family decoders. Each family's apply_inner
    // sees only its own flag bits and is unaware of the unified layout.
    let family_1_bits: [Boolean; ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS] =
        std::array::from_fn(|i| bitmask[FAMILY_1_FLAG_OFFSET + i]);
    let family_2_bits: [Boolean; JUMP_SLT_BRANCH_FAMILY_NUM_BITS] =
        std::array::from_fn(|i| bitmask[FAMILY_2_FLAG_OFFSET + i]);
    let family_3_bits: [Boolean; SHIFT_BINARY_FAMILY_NUM_FLAGS] =
        std::array::from_fn(|i| bitmask[FAMILY_3_FLAG_OFFSET + i]);

    let family_1_decoder = AddSubLuiAuipcMopFamilyCircuitMask::from_mask(family_1_bits);
    let family_2_decoder = JumpSltBranchFamilyCircuitMask::from_mask(family_2_bits);
    let family_3_decoder = ShiftBinaryFamilyCircuitMask::from_mask(family_3_bits);

    let is_lw = bitmask[FAMILY_4_LW_BIT];
    let is_sw = bitmask[FAMILY_4_SW_BIT];

    // Allocate the 3 memory accesses ONCE — shared across all families.
    //
    // rs1 is always a register read (every family needs rs1). rs2 and rd are
    // `RegisterOrRam` to accommodate Family 4 LW (rs2-slot ≡ RAM read) and Family 4
    // SW (rd-slot ≡ RAM write); Families 1-3 + the matching half of Family 4 keep
    // them as register accesses by pinning `is_register = NOT is_lw / NOT is_sw`.
    //
    // rs1 + rs2 are committed as U8 bytes so Family 3's
    // byte-keyed lookups + Family 4's RAM-address lookup can use them directly.
    // Families 1+2 + Family 4's address arithmetic algebraically reassemble U16
    // from bytes via free degree-1 polynomial expressions inside their bodies.
    // rd write remains U16.
    let rs1_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterRead {
            reg_idx: inputs.decoder_data.rs1_index,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(0),
            split_as_u8: true,
        },
        "rs1",
        0,
    );

    let memread_addr =
        core::array::from_fn(|i| cs.add_named_variable(&format!("unified memread_addr[{i}]")));
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let value = placer.get_oracle_u32(Placeholder::ShuffleRamAddress(1));
            placer.assign_u32_from_u16_parts(memread_addr, &value);
        };
        cs.set_values(value_fn);
    }
    let rs2_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterOrRamRead {
            // is_register = 1 when this slot is a register read (Families 1/2/3 +
            // Family 4 SW). Equivalently NOT is_lw.
            is_register: is_lw.toggle(),
            address: memread_addr,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(1),
            split_as_u8: true,
        },
        "rs2/mem read",
        1,
    );

    let memwrite_addr =
        core::array::from_fn(|i| cs.add_named_variable(&format!("unified memwrite_addr[{i}]")));
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let value = placer.get_oracle_u32(Placeholder::ShuffleRamAddress(2));
            placer.assign_u32_from_u16_parts(memwrite_addr, &value);
        };
        cs.set_values(value_fn);
    }
    let rd_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterOrRamReadWrite {
            // is_register = NOT is_sw — true for Families 1/2/3 + Family 4 LW.
            is_register: is_sw.toggle(),
            address: memwrite_addr,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(2),
            write_value_placeholder: Placeholder::ShuffleRamWriteValue(2),
            split_read_as_u8: false,
            split_write_as_u8: false,
        },
        "rd/mem write",
        2,
    );

    let MemoryAccess::RegisterOnly(rs1_access) = rs1_access else {
        unreachable!()
    };
    let MemoryAccess::RegisterOrRam(rs2_access) = rs2_access else {
        unreachable!()
    };
    let MemoryAccess::RegisterOrRam(rd_access) = rd_access else {
        unreachable!()
    };
    let WordRepresentation::U8Limbs(rs1_limbs) = rs1_access.read_value else {
        unreachable!()
    };
    let WordRepresentation::U8Limbs(rs2_limbs) = rs2_access.read_value.clone() else {
        unreachable!()
    };
    let WordRepresentation::U16Limbs(rd_write_limbs) = rd_access.write_value.clone() else {
        unreachable!()
    };
    let rs2_read_timestamp = rs2_access.read_timestamp;

    // Each family body adds constraints gated by its own flag bits. Family-internal
    // flags within each family are mutually exclusive (decoder lookup binds to family
    // sub-spaces), so adding all bodies' constraints is sound: at most one family's
    // is_* flags are 1 per cycle. Family 4's body owns the cleanaddr/ROM/lookup
    // logic and the register-side address-binding constraints (gated on
    // `NOT is_lw` / `NOT is_sw`, which fire for Families 1-3 too).
    apply_add_sub_lui_auipc_mop_inner(
        cs,
        inputs.clone(),
        family_1_decoder,
        rs1_limbs,
        rs2_limbs,
        rd_write_limbs,
        rs2_read_timestamp,
    );
    apply_jump_branch_slt_inner(
        cs,
        inputs.clone(),
        family_2_decoder,
        rs1_limbs,
        rs2_limbs,
        rd_write_limbs,
    );
    apply_shift_binop_inner(
        cs,
        inputs.clone(),
        family_3_decoder,
        rs1_limbs,
        rs2_limbs,
        rd_write_limbs,
    );
    let pc_in = inputs.cycle_start_state.pc;
    let pc_out = inputs.cycle_end_state.pc;
    apply_mem_word_only_inner(
        cs,
        inputs,
        is_lw,
        is_sw,
        rs1_limbs,
        rs2_access,
        rd_access,
    );

    // Unified PC bump (gated). Families 1, 3, 4 leave PC handling to the caller;
    // Family 2 (jump_branch_slt) owns its own gated PC logic for jal/jalr/branch/slt.
    // We add `pc_next = pc + 4` constraints that fire only when no Family-2 sub-opcode
    // is active, and let Family 2's existing "branch-not-taken" witness default
    // (pc_out_vars = pc + 4) handle the witness side for non-Family-2 cycles.
    apply_unified_pc_bump(cs, pc_in, pc_out, family_2_bits);
}

/// Adds the `pc_next = pc + 4` constraint, gated on `no Family-2 bit set`. Family 2's
/// body owns the un-gated PC machinery for jal/jalr/branch/slt; this function fills in
/// the constraint for the rest of the families (and padding cycles) without touching
/// the witness — Family 2's "branch-not-taken" default already writes pc_next = pc + 4
/// when none of its flag bits is set.
fn apply_unified_pc_bump<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    pc_in: [crate::definitions::Variable; REGISTER_SIZE],
    pc_out: [crate::definitions::Variable; REGISTER_SIZE],
    family_2_bits: [Boolean; JUMP_SLT_BRANCH_FAMILY_NUM_BITS],
) {
    // Range checks on pc_out are unconditional — Family 2's PC machinery does not
    // explicitly range-check its outputs in the standalone path, so we add them
    // here for the unified circuit (the standalone wrapper for Family 2 backports
    // them too for parity).
    cs.require_invariant(
        pc_out[0],
        Invariant::RangeChecked {
            width: LIMB_WIDTH as u32,
        },
    );
    cs.require_invariant(
        pc_out[1],
        Invariant::RangeChecked {
            width: LIMB_WIDTH as u32,
        },
    );

    // pc_inc_carry = (pc_in[0] + 4) >> 16 — boolean. Witnessed unconditionally so
    // booleanity is satisfied on every cycle; the gated constraint only ties it to
    // pc_in / pc_out when Family 2 is not firing.
    let pc_inc_carry = cs.add_named_boolean_variable("unified pc-bump carry");
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let pc_lo = placer.get_u16(pc_in[0]);
            let four = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                common_constants::PC_STEP as u16,
            );
            let (_, carry) = pc_lo.overflowing_add(&four);
            placer.assign_mask(pc_inc_carry.get_variable().unwrap(), &carry);
        };
        cs.set_values(value_fn);
    }

    // gate = 1 - sum(family_2_bits). One-hot decoder bits ⇒ sum is 0 or 1, so gate is
    // 0 or 1 and degree-1 in the bitmask vars.
    let mut gate: Constraint<F> = Constraint::from(1u32);
    for &b in family_2_bits.iter() {
        gate = gate - Constraint::from(b);
    }

    let pc_step: Term<F> = Term::from(common_constants::PC_STEP as u32);
    let shift16: Term<F> = Term::from(1 << 16);

    // gate * (pc_in[0] + 4 - pc_out[0] - 2^16 * pc_inc_carry) = 0  (deg 2)
    cs.add_constraint(
        gate.clone()
            * (Constraint::from(pc_in[0]) + pc_step - Term::from(pc_out[0])
                - shift16 * Term::from(pc_inc_carry)),
    );
    // gate * (pc_inc_carry + pc_in[1] - pc_out[1]) = 0  (deg 2)
    cs.add_constraint(
        gate * (Constraint::from(pc_inc_carry) + Term::from(pc_in[1]) - Term::from(pc_out[1])),
    );
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use crate::cs::circuit_impl::BasicAssembly;
    use crate::cs::circuit_trait::Circuit;
    use crate::definitions::OutputType;
    use crate::gkr_compiler::GKRCompiler;

    #[test]
    fn compile_unified_reduced_machine_with_inline_inits_and_teardowns() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let mut cs = BasicAssembly::<BabyBearField>::new();
        unified_reduced_machine_table_addition_fn(&mut cs);
        unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr(&mut cs);
        let (cs_output, _) = cs.finalize();

        let compiler = GKRCompiler::<BabyBearField>::default();
        let artifact = compiler.compile_family_circuit_with_inline_inits_and_teardowns(
            cs_output,
            common_constants::ROM_WORD_SIZE,
            1,
            24,
            true,
        );

        assert!(artifact
            .global_output_map
            .contains_key(&OutputType::PermutationProduct));
        assert!(artifact
            .global_output_map
            .contains_key(&OutputType::InitsAndTeardownsProduct));
        assert_eq!(
            artifact.global_output_map[&OutputType::PermutationProduct].len(),
            2
        );
        assert_eq!(
            artifact.global_output_map[&OutputType::InitsAndTeardownsProduct].len(),
            2
        );
        assert!(!artifact.memory_layout.teardown_sets.is_empty());
    }
}
