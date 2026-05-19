use super::add_sub::apply_unified_add_sub_inner;
use super::jbs::apply_unified_jbs_inner;
use super::mem::apply_unified_mem_inner;
use super::shifts::apply_unified_shifts_inner;
use super::*;
use crate::constraint::{Constraint, Term};
use crate::cs::circuit_trait::*;
use crate::gkr_circuits::add_sub_family::{
    add_sub_lui_auipc_mop_table_addition_fn, add_sub_lui_auipc_mop_table_driver_fn,
    AddSubLuiAuipcMopFamilyCircuitMask,
};
use crate::gkr_circuits::binary_shifts_family::{
    shift_binop_table_addition_fn, shift_binop_table_driver_fn, ShiftBinaryFamilyCircuitMask,
};
use crate::gkr_circuits::jump_branch_slt_family::{
    jump_branch_slt_table_addition_fn, jump_branch_slt_table_driver_fn,
    JumpSltBranchFamilyCircuitMask,
};
use crate::gkr_circuits::mem_word_only::{
    mem_word_only_table_addition_fn, mem_word_only_table_driver_fn,
};
use crate::oracle::Placeholder;
use crate::tables::TableDriver;
use crate::types::{Boolean, LIMB_WIDTH};
use crate::witness_placer::*;
use field::PrimeField;

/// Unified reduced-machine flag layout:
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
pub(super) const FAMILY_1_FLAG_OFFSET: usize = 0;
pub(super) const FAMILY_2_FLAG_OFFSET: usize =
    FAMILY_1_FLAG_OFFSET + ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS;
pub(super) const FAMILY_3_FLAG_OFFSET: usize =
    FAMILY_2_FLAG_OFFSET + JUMP_SLT_BRANCH_FAMILY_NUM_BITS;
pub(super) const FAMILY_4_FLAG_OFFSET: usize =
    FAMILY_3_FLAG_OFFSET + SHIFT_BINARY_FAMILY_NUM_FLAGS;

/// Family 4 occupies 2 unified flags (one-hot LW/SW), independent of the standalone
/// `WORD_ONLY_MEMORY_FAMILY_NUM_FLAGS = 1` encoding.
pub(super) const UNIFIED_FAMILY_4_NUM_FLAGS: usize = 2;
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
    apply_unified_add_sub_inner(
        cs,
        inputs.clone(),
        family_1_decoder,
        rs1_limbs,
        rs2_limbs,
        rd_write_limbs,
        rs2_read_timestamp,
    );
    apply_unified_jbs_inner(
        cs,
        inputs.clone(),
        family_2_decoder,
        rs1_limbs,
        rs2_limbs,
        rd_write_limbs,
    );
    apply_unified_shifts_inner(
        cs,
        inputs.clone(),
        family_3_decoder,
        rs1_limbs,
        rs2_limbs,
        rd_write_limbs,
    );
    let pc_in = inputs.cycle_start_state.pc;
    let pc_out = inputs.cycle_end_state.pc;
    let execute = inputs.execute;
    apply_unified_mem_inner(cs, inputs, is_lw, is_sw, rs1_limbs, rs2_access, rd_access);

    // Unified PC bump (gated). Families 1, 3, 4 leave PC handling to the caller;
    // Family 2 (jump_branch_slt) owns its own gated PC logic for jal/jalr/branch/slt.
    // We add `pc_next = pc + 4` constraints that fire only when (cycle executes) AND
    // (no Family-2 sub-opcode is active). Padding rows have execute=0 → trivially satisfied.
    apply_unified_pc_bump(cs, pc_in, pc_out, execute, family_2_bits);

    apply_unified_family_dispatch_one_hot(
        cs,
        execute,
        family_1_bits,
        family_2_bits,
        family_3_bits,
        is_lw,
        is_sw,
    );
}

/// Adds the `pc_next = pc + 4` constraint, gated on `execute AND no Family-2 sub-opcode bit set`.
/// Family 2's body owns the un-gated PC machinery for jal/jalr/branch/slt; this function fills
/// in the constraint for the rest of the families AND must trivially hold on padding rows
/// (execute=0) where pc_in=pc_out=0 would otherwise violate `pc + 4 = pc_out`.
///
/// Soundness precondition: `pc_in[0]` MUST be 16-bit-valued for the `pc_inc_carry` witness
/// `(pc_in[0] + 4) >> 16 ∈ {0, 1}` to be Boolean. This is enforced transitively across
/// cycles: this function range-checks `pc_out[0]` to 16 bits, and the memory permutation
/// argument identifies cycle N's `pc_out` with cycle N+1's `pc_in`. The chain anchors at
/// cycle 0 where `pc_in = INITIAL_PC = 0` (range-trivially-16-bit).
fn apply_unified_pc_bump<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    pc_in: [crate::definitions::Variable; REGISTER_SIZE],
    pc_out: [crate::definitions::Variable; REGISTER_SIZE],
    execute: crate::definitions::Variable,
    family_2_bits: [Boolean; JUMP_SLT_BRANCH_FAMILY_NUM_BITS],
) {
    // Unconditional 16-bit range checks on pc_out limbs. Family 2's standalone
    // PC path does not enforce this, so the unified body owns it (and Family 2's
    // standalone wrapper adds the same checks for parity).
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

    // Helper Boolean: gate = execute * (1 - sum(family_2 sub-opcode bits)).
    // Only the 4 sub-opcode bits (JAL/JALR/SLT/BRANCH at family_2_bits[0..4]) are
    // mutually exclusive — the 5th bit (RD_IS_ZERO_BIT) is set IN ADDITION to a
    // sub-opcode bit when rd is x0, so it must not enter the sum.
    // Wrapping in `execute` makes padding rows (execute=0) trivially satisfy the
    // PC-bump constraints; keeping the helper as a single Boolean keeps the
    // top-level constraint at degree 2.
    let pc_bump_gate = cs.add_named_boolean_variable("unified pc-bump gate");
    {
        let execute_var = execute;
        let f2_vars: [Variable; 4] = std::array::from_fn(|i| {
            family_2_bits[i]
                .get_variable()
                .expect("Boolean::Is expected")
        });
        let pc_bump_gate_var = pc_bump_gate.get_variable().unwrap();
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let execute_m = placer.get_boolean(execute_var);
            let any_f2 = f2_vars
                .iter()
                .map(|v| placer.get_boolean(*v))
                .reduce(|a, b| a.or(&b))
                .unwrap();
            let gate_m = execute_m.and(&any_f2.negate());
            placer.assign_mask(pc_bump_gate_var, &gate_m);
        };
        cs.set_values(value_fn);
    }
    // Setup constraint: pc_bump_gate = execute - sum(execute * family_2_subop_bits)
    //   ⇒ pc_bump_gate - execute + sum(execute * family_2_subop_bits) = 0  (deg 2)
    {
        let mut setup = Constraint::from(pc_bump_gate) - Term::from(execute);
        for &b in family_2_bits[..4].iter() {
            setup = setup + Constraint::from(execute) * Constraint::from(b);
        }
        cs.add_constraint(setup);
    }

    let pc_step: Term<F> = Term::from(common_constants::PC_STEP as u32);
    let shift16: Term<F> = Term::from(1 << 16);

    // pc_bump_gate * (pc_in[0] + 4 - pc_out[0] - 2^16 * pc_inc_carry) = 0  (deg 2)
    cs.add_constraint(
        Constraint::from(pc_bump_gate)
            * (Constraint::from(pc_in[0]) + pc_step
                - Term::from(pc_out[0])
                - shift16 * Term::from(pc_inc_carry)),
    );
    // pc_bump_gate * (pc_inc_carry + pc_in[1] - pc_out[1]) = 0  (deg 2)
    cs.add_constraint(
        Constraint::from(pc_bump_gate)
            * (Constraint::from(pc_inc_carry) + Term::from(pc_in[1]) - Term::from(pc_out[1])),
    );
}

/// pin that at most one family fires per executing cycle.
fn apply_unified_family_dispatch_one_hot<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    execute: crate::definitions::Variable,
    family_1_bits: [Boolean; ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS],
    family_2_bits: [Boolean; JUMP_SLT_BRANCH_FAMILY_NUM_BITS],
    family_3_bits: [Boolean; SHIFT_BINARY_FAMILY_NUM_FLAGS],
    is_lw: Boolean,
    is_sw: Boolean,
) {
    let is_any_family_active = cs.add_named_boolean_variable("unified family-dispatch one-hot");

    // Witness: is_any_family_active = execute AND (any of the family-dispatch bits)
    {
        let f1_vars: [Variable; ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS] =
            std::array::from_fn(|i| family_1_bits[i].get_variable().unwrap());
        let f2_vars: [Variable; 4] =
            std::array::from_fn(|i| family_2_bits[i].get_variable().unwrap());
        let f3_vars: [Variable; SHIFT_BINARY_FAMILY_NUM_FLAGS] =
            std::array::from_fn(|i| family_3_bits[i].get_variable().unwrap());
        let is_lw_var = is_lw.get_variable().unwrap();
        let is_sw_var = is_sw.get_variable().unwrap();
        let target = is_any_family_active.get_variable().unwrap();
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let execute_m = placer.get_boolean(execute);
            let any_bit = f1_vars
                .iter()
                .chain(f2_vars.iter())
                .chain(f3_vars.iter())
                .chain(std::iter::once(&is_lw_var))
                .chain(std::iter::once(&is_sw_var))
                .map(|v| placer.get_boolean(*v))
                .reduce(|a, b| a.or(&b))
                .unwrap();
            let result = execute_m.and(&any_bit);
            placer.assign_mask(target, &result);
        };
        cs.set_values(value_fn);
    }

    // Setup constraint (deg 2):
    //   is_any_family_active - execute * (sum of dispatch bits) = 0
    // sum = family_1_bits[..] + family_2_bits[..4] + family_3_bits[..] + is_lw + is_sw
    let mut setup = Constraint::from(is_any_family_active);
    for &b in family_1_bits.iter() {
        setup = setup - Constraint::from(execute) * Constraint::from(b);
    }
    for &b in family_2_bits[..4].iter() {
        setup = setup - Constraint::from(execute) * Constraint::from(b);
    }
    for &b in family_3_bits.iter() {
        setup = setup - Constraint::from(execute) * Constraint::from(b);
    }
    setup = setup - Constraint::from(execute) * Constraint::from(is_lw);
    setup = setup - Constraint::from(execute) * Constraint::from(is_sw);
    cs.add_constraint(setup);
}

/// Register all tables the unified circuit body looks up against. Shared by both
/// the artifact-build path and the SSA-dump path so they stay in lockstep with
/// what the prover-side driver does at prove time.
///
/// Family 4 (mem_word_only) needs the AlignedRomRead lookup table. It's added
/// at cs-side with dummy bytecode so `offset_for_decoder_table` accounts for
/// its size; the prover supplies the real binary-derived content at prove time
/// via the same `create_mem_word_only_special_tables` call.
fn unified_register_all_tables<F: ::field::PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    unified_reduced_machine_table_addition_fn(cs);
    for (table_type, table) in
        crate::gkr_circuits::mem_word_only::create_mem_word_only_special_tables::<
            F,
            { common_constants::ROM_SECOND_WORD_BITS },
        >(&[])
    {
        cs.add_table_with_content(table_type, table);
    }
}

/// Build the unified circuit artifact via the inline-i/t compile path.
/// Single source of truth used by both the cs-side serialization tests below
/// and by the verifier_generator integration test (via the
/// `gkr_circuits!` macro entry in `verifier_common`).
fn build_unified_artifact<F: ::field::PrimeField>(
    use_caches: bool,
) -> crate::gkr_compiler::GKRCircuitArtifact<F> {
    use crate::cs::circuit_impl::BasicAssembly;
    use crate::gkr_compiler::GKRCompiler;

    let mut cs = BasicAssembly::<F>::new();
    unified_register_all_tables(&mut cs);
    unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr(&mut cs);
    let (cs_output, _) = cs.finalize();

    let compiler = GKRCompiler::<F>::default();
    compiler.compile_family_circuit_with_inline_inits_and_teardowns(
        cs_output,
        common_constants::ROM_WORD_SIZE,
        /* num_inits_and_teardowns_pairs */ 1,
        /* trace_len_log2 */ 24,
        use_caches,
    )
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use crate::definitions::OutputType;
    use crate::utils::serialize_to_file;

    /// Sanity-check the artifact shape: both output channels present + i/t
    /// teardown_sets populated. Doesn't write anything to disk.
    #[test]
    fn compile_unified_reduced_machine_with_inline_inits_and_teardowns() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let artifact = build_unified_artifact::<BabyBearField>(true);

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

    /// Serialize the caches-variant artifact to the path the
    /// `gkr_circuits!` macro entry expects. Mirrors per-family pattern
    /// (`compile_X_into_gkr` in each family's `circuit.rs::test`).
    #[test]
    fn compile_unified_reduced_machine_into_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let artifact = build_unified_artifact::<BabyBearField>(true);
        serialize_to_file(
            &artifact,
            "compiled_circuits/unified_reduced_machine_layout_gkr.json",
        );
    }

    /// No-caches variant. Matches the per-family `_no_caches` companion tests.
    #[test]
    fn compile_unified_reduced_machine_into_no_caches_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let artifact = build_unified_artifact::<BabyBearField>(false);
        serialize_to_file(
            &artifact,
            "compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json",
        );
    }

    /// SSA witness graph dump for the unified circuit. Needed by
    /// `witness_eval_generator::gen_for_gkr` to produce
    /// `prover/compiled_circuits/unified_reduced_machine_generated_gkr.rs`, which
    /// the prover-side G1 test imports via a `mod unified_reduced_machine`.
    #[test]
    fn compile_unified_reduced_machine_gkr_witness_graph() {
        skip_if_ci!();
        use crate::gkr_compiler::dump_ssa_witness_eval_form;
        use ::field::baby_bear::base::BabyBearField;

        let ssa_forms = dump_ssa_witness_eval_form::<BabyBearField>(
            &|cs| unified_register_all_tables(cs),
            &|cs| unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr(cs),
        );
        serialize_to_file(
            &ssa_forms,
            "compiled_circuits/unified_reduced_machine_ssa_gkr.json",
        );
    }
}
