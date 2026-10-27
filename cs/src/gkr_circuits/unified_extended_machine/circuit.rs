use super::mem_subword::{apply_extended_memory_inner, MemoryFlags, MEM_SCRATCH_BOOLS};
use super::mul::apply_extended_mul_inner;
use super::*;
use crate::cs::circuit_trait::*;
use crate::gkr_circuits::add_sub_family::{
    add_sub_lui_auipc_mop_table_addition_fn, add_sub_lui_auipc_mop_table_driver_fn,
};
use crate::gkr_circuits::unified_reduced_machine::add_sub_lui_auipc_mop::apply_unified_add_sub_lui_auipc_mop_inner;
use crate::gkr_circuits::unified_reduced_machine::binary_shifts::apply_unified_binary_shifts_inner;
use crate::gkr_circuits::unified_reduced_machine::circuit::{
    const_max, flush_unified_lookup_pool, F1_SCRATCH_BOOLS, F1_SCRATCH_VARS, F2_PC_TMP_SLOT,
    F2_SCRATCH_BOOLS, F2_SCRATCH_VARS, F3_RS1_BYTE_SPLIT_SLOTS, F3_RS2_BYTE_SPLIT_SLOTS,
    F3_SCRATCH_VARS, SHARED_REGISTER_SLOTS, UNIFIED_F3_BASE_TABLES, UNIFIED_LOOKUP_WIDTH,
    UNIFIED_SCRATCH_BOOL_COUNT, UNIFIED_SCRATCH_VAR_COUNT, UNIFIED_WIDE_BINOP_TABLES,
    UNIFIED_XOR_ROTATE_TABLES,
};
use crate::gkr_circuits::unified_reduced_machine::jump_branch_slt::{
    apply_unified_jump_branch_slt_inner, jump_branch_slt_unified_table_addition_fn,
    jump_branch_slt_unified_table_driver_fn,
};
use crate::gkr_circuits::unified_reduced_machine::{
    FAMILY_1_FLAG_OFFSET as REDUCED_F1_OFFSET, FAMILY_2_FLAG_OFFSET as REDUCED_F2_OFFSET,
    FAMILY_3_FLAG_OFFSET as REDUCED_F3_OFFSET, FAMILY_4_FLAG_OFFSET as REDUCED_F4_OFFSET,
    UNIFIED_F3_NUM_FLAGS,
};
use crate::oracle::Placeholder;
use crate::structured_expr::Expr;
use crate::tables::TableDriver;
use crate::types::{Boolean, Num, Register, LIMB_WIDTH};
use crate::witness_placer::*;
use field::PrimeField;

/// Unified extended-machine flag layout. Families 1–3 are the reduced machine's regions
/// verbatim (same offsets, same per-family bodies); the reduced machine's word-only memory
/// region is replaced by the 4-flag sub-word memory family and the MUL family is appended.
///
/// | Bit range  | Family                                  | Count |
/// |------------|-----------------------------------------|-------|
/// | [0..10)    | Family 1 (add_sub_lui_auipc_mop + tri-add) | 10  |
/// | [10..15)   | Family 2 (jump_branch_slt, incl. RD_IS_ZERO) | 5 |
/// | [15..17)   | Family 3 (shift / binop incl. xor-rotate) | 2   |
/// | [17..21)   | Memory: LOAD, STORE (dispatch), LOAD_SUBWORD, STORE_SUBWORD (aux) | 4 |
/// | [21..23)   | MUL, MULHU                              | 2     |
///
/// Dispatch bits (exactly one per executing row): all Family 1 and 3 bits, Family 2's four
/// sub-opcode bits, LOAD, STORE, MUL, MULHU. Auxiliary bits: RD_IS_ZERO (with a Family 2
/// sub-opcode), LOAD_SUBWORD (with LOAD), STORE_SUBWORD (with STORE).
pub const FAMILY_1_FLAG_OFFSET: usize = REDUCED_F1_OFFSET;
pub const FAMILY_2_FLAG_OFFSET: usize = REDUCED_F2_OFFSET;
pub const FAMILY_3_FLAG_OFFSET: usize = REDUCED_F3_OFFSET;
pub const MEM_FLAG_OFFSET: usize = REDUCED_F4_OFFSET;
pub const MEM_LOAD_BIT: usize = MEM_FLAG_OFFSET;
pub const MEM_STORE_BIT: usize = MEM_FLAG_OFFSET + 1;
pub const MEM_LOAD_SUBWORD_BIT: usize = MEM_FLAG_OFFSET + 2;
pub const MEM_STORE_SUBWORD_BIT: usize = MEM_FLAG_OFFSET + 3;
pub const EXTENDED_MEMORY_NUM_FLAGS: usize = 4;
pub const MUL_FLAG_OFFSET: usize = MEM_FLAG_OFFSET + EXTENDED_MEMORY_NUM_FLAGS;
pub const MUL_BIT: usize = MUL_FLAG_OFFSET;
pub const MULHU_BIT: usize = MUL_FLAG_OFFSET + 1;
pub const EXTENDED_MUL_NUM_FLAGS: usize = 2;
pub const UNIFIED_EXTENDED_MACHINE_NUM_FLAGS: usize = MUL_FLAG_OFFSET + EXTENDED_MUL_NUM_FLAGS;
const _: () = assert!(MEM_FLAG_OFFSET == FAMILY_3_FLAG_OFFSET + UNIFIED_F3_NUM_FLAGS);

/// Shared scratch pools: the reduced machine's pool (sized by Families 1–3 and its word-only
/// memory family) already covers the two new families, so the pool widths do not change.
///
/// Memory family: Booleans [0..4) = of_lo, of_hi, b0, b1 (aliased with F1's carries /
/// tri-add bits, F2's add carries); `top_14` in the shared register's limb 0 (slot 17, RC-16);
/// lookup parts in [`MEM_PART_SLOTS`] (Family 3 shift-output bytes there).
///
/// MUL family: no Booleans; rs1 bytes in the shared register slots 17/18 (bytes satisfy the
/// RC-16), rs2 bytes read from Family 3's unconditional split slots 19/20, the other product
/// half in [`MUL_OTHER_HALF_SLOTS`] (RC-16 pool-wide: Family 3 keeps bytes there) and the
/// carries in [`MUL_CARRY_SLOTS`] (pinned only by the gated lookups, so any occupant is fine).
const _: () = assert!(MEM_SCRATCH_BOOLS <= UNIFIED_SCRATCH_BOOL_COUNT);
pub(super) const MEM_PART_SLOTS: [usize; 2] = [13, 14];
pub(super) const MUL_OTHER_HALF_SLOTS: [usize; 2] = [11, 12];
pub(super) const MUL_CARRY_SLOTS: [usize; 3] = [8, 9, 10];
const _: () = {
    // The new families' slots must stay out of every other family's prefix (F1: 2 vars, F2: 5
    // vars + the PC temporary at 7) and inside the pool; Family 3 owns the rest with bytes.
    let other_prefix = const_max(
        const_max(F1_SCRATCH_VARS, F2_SCRATCH_VARS),
        F2_PC_TMP_SLOT + 1,
    );
    assert!(MUL_CARRY_SLOTS[0] >= other_prefix);
    assert!(MUL_CARRY_SLOTS[2] < MUL_OTHER_HALF_SLOTS[0]);
    assert!(MUL_OTHER_HALF_SLOTS[1] < MEM_PART_SLOTS[0]);
    assert!(MEM_PART_SLOTS[1] < F3_RS1_BYTE_SPLIT_SLOTS[0]);
    assert!(F3_RS2_BYTE_SPLIT_SLOTS[1] < UNIFIED_SCRATCH_VAR_COUNT);
    assert!(F3_SCRATCH_VARS == UNIFIED_SCRATCH_VAR_COUNT);
};

const EXTENDED_MEMORY_TABLES: [TableType; 3] = [
    TableType::LoadSubwordLimb,
    TableType::StoreSubwordKeep,
    TableType::StoreSubwordSource,
];

const EXTENDED_MUL_TABLES: [TableType; 2] = [TableType::RangeCheck8x8, TableType::RangeCheck10x10];

pub fn unified_extended_machine_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    add_sub_lui_auipc_mop_table_addition_fn(cs);
    jump_branch_slt_unified_table_addition_fn(cs);
    for t in UNIFIED_F3_BASE_TABLES
        .into_iter()
        .chain(UNIFIED_WIDE_BINOP_TABLES)
        .chain(UNIFIED_XOR_ROTATE_TABLES)
        .chain(EXTENDED_MEMORY_TABLES)
        .chain(EXTENDED_MUL_TABLES)
    {
        cs.materialize_table::<UNIFIED_LOOKUP_WIDTH>(t);
    }
}

pub fn unified_extended_machine_table_driver_fn<F: PrimeField>(table_driver: &mut TableDriver<F>) {
    add_sub_lui_auipc_mop_table_driver_fn(table_driver);
    jump_branch_slt_unified_table_driver_fn(table_driver);
    for t in UNIFIED_F3_BASE_TABLES
        .into_iter()
        .chain(UNIFIED_WIDE_BINOP_TABLES)
        .chain(UNIFIED_XOR_ROTATE_TABLES)
        .chain(EXTENDED_MEMORY_TABLES)
        .chain(EXTENDED_MUL_TABLES)
    {
        table_driver.materialize_table::<UNIFIED_LOOKUP_WIDTH>(t);
    }
}

/// BabyBear-mop wrapper, like the reduced machine's entry point.
pub fn unified_extended_machine_circuit_with_preprocessed_bytecode_for_gkr<
    F: PrimeField,
    CS: Circuit<F>,
>(
    cs: &mut CS,
) {
    unified_extended_machine_circuit_with_preprocessed_bytecode_for_gkr_core::<
        F,
        ::field::baby_bear::base::BabyBearField,
        CS,
    >(cs);
}

pub fn unified_extended_machine_circuit_with_preprocessed_bytecode_for_gkr_core<
    F: PrimeField,
    MopF: PrimeField,
    CS: Circuit<F>,
>(
    cs: &mut CS,
) {
    // funct3 is used by Family 2 (branch variants), Family 3 (table ids) and the memory
    // family (sub-word mode bits).
    let (input, bitmask) =
        cs.allocate_machine_state(true, false, UNIFIED_EXTENDED_MACHINE_NUM_FLAGS);
    let bitmask: [_; UNIFIED_EXTENDED_MACHINE_NUM_FLAGS] = bitmask.try_into().unwrap();
    let bitmask = bitmask.map(Boolean::Is);

    apply_unified_extended_machine_inner::<F, MopF, _>(cs, input, bitmask);
}

fn apply_unified_extended_machine_inner<F: PrimeField, MopF: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    bitmask: [Boolean; UNIFIED_EXTENDED_MACHINE_NUM_FLAGS],
) {
    let mask = UnifiedExtendedMachineFamilyCircuitMask::from_full_mask(bitmask);
    let is_load = mask.is_load();
    let is_store = mask.is_store();

    // The 3 shared accesses: rs1 is always a register read; the rs2 slot is a RAM read on
    // loads, the rd slot a RAM read-write on stores.
    let rs1_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterRead {
            reg_idx: inputs.decoder_data.rs1_index,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(0),
            split_as_u8: false,
        },
        "rs1",
        0,
    );

    let memread_addr =
        core::array::from_fn(|i| cs.add_named_variable(&format!("extended memread_addr[{i}]")));
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let value = placer.get_oracle_u32(Placeholder::ShuffleRamAddress(1));
            placer.assign_u32_from_u16_parts(memread_addr, &value);
        };
        cs.set_values(value_fn);
    }
    let rs2_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterOrRamRead {
            is_register: is_load.toggle(),
            address: memread_addr,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(1),
            split_as_u8: false,
        },
        "rs2/mem read",
        1,
    );

    let memwrite_addr =
        core::array::from_fn(|i| cs.add_named_variable(&format!("extended memwrite_addr[{i}]")));
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let value = placer.get_oracle_u32(Placeholder::ShuffleRamAddress(2));
            placer.assign_u32_from_u16_parts(memwrite_addr, &value);
        };
        cs.set_values(value_fn);
    }
    let rd_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterOrRamReadWrite {
            is_register: is_store.toggle(),
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
    let WordRepresentation::U16Limbs(rs1_limbs) = rs1_access.read_value else {
        unreachable!()
    };
    let WordRepresentation::U16Limbs(rs2_limbs) = rs2_access.read_value else {
        unreachable!()
    };
    let WordRepresentation::U16Limbs(rd_write_limbs) = rd_access.write_value else {
        unreachable!()
    };
    let WordRepresentation::U16Limbs(rd_read_limbs) = rd_access.read_value else {
        unreachable!()
    };
    let rs2_read_timestamp = rs2_access.read_timestamp;

    // The shared scratch pools, exactly as in the reduced machine.
    let scratch_bools: [Boolean; UNIFIED_SCRATCH_BOOL_COUNT] = core::array::from_fn(|i| {
        cs.add_named_boolean_variable(&format!("shared scratch bool[{i}]"))
    });
    let scratch_vars: [Variable; UNIFIED_SCRATCH_VAR_COUNT] =
        core::array::from_fn(|i| cs.add_named_variable(&format!("shared scratch var[{i}]")));
    for slot in SHARED_REGISTER_SLOTS {
        cs.require_invariant(
            scratch_vars[slot],
            Invariant::RangeChecked {
                width: LIMB_WIDTH as u32,
            },
        );
    }
    let shared_intermediate_reg =
        Register(SHARED_REGISTER_SLOTS.map(|slot| Num::Var(scratch_vars[slot])));

    apply_unified_add_sub_lui_auipc_mop_inner::<F, MopF, _>(
        cs,
        inputs.clone(),
        mask.add_sub_lui_auipc_mop(),
        mask.perform_tri_add(),
        rs1_limbs,
        rs2_limbs,
        rd_write_limbs,
        rd_read_limbs,
        rs2_read_timestamp,
        shared_intermediate_reg,
        core::array::from_fn::<_, F1_SCRATCH_BOOLS, _>(|i| scratch_bools[i]),
        core::array::from_fn::<_, F1_SCRATCH_VARS, _>(|i| scratch_vars[i]),
    );
    let f2_lookups = apply_unified_jump_branch_slt_inner(
        cs,
        inputs.clone(),
        mask.jump_branch_slt(),
        rs1_limbs,
        rs2_limbs,
        rd_write_limbs,
        shared_intermediate_reg,
        core::array::from_fn::<_, F2_SCRATCH_BOOLS, _>(|i| scratch_bools[i]),
        core::array::from_fn::<_, F2_SCRATCH_VARS, _>(|i| scratch_vars[i]),
        scratch_vars[F2_PC_TMP_SLOT],
    );
    let f3_lookups = apply_unified_binary_shifts_inner(
        cs,
        inputs.clone(),
        mask.binary_shifts(),
        rs1_limbs,
        rs2_limbs,
        rd_write_limbs,
        core::array::from_fn::<_, F3_SCRATCH_VARS, _>(|i| scratch_vars[i]),
    );
    let mem_lookups = apply_extended_memory_inner(
        cs,
        &inputs,
        MemoryFlags {
            is_load,
            is_store,
            is_load_subword: mask.is_load_subword(),
            is_store_subword: mask.is_store_subword(),
        },
        rs1_limbs,
        &rs2_access,
        &rd_access,
        core::array::from_fn::<_, MEM_SCRATCH_BOOLS, _>(|i| scratch_bools[i]),
        MEM_PART_SLOTS.map(|slot| scratch_vars[slot]),
        scratch_vars[SHARED_REGISTER_SLOTS[0]],
    );
    let mul_lookups = apply_extended_mul_inner(
        cs,
        mask.is_mul(),
        mask.is_mulhu(),
        rs1_limbs,
        rs2_limbs,
        rd_write_limbs,
        F3_RS1_BYTE_SPLIT_SLOTS.map(|slot| scratch_vars[slot]),
        F3_RS2_BYTE_SPLIT_SLOTS.map(|slot| scratch_vars[slot]),
        MUL_OTHER_HALF_SLOTS.map(|slot| scratch_vars[slot]),
        MUL_CARRY_SLOTS.map(|slot| scratch_vars[slot]),
    );

    flush_unified_lookup_pool(cs, &[f2_lookups, f3_lookups, mem_lookups, mul_lookups]);

    let pc_in = inputs.cycle_start_state.pc;
    let pc_out = inputs.cycle_end_state.pc;
    let execute = inputs.execute;
    apply_extended_pc_bump(cs, pc_in, pc_out, execute, &mask);
    apply_extended_family_dispatch_one_hot(cs, execute, &mask);
}

/// Σ of the dispatch bits (every flag except RD_IS_ZERO, LOAD_SUBWORD, STORE_SUBWORD).
pub(super) fn dispatch_sum<F: PrimeField>(
    mask: &UnifiedExtendedMachineFamilyCircuitMask,
) -> Expr<F> {
    Expr::sum(
        mask.add_sub_lui_auipc_mop_bits()
            .into_iter()
            .chain(mask.jump_branch_slt_bits()[..4].iter().copied())
            .chain(mask.binary_shifts_bits())
            .chain([mask.is_load(), mask.is_store()])
            .chain(mask.mul_bits())
            .map(Expr::from)
            .collect(),
    )
}

/// PC-bump gate: `execute − Σ` Family 2 sub-opcode bits; 1 on executing non-Family-2 rows.
pub(super) fn pc_bump_gate<F: PrimeField>(
    execute: Variable,
    mask: &UnifiedExtendedMachineFamilyCircuitMask,
) -> Expr<F> {
    let family_2_bits = mask.jump_branch_slt_bits();
    Expr::var(execute) - Expr::sum(family_2_bits[..4].iter().map(|&b| Expr::from(b)).collect())
}

/// `pc_next = pc + 4` for every family but Family 2 (which owns its PC logic); identical to the
/// reduced machine's bump, see its soundness note on `pc_in[0]` being 16-bit by induction.
fn apply_extended_pc_bump<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    pc_in: [Variable; REGISTER_SIZE],
    pc_out: [Variable; REGISTER_SIZE],
    execute: Variable,
    mask: &UnifiedExtendedMachineFamilyCircuitMask,
) {
    for limb in pc_out {
        cs.require_invariant(
            limb,
            Invariant::RangeChecked {
                width: LIMB_WIDTH as u32,
            },
        );
    }

    let pc_inc_carry = cs.add_named_boolean_variable("extended pc-bump carry");
    {
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let pc_lo = placer.get_u16(pc_in[0]);
            let four = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                common_constants::PC_STEP as u16,
            );
            let (_, carry) = pc_lo.overflowing_add(&four);
            placer.assign_mask(pc_inc_carry.expect_variable(), &carry);
        };
        cs.set_values(value_fn);
    }

    let gate = pc_bump_gate(execute, mask);
    let pc_step: Expr<F> =
        Expr::constant(F::from_u32_with_reduction(common_constants::PC_STEP as u32));
    let shift16: Expr<F> = Expr::constant(F::from_u32_with_reduction(1 << 16));

    cs.add_constraint_expr(
        gate.clone()
            * (Expr::var(pc_in[0]) + pc_step
                - Expr::var(pc_out[0])
                - shift16 * Expr::from(pc_inc_carry)),
    );
    cs.add_constraint_expr(
        gate * (Expr::from(pc_inc_carry) + Expr::var(pc_in[1]) - Expr::var(pc_out[1])),
    );
}

/// Exactly one family fires per executing row (linear tie `execute = Σ dispatch bits`) and no
/// flag at all on padding rows.
fn apply_extended_family_dispatch_one_hot<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    execute: Variable,
    mask: &UnifiedExtendedMachineFamilyCircuitMask,
) {
    cs.add_constraint_expr_allow_explicit_linear_prevent_optimizations_expr(
        Expr::var(execute) - dispatch_sum(mask),
    );

    let all_flags = Expr::sum(
        mask.add_sub_lui_auipc_mop_bits()
            .into_iter()
            .chain(mask.jump_branch_slt_bits())
            .chain(mask.binary_shifts_bits())
            .chain(mask.memory_bits())
            .chain(mask.mul_bits())
            .map(Expr::from)
            .collect(),
    );
    cs.add_constraint_expr((Expr::<F>::one() - Expr::var(execute)) * all_flags);
}

/// Every table the circuit looks up against. No bytecode-dependent (ROM) tables exist for this
/// machine, so the same registration serves compile time and prove time.
pub fn unified_extended_register_all_tables<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    unified_extended_machine_table_addition_fn(cs);
}

/// Build the artifact through the inline-i/t compile path (BabyBear mop).
pub fn build_unified_extended_artifact<F: PrimeField>(
    use_caches: bool,
    trace_len_log2: usize,
    num_init_and_teardown_pairs: usize,
) -> crate::gkr_compiler::GKRCircuitArtifact<F> {
    build_unified_extended_artifact_core::<F, ::field::baby_bear::base::BabyBearField>(
        use_caches,
        trace_len_log2,
        num_init_and_teardown_pairs,
    )
}

pub fn build_unified_extended_artifact_core<F: PrimeField, MopF: PrimeField>(
    use_caches: bool,
    trace_len_log2: usize,
    num_init_and_teardown_pairs: usize,
) -> crate::gkr_compiler::GKRCircuitArtifact<F> {
    use crate::cs::circuit_impl::BasicAssembly;
    use crate::gkr_compiler::GKRCompiler;

    let mut cs = BasicAssembly::<F>::new();
    unified_extended_register_all_tables(&mut cs);
    unified_extended_machine_circuit_with_preprocessed_bytecode_for_gkr_core::<F, MopF, _>(&mut cs);
    let (cs_output, _) = cs.finalize();

    let compiler = GKRCompiler::<F>::default();
    compiler.compile_family_circuit_with_inline_inits_and_teardowns(
        cs_output,
        common_constants::ROM_WORD_SIZE,
        num_init_and_teardown_pairs,
        trace_len_log2,
        use_caches,
    )
}

#[cfg(test)]
mod test {
    use super::super::decoder::extended_decoder_mask_violation;
    use super::*;
    use crate::constraint::Term;
    use crate::definitions::OutputType;
    use crate::utils::serialize_to_file;
    use test_utils::skip_if_ci;

    const EXTENDED_CIRCUIT_TRACE_LEN_LOG2: usize = 23;
    // The lookup tables (decoder 2^20 + sub-word memory 2^21 + the rest) exceed 2^22 rows, so
    // the large-field variant needs the full 2^23 trace as well.
    const LARGE_FIELD_EXTENDED_CIRCUIT_TRACE_LEN_LOG2: usize = 23;

    fn eval<F: PrimeField>(
        constraint: &crate::constraint::Constraint<F>,
        values: &std::collections::HashMap<Variable, F>,
    ) -> F {
        let mut result = F::ZERO;
        for term in constraint.terms.iter() {
            match term {
                Term::Constant(c) => {
                    result.add_assign(c);
                }
                Term::Expression {
                    coeff,
                    inner,
                    degree,
                } => {
                    let mut t = *coeff;
                    for v in &inner[..*degree] {
                        t.mul_assign(&values[v]);
                    }
                    result.add_assign(&t);
                }
            }
        }
        result
    }

    /// On every admitted row the PC advances by 4 exactly on executing non-Family-2 rows, the
    /// dispatch tie holds, and the memory family's word gate is 1 exactly on LW/SW rows.
    #[test]
    fn gates_match_their_flag_semantics_on_admitted_rows() {
        use crate::gkr_circuits::jump_branch_slt_family::{BRANCH_BIT, JALR_BIT, JAL_BIT, SLT_BIT};
        use ::field::baby_bear::base::BabyBearField;
        use ::field::proth120::Proth120;

        fn check<F: PrimeField>() {
            let execute = Variable(0);
            let bits: [Variable; UNIFIED_EXTENDED_MACHINE_NUM_FLAGS] =
                core::array::from_fn(|i| Variable(i as u64 + 1));
            let mask =
                UnifiedExtendedMachineFamilyCircuitMask::from_full_mask(bits.map(Boolean::Is));
            let word_gate: Expr<F> = Expr::from(mask.is_load()) + Expr::from(mask.is_store())
                - Expr::from(mask.is_load_subword())
                - Expr::from(mask.is_store_subword());
            let gates = [
                pc_bump_gate(execute, &mask),
                Expr::var(execute) - dispatch_sum(&mask),
                word_gate,
            ]
            .map(|e| e.to_max_quadratic_constraint());

            let executing: Vec<u32> = (0..1u32 << UNIFIED_EXTENDED_MACHINE_NUM_FLAGS)
                .filter(|&m| extended_decoder_mask_violation(m).is_none())
                .collect();
            assert_eq!(executing.len(), 24);
            for (is_executing, m) in executing.into_iter().map(|m| (true, m)).chain([(false, 0)]) {
                let mut values: std::collections::HashMap<_, _> = bits
                    .iter()
                    .enumerate()
                    .map(|(i, v)| (*v, F::from_u32_unchecked(m >> i & 1)))
                    .collect();
                values.insert(execute, F::from_u32_unchecked(is_executing as u32));
                let f2_flag = |b: usize| m >> (FAMILY_2_FLAG_OFFSET + b) & 1 == 1;
                let family_2 = [JAL_BIT, JALR_BIT, SLT_BIT, BRANCH_BIT]
                    .into_iter()
                    .any(f2_flag);
                let bit = |b: usize| m >> b & 1 == 1;
                let word = (bit(MEM_LOAD_BIT) || bit(MEM_STORE_BIT))
                    && !(bit(MEM_LOAD_SUBWORD_BIT) || bit(MEM_STORE_SUBWORD_BIT));
                let semantics = [is_executing && !family_2, false, word];
                for (i, (gate, expected)) in gates.iter().zip(semantics).enumerate() {
                    assert_eq!(
                        eval(gate, &values),
                        if expected { F::ONE } else { F::ZERO },
                        "gate {i}, execute {is_executing}, mask {m:#b}"
                    );
                }
            }
        }
        check::<BabyBearField>();
        check::<Proth120>();
    }

    /// The circuit builds in both fields and the artifact has the inline-i/t shape.
    #[test]
    fn compile_unified_extended_machine_with_inline_inits_and_teardowns() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let artifact = build_unified_extended_artifact::<BabyBearField>(
            true,
            EXTENDED_CIRCUIT_TRACE_LEN_LOG2,
            1,
        );
        assert!(artifact
            .global_output_map
            .contains_key(&OutputType::PermutationProduct));
        assert!(artifact
            .global_output_map
            .contains_key(&OutputType::InitsAndTeardownsProduct));
        assert!(!artifact.memory_layout.teardown_sets.is_empty());
        println!(
            "unified extended machine: {} memory + {} witness committed base columns",
            artifact.memory_layout.total_width, artifact.witness_layout.total_width
        );
    }

    #[test]
    fn compile_unified_extended_machine_into_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let artifact = build_unified_extended_artifact::<BabyBearField>(
            true,
            EXTENDED_CIRCUIT_TRACE_LEN_LOG2,
            1,
        );
        serialize_to_file(
            &artifact,
            "compiled_circuits/unified_extended_machine_layout_gkr.json",
        );
    }

    #[test]
    fn compile_unified_extended_machine_into_no_caches_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let artifact = build_unified_extended_artifact::<BabyBearField>(
            false,
            EXTENDED_CIRCUIT_TRACE_LEN_LOG2,
            1,
        );
        serialize_to_file(
            &artifact,
            "compiled_circuits/unified_extended_machine_layout_no_caches_gkr.json",
        );
    }

    #[test]
    fn compile_unified_extended_machine_gkr_witness_graph() {
        skip_if_ci!();
        use crate::gkr_compiler::dump_ssa_witness_eval_form;
        use ::field::baby_bear::base::BabyBearField;

        let ssa_forms = dump_ssa_witness_eval_form::<BabyBearField>(
            &|cs| unified_extended_register_all_tables(cs),
            &|cs| unified_extended_machine_circuit_with_preprocessed_bytecode_for_gkr(cs),
        );
        serialize_to_file(
            &ssa_forms,
            "compiled_circuits/unified_extended_machine_ssa_gkr.json",
        );
    }

    #[test]
    fn compile_unified_extended_machine_into_gkr_large_field() {
        skip_if_ci!();
        use ::field::proth120::Proth120;

        let artifact = build_unified_extended_artifact::<Proth120>(
            true,
            LARGE_FIELD_EXTENDED_CIRCUIT_TRACE_LEN_LOG2,
            1,
        );
        serialize_to_file(
            &artifact,
            "compiled_circuits/unified_extended_machine_layout_gkr_proth120.json",
        );
    }
}
