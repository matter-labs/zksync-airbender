use super::add_sub_lui_auipc_mop::apply_unified_add_sub_lui_auipc_mop_inner;
use super::binary_shifts::apply_unified_binary_shifts_inner;
use super::jump_branch_slt::apply_unified_jump_branch_slt_inner;
use super::jump_branch_slt::{
    jump_branch_slt_unified_table_addition_fn, jump_branch_slt_unified_table_driver_fn,
};
use super::mem_word_only::apply_unified_mem_word_only_inner;
use super::*;
use crate::cs::circuit_trait::*;
use crate::gkr_circuits::add_sub_family::{
    add_sub_lui_auipc_mop_table_addition_fn, add_sub_lui_auipc_mop_table_driver_fn,
};
use crate::gkr_circuits::mem_word_only::{
    mem_word_only_table_addition_fn, mem_word_only_table_driver_fn,
};
use crate::oracle::Placeholder;
use crate::structured_expr::Expr;
use crate::tables::TableDriver;
use crate::types::{Boolean, Num, Register, LIMB_WIDTH};
use crate::witness_placer::*;
use field::PrimeField;

/// Unified reduced-machine flag layout:
///
/// | Bit range  | Family                            | Count |
/// |------------|-----------------------------------|-------|
/// | [0..9)     | Family 1 (add_sub_lui_auipc_mop)  | 9     |
/// | [9]        | Family 1 unified-only tri-add     | 1     |
/// | [10..15)   | Family 2 (jump_branch_slt)        | 5     |
/// | [15..17)   | Family 3 (shift_binop)            | 2     |
/// | [17..19)   | Family 4 (mem_word_only)          | 2     |
///
/// (`ZimopIXorRot` rides the Family-3 binary-op bit [16] — no unified-only F3 flag.)
///
/// Family 4 is encoded one-hot in the unified bitmask (bit 17 = LW, bit 18 = SW)
/// to match the per-sub-opcode convention used by Families 1/2/3. This diverges
/// from the Family-4 standalone encoding (1 bit = is_store) but lets the unified
/// body read the LW/SW gates directly as Booleans without committing additional
/// witness columns.
///
/// (`REDUCED_MACHINE_NUM_FLAGS = 18` in `definitions::unrolled_families` includes
/// 1 reserved bit — `mem_subword_only`'s third sub-opcode bit (`SUBWORD_ONLY_MEMORY_FAMILY_NUM_FLAGS = 3`)
///  — that the unified reduced-machine layout doesn't allocate because mem_subword isn't part of the reduced-machine family set.)
pub const FAMILY_1_FLAG_OFFSET: usize = 0;
pub const UNIFIED_F1_NUM_FLAGS: usize = ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS + 1;
pub const FAMILY_1_TRI_ADD_BIT: usize =
    FAMILY_1_FLAG_OFFSET + ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS;

pub const FAMILY_2_FLAG_OFFSET: usize = FAMILY_1_FLAG_OFFSET + UNIFIED_F1_NUM_FLAGS;
pub const FAMILY_3_FLAG_OFFSET: usize = FAMILY_2_FLAG_OFFSET + JUMP_SLT_BRANCH_FAMILY_NUM_BITS;
pub const UNIFIED_F3_NUM_FLAGS: usize = SHIFT_BINARY_FAMILY_NUM_FLAGS;
pub const FAMILY_3_BINARY_OP_BIT: usize = FAMILY_3_FLAG_OFFSET + 1;

pub const FAMILY_4_FLAG_OFFSET: usize = FAMILY_3_FLAG_OFFSET + UNIFIED_F3_NUM_FLAGS;

/// Family 4 occupies 2 unified flags (one-hot LW/SW), independent of the standalone
/// `WORD_ONLY_MEMORY_FAMILY_NUM_FLAGS = 1` encoding.
pub const UNIFIED_FAMILY_4_NUM_FLAGS: usize = 2;
pub const FAMILY_4_LW_BIT: usize = FAMILY_4_FLAG_OFFSET;
pub const FAMILY_4_SW_BIT: usize = FAMILY_4_FLAG_OFFSET + 1;

pub const UNIFIED_REDUCED_MACHINE_NUM_FLAGS: usize = UNIFIED_F1_NUM_FLAGS
    + JUMP_SLT_BRANCH_FAMILY_NUM_BITS
    + UNIFIED_F3_NUM_FLAGS
    + UNIFIED_FAMILY_4_NUM_FLAGS;

/// Per-family count of *branch-local* scratch Booleans — committed Booleans used
/// only inside that family's flag-gated constraints, hence unconstrained (free)
/// on rows where the family is idle. Because at most one family fires per row,
/// these slots can be ALIASED across families into one shared pool.
pub(super) const F1_SCRATCH_BOOLS: usize = 5; // 2-input add/sub: carry, intermediate_carry ([0],[1]); tri-add (unified-only) also uses [2],[3] so each limb's carry ∈ {0,1,2} is a sum of two Booleans; two-field mop.rr reuses [2],[3],[4] for the q-top/k bits t0/t1/t2 (written only on is_mul_like/is_addmod/is_submod rows — disjoint from is_tri_add). Aliased (one-hot ⇒ ≤1 family/row) with F4's pooled bools: [0],[1]=of_lo,of_hi; [2]=is_rom; [3]=sw-align bit_0; [4]=sw-align bit_1 — and with F2's [4]=next_pc_bit_1.
pub(super) const F2_SCRATCH_BOOLS: usize = 5; // add_rel_{0,1}_{intermediate,final}_of (4) + next_pc_bit_1
pub(super) const F3_SCRATCH_BOOLS: usize = 0;
pub(super) const F4_SCRATCH_BOOLS: usize = 5; // of_lo, of_hi, is_rom, sw-align bit_0, bit_1

const fn const_max(a: usize, b: usize) -> usize {
    if a > b {
        a
    } else {
        b
    }
}

/// Shared base-layer scratch-Boolean pool size = max across families (one pool,
/// reused per row by whichever family fires)
const UNIFIED_SCRATCH_BOOL_COUNT: usize = const_max(
    const_max(F1_SCRATCH_BOOLS, F2_SCRATCH_BOOLS),
    const_max(F3_SCRATCH_BOOLS, F4_SCRATCH_BOOLS),
);

pub(super) const F1_SCRATCH_VARS: usize = 2; // two-field mop.rr quotient low limbs q_lo16, q_hi16 ([0],[1]); written only on is_mul_like rows and RC-16'd (unconditional, holds pool-wide since every family's value in [0],[1] is < 2^16). 0 on the single-field native path (F == MopF branch never touches these). Aliased with F2's [0]=comparison_result_is_zero,[1]=rs1_sign; F3's [0]=imm_sign_ext/trunc_shift,[1]=shift_output byte; F4's [0],[1]=ram_addr limbs.
pub(super) const F2_SCRATCH_VARS: usize = 5; // comparison_result_is_zero, rs1_sign, should_jump_or_slt_value, slt_sign_source, rs2_sign
pub(super) const F3_SCRATCH_VARS: usize = 21; // shift/binop scratch_space (17) + 4 rs1/rs2 low-byte split points (xor-rotate reuses the rs2 split: rs2 aliases rd at decode)
pub(super) const F4_SCRATCH_VARS: usize = 2; // ram_addr[0], ram_addr[1]

/// Shared base-layer scratch-Variable pool size = max across families.
const UNIFIED_SCRATCH_VAR_COUNT: usize = const_max(
    const_max(F1_SCRATCH_VARS, F2_SCRATCH_VARS),
    const_max(F3_SCRATCH_VARS, F4_SCRATCH_VARS),
);

pub(super) const F3_RS1_BYTE_SPLIT_SLOTS: [usize; 2] = [17, 18];
pub(super) const F3_RS2_BYTE_SPLIT_SLOTS: [usize; 2] = [19, 20];

/// The shared F1/F2/F4 register (F1 modular-op canonicity witness, F2 saved
/// PC / comparison result, F4 `top_14`) lives in Family 3's rs1 byte-split slots and the F2
/// PC temporary in a Family-3 shift-output slot; F1, F2 and F4 use none of them. Family 3's
/// values there are bytes, so the slots' unconditional RC-16 holds on every row. The register
/// avoids the shift-output slots: Family 2's RegIsZero peek reads it, and Family 3's
/// shift outputs depend on slot 0, which that peek writes, so the witness scheduler would
/// wait on itself.
const SHARED_REGISTER_SLOTS: [usize; 2] = F3_RS1_BYTE_SPLIT_SLOTS;
const F2_PC_TMP_SLOT: usize = 7;
const _: () = assert!(
    F2_PC_TMP_SLOT >= const_max(const_max(F1_SCRATCH_VARS, F2_SCRATCH_VARS), F4_SCRATCH_VARS)
        && SHARED_REGISTER_SLOTS[0] > F2_PC_TMP_SLOT
        && SHARED_REGISTER_SLOTS[1] < UNIFIED_SCRATCH_VAR_COUNT
);

pub(super) const UNIFIED_LOOKUP_WIDTH: usize = 8;

pub(super) struct LookupRequest<F: PrimeField> {
    table_id: Expr<F>,
    inputs: Vec<Expr<F>>,
}

impl<F: PrimeField> LookupRequest<F> {
    pub(super) fn new(table_id: Expr<F>, inputs: Vec<Expr<F>>) -> Self {
        assert!(
            inputs.len() <= UNIFIED_LOOKUP_WIDTH,
            "LookupRequest has {} inputs, exceeds UNIFIED_LOOKUP_WIDTH={UNIFIED_LOOKUP_WIDTH}",
            inputs.len()
        );
        assert!(table_id.degree() <= 2);
        for inp in inputs.iter() {
            assert!(inp.degree() <= 2);
        }

        Self { table_id, inputs }
    }
}

fn flush_unified_lookup_pool<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    per_family: &[Vec<LookupRequest<F>>],
) {
    let num_slots = per_family.iter().map(Vec::len).max().unwrap_or(0);
    for k in 0..num_slots {
        // Pool the per-family requests for slot `k` by adding their `Expr`s (a slot no family
        // populates stays `None` and folds in as the constant 0). Kept as `Expr` so each masked
        // product `mask * input` reaches the compiler as one multiplication rather than the
        // distributed sum a flattened `Constraint` would produce.
        let mut table_id: Option<Expr<F>> = None;
        let mut inputs: [Option<Expr<F>>; UNIFIED_LOOKUP_WIDTH] = core::array::from_fn(|_| None);
        for family in per_family {
            let Some(req) = family.get(k) else { continue };
            assert!(req.inputs.len() <= UNIFIED_LOOKUP_WIDTH);
            table_id = Some(match table_id.take() {
                None => req.table_id.clone(),
                Some(acc) => acc + req.table_id.clone(),
            });
            for (j, inp) in req.inputs.iter().enumerate() {
                inputs[j] = Some(match inputs[j].take() {
                    None => inp.clone(),
                    Some(acc) => acc + inp.clone(),
                });
            }
        }
        let table_id_var = cs.add_intermediate_named_variable_from_expr(
            table_id.expect("a pooled slot must have at least one contributing family"),
            &format!("pooled lookup table_id (slot {k})"),
        );
        let tuple: [LookupInput<F>; UNIFIED_LOOKUP_WIDTH] = core::array::from_fn(|j| {
            // Positions no family populates fold in as the constant 0 (no column).
            match inputs[j].take() {
                None => LookupInput::from(F::ZERO),
                Some(expr) => LookupInput::from(cs.add_intermediate_named_variable_from_expr(
                    expr,
                    &format!("pooled lookup input (slot {k}, pos {j})"),
                )),
            }
        });
        cs.enforce_lookup_tuple_for_variable_table::<UNIFIED_LOOKUP_WIDTH>(&tuple, table_id_var);
    }
}

const UNIFIED_XOR_ROTATE_TABLES: [TableType; 4] = [
    TableType::XorRotate16,
    TableType::XorRotate12,
    TableType::XorRotate8,
    TableType::XorRotate7,
];

const UNIFIED_F3_BASE_TABLES: [TableType; 4] = [
    TableType::ZeroEntry, // needed for conditional lookup enforcements
    TableType::TruncateShiftAmountAndRangeCheck8,
    TableType::GetSignExtensionByte,
    TableType::ShiftImplementationOverBytes,
];

const UNIFIED_WIDE_BINOP_TABLES: [TableType; 3] =
    [TableType::WideXor, TableType::WideOr, TableType::WideAnd];

pub fn unified_reduced_machine_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    add_sub_lui_auipc_mop_table_addition_fn(cs);
    jump_branch_slt_unified_table_addition_fn(cs);
    mem_word_only_table_addition_fn(cs);
    for t in UNIFIED_F3_BASE_TABLES
        .into_iter()
        .chain(UNIFIED_WIDE_BINOP_TABLES)
        .chain(UNIFIED_XOR_ROTATE_TABLES)
    {
        cs.materialize_table::<UNIFIED_LOOKUP_WIDTH>(t);
    }
}

pub fn unified_reduced_machine_table_driver_fn<F: PrimeField>(table_driver: &mut TableDriver<F>) {
    add_sub_lui_auipc_mop_table_driver_fn(table_driver);
    jump_branch_slt_unified_table_driver_fn(table_driver);
    mem_word_only_table_driver_fn(table_driver);
    for t in UNIFIED_F3_BASE_TABLES
        .into_iter()
        .chain(UNIFIED_WIDE_BINOP_TABLES)
        .chain(UNIFIED_XOR_ROTATE_TABLES)
    {
        table_driver.materialize_table::<UNIFIED_LOOKUP_WIDTH>(t);
    }
}

/// Wrapper preserving the historic single-field signature; delegates to the
/// two-generic core with the mop field fixed to `BabyBearField` — the only mop.rr
/// field (asserted in `mop_two_field_decompose`). For `F = BabyBearField` this is
/// the native single-field path; for a large `F` (e.g. Proth120) it IS the
/// two-field instantiation. The `_core` form exists for the generic threading,
/// not as an extension point for other mop fields.
pub fn unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr<
    F: PrimeField,
    CS: Circuit<F>,
>(
    cs: &mut CS,
) {
    unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr_core::<
        F,
        ::field::baby_bear::base::BabyBearField,
        CS,
    >(cs);
}

/// Top-level unified circuit body. Allocates a single shared set of memory accesses
/// for all reduced-machine families, then dispatches to each family's per-flag body.
/// Per-family bodies don't allocate their own accesses — they accept extracted
/// limbs/timestamps as parameters.
pub fn unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr_core<
    F: PrimeField,
    MopF: PrimeField,
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
    let bitmask = bitmask.map(Boolean::Is);

    apply_unified_reduced_machine_inner::<F, MopF, _>(cs, input, bitmask);
}

fn apply_unified_reduced_machine_inner<F: PrimeField, MopF: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    bitmask: [Boolean; UNIFIED_REDUCED_MACHINE_NUM_FLAGS],
) {
    let unified_mask = UnifiedReducedMachineFamilyCircuitMask::from_full_mask(bitmask);
    let is_lw = unified_mask.is_lw();
    let is_sw = unified_mask.is_sw();

    // Allocate the 3 memory accesses ONCE — shared across all families.
    //
    // rs1 is always a register read (every family needs rs1). rs2 and rd are
    // `RegisterOrRam` to accommodate Family 4 LW (rs2-slot ≡ RAM read) and Family 4
    // SW (rd-slot ≡ RAM write); Families 1-3 + the matching half of Family 4 keep
    // them as register accesses by pinning `is_register = NOT is_lw / NOT is_sw`.
    //
    // rs1 + rs2 are committed as U16 limbs (matched limb-for-limb against the
    // RC-16 writes, so each limb is canonically pinned). Families 1/2/4 use the
    // U16 halves directly. Family 3's byte-keyed lookups decompose each U16 limb
    // on demand (1 committed scratch byte + 1 free linear-expression byte), and
    // the byte-table membership range-checks both to u8 — so no separate RC-8 and
    // no operand bytes committed to the memory oracle. rd write remains U16.
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
            split_as_u8: false,
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

    // Each family body adds constraints gated by its own flag bits. Family-internal
    // flags within each family are mutually exclusive (decoder lookup binds to family
    // sub-spaces), so adding all bodies' constraints is sound: at most one family's
    // is_* flags are 1 per cycle. Family 4's body owns the cleanaddr/ROM/lookup
    // logic and the register-side address-binding constraints (gated on
    // `NOT is_lw` / `NOT is_sw`, which fire for Families 1-3 too).
    apply_unified_add_sub_lui_auipc_mop_inner::<F, MopF, _>(
        cs,
        inputs.clone(),
        unified_mask.add_sub_lui_auipc_mop(),
        unified_mask.perform_tri_add(),
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
        unified_mask.jump_branch_slt(),
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
        unified_mask.binary_shifts(),
        rs1_limbs,
        rs2_limbs,
        rd_write_limbs,
        core::array::from_fn::<_, F3_SCRATCH_VARS, _>(|i| scratch_vars[i]),
    );
    let pc_in = inputs.cycle_start_state.pc;
    let pc_out = inputs.cycle_end_state.pc;
    let execute = inputs.execute;
    let f4_lookups = apply_unified_mem_word_only_inner(
        cs,
        inputs,
        is_lw,
        is_sw,
        rs1_limbs,
        rs2_access,
        rd_access,
        core::array::from_fn::<_, F4_SCRATCH_BOOLS, _>(|i| scratch_bools[i]),
        core::array::from_fn::<_, F4_SCRATCH_VARS, _>(|i| scratch_vars[i]),
        shared_intermediate_reg.0[0].get_variable(),
    );

    flush_unified_lookup_pool(cs, &[f2_lookups, f3_lookups, f4_lookups]);

    // Unified PC bump (gated). Families 1, 3, 4 leave PC handling to the caller;
    // Family 2 (jump_branch_slt) owns its own gated PC logic for jal/jalr/branch/slt.
    // We add `pc_next = pc + 4` constraints that fire only when (cycle executes) AND
    // (no Family-2 sub-opcode is active). Padding rows have execute=0 → trivially satisfied.
    apply_unified_pc_bump(cs, pc_in, pc_out, execute, &unified_mask);

    apply_unified_family_dispatch_one_hot(cs, execute, &unified_mask);
}

/// Σ of all 18 dispatch bits (every family bit except Family 2's RD_IS_ZERO).
pub(super) fn dispatch_sum<F: PrimeField>(
    unified_mask: &UnifiedReducedMachineFamilyCircuitMask,
) -> Expr<F> {
    let non_f2_sum = Expr::sum(
        unified_mask
            .add_sub_lui_auipc_mop_bits()
            .into_iter()
            .chain(unified_mask.binary_shifts_bits())
            .chain([unified_mask.is_lw(), unified_mask.is_sw()])
            .map(Expr::from)
            .collect(),
    );
    let family_2_bits = unified_mask.jump_branch_slt_bits();
    Expr::sum(
        std::iter::once(non_f2_sum)
            .chain(family_2_bits[..4].iter().map(|&b| Expr::from(b)))
            .collect(),
    )
}

/// PC-bump gate: `execute − Σ` Family 2 sub-opcode bits (JAL, JALR, SLT, BRANCH; not
/// RD_IS_ZERO). On admitted rows it is 1 on executing non-Family-2 rows and 0 on Family 2
/// rows and padding.
pub(super) fn pc_bump_gate<F: PrimeField>(
    execute: Variable,
    unified_mask: &UnifiedReducedMachineFamilyCircuitMask,
) -> Expr<F> {
    let family_2_bits = unified_mask.jump_branch_slt_bits();
    Expr::var(execute) - Expr::sum(family_2_bits[..4].iter().map(|&b| Expr::from(b)).collect())
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
    unified_mask: &UnifiedReducedMachineFamilyCircuitMask,
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
            placer.assign_mask(pc_inc_carry.expect_variable(), &carry);
        };
        cs.set_values(value_fn);
    }

    let pc_bump_gate = pc_bump_gate(execute, unified_mask);

    let pc_step: Expr<F> =
        Expr::constant(F::from_u32_with_reduction(common_constants::PC_STEP as u32));
    let shift16: Expr<F> = Expr::constant(F::from_u32_with_reduction(1 << 16));

    // pc_bump_gate * (pc_in[0] + 4 - pc_out[0] - 2^16 * pc_inc_carry) = 0  (deg 2)
    cs.add_constraint_expr(
        pc_bump_gate.clone()
            * (Expr::var(pc_in[0]) + pc_step
                - Expr::var(pc_out[0])
                - shift16 * Expr::from(pc_inc_carry)),
    );
    // pc_bump_gate * (pc_inc_carry + pc_in[1] - pc_out[1]) = 0  (deg 2)
    cs.add_constraint_expr(
        pc_bump_gate * (Expr::from(pc_inc_carry) + Expr::var(pc_in[1]) - Expr::var(pc_out[1])),
    );
}

/// pin that exactly one family fires per executing cycle: the linear tie
/// `execute = Σ dispatch bits`.
fn apply_unified_family_dispatch_one_hot<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    execute: crate::definitions::Variable,
    unified_mask: &UnifiedReducedMachineFamilyCircuitMask,
) {
    let family_1_bits = unified_mask.add_sub_lui_auipc_mop_bits();
    let family_2_bits = unified_mask.jump_branch_slt_bits();
    let family_3_bits = unified_mask.binary_shifts_bits();
    let is_lw = unified_mask.is_lw();
    let is_sw = unified_mask.is_sw();

    cs.add_constraint_expr_allow_explicit_linear_prevent_optimizations_expr(
        Expr::var(execute) - dispatch_sum(unified_mask),
    );

    // Padding-row zeroing: on execute=0 rows, the decoder lookup is gated by
    // `execute` and so doesn't bind the bitmask — without this constraint a
    // malicious witness could set arbitrary family-bits on padding rows. Pin
    // ALL family bits (including family_2_bits[4] = RD_IS_ZERO_BIT) to 0 when
    // execute=0. Booleanity of each bit plus the constraint
    //   (1 - execute) * (sum of all family bits) = 0
    // forces the sum to 0 in the field, which forces each bit to 0 (since each
    // is in {0,1}). One degree-2 constraint covers all 19 bits.
    let mut padding_zero_sum: Expr<F> = Expr::zero();
    for &b in family_1_bits.iter() {
        padding_zero_sum = padding_zero_sum + Expr::from(b);
    }
    for &b in family_2_bits.iter() {
        padding_zero_sum = padding_zero_sum + Expr::from(b);
    }
    for &b in family_3_bits.iter() {
        padding_zero_sum = padding_zero_sum + Expr::from(b);
    }
    padding_zero_sum = padding_zero_sum + Expr::from(is_lw);
    padding_zero_sum = padding_zero_sum + Expr::from(is_sw);
    cs.add_constraint_expr((Expr::<F>::one() - Expr::var(execute)) * padding_zero_sum);
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
/// Single source of truth used by the cs-side serialization tests below,
/// the verifier_generator integration test, and the `unified_reduced_machine`
/// setup crate that wires the circuit into the GKR prover.
///
/// BabyBear wrapper preserving the historic single-field signature; delegates to
/// `build_unified_artifact_core` with `MopF = BabyBearField`.
pub fn build_unified_artifact<F: ::field::PrimeField>(
    use_caches: bool,
    trace_len_log2: usize,
    num_init_and_teardown_pairs: usize,
) -> crate::gkr_compiler::GKRCircuitArtifact<F> {
    build_unified_artifact_core::<F, ::field::baby_bear::base::BabyBearField>(
        use_caches,
        trace_len_log2,
        num_init_and_teardown_pairs,
    )
}

pub fn build_unified_artifact_core<F: ::field::PrimeField, MopF: ::field::PrimeField>(
    use_caches: bool,
    trace_len_log2: usize,
    num_init_and_teardown_pairs: usize,
) -> crate::gkr_compiler::GKRCircuitArtifact<F> {
    use crate::cs::circuit_impl::BasicAssembly;
    use crate::gkr_compiler::GKRCompiler;

    let mut cs = BasicAssembly::<F>::new();
    unified_register_all_tables(&mut cs);
    unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr_core::<F, MopF, _>(&mut cs);
    let (cs_output, _) = cs.finalize();

    let compiler = GKRCompiler::<F>::default();
    compiler.compile_family_circuit_with_inline_inits_and_teardowns(
        cs_output,
        common_constants::ROM_WORD_SIZE,
        /* num_inits_and_teardowns_pairs */ num_init_and_teardown_pairs,
        /* trace_len_log2 */ trace_len_log2,
        use_caches,
    )
}

#[cfg(test)]
mod test {
    use crate::constraint::Term;
    use test_utils::skip_if_ci;

    const UNIFIED_CIRCUIT_TRACE_LEN_LOG2: usize = 23;
    const LARGE_FIELD_UNIFIED_CIRCUIT_TRACE_LEN_LOG2: usize = 22;

    use super::*;
    use crate::definitions::OutputType;
    use crate::utils::serialize_to_file;

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

    /// On every admitted row (an executing row whose mask passes the check the decoder table
    /// build enforces, or a padding row, whose flags are zero): JAL/JALR write rd unless
    /// rd = x0, SLT writes rd unless rd = x0, a Family 2 row with rd = x0 writes zero, the PC
    /// advances by 4 exactly on executing non-Family-2 rows, and an executing row has exactly
    /// one dispatch bit.
    #[test]
    fn gates_match_their_flag_semantics_on_admitted_rows() {
        use super::super::decoder::unified_decoder_mask_violation;
        use super::super::jump_branch_slt::f2_rd_write_gates;
        use crate::gkr_circuits::jump_branch_slt_family::{
            BRANCH_BIT, JALR_BIT, JAL_BIT, RD_IS_ZERO_BIT, SLT_BIT,
        };
        use ::field::baby_bear::base::BabyBearField;
        use ::field::proth120::Proth120;

        fn check<F: PrimeField>() {
            let execute = Variable(0);
            let bits: [Variable; UNIFIED_REDUCED_MACHINE_NUM_FLAGS] =
                core::array::from_fn(|i| Variable(i as u64 + 1));
            let mask =
                UnifiedReducedMachineFamilyCircuitMask::from_full_mask(bits.map(Boolean::Is));
            let f2 = mask.jump_branch_slt();
            let [jal_or_jalr_writes_rd, slt_writes_rd, rd_is_x0] = f2_rd_write_gates(
                f2.perform_jal(),
                f2.perform_jalr(),
                f2.perform_slt(),
                f2.perform_branch(),
                f2.rd_is_zero(),
            );
            let gates = [
                jal_or_jalr_writes_rd,
                slt_writes_rd,
                rd_is_x0,
                pc_bump_gate(execute, &mask),
                Expr::var(execute) - dispatch_sum(&mask),
            ]
            .map(|e| e.to_max_quadratic_constraint());

            let executing: Vec<u32> = (0..1u32 << UNIFIED_REDUCED_MACHINE_NUM_FLAGS)
                .filter(|&m| unified_decoder_mask_violation(m).is_none())
                .collect();
            assert_eq!(executing.len(), 20);
            for (is_executing, m) in executing.into_iter().map(|m| (true, m)).chain([(false, 0)]) {
                let mut values: std::collections::HashMap<_, _> = bits
                    .iter()
                    .enumerate()
                    .map(|(i, v)| (*v, F::from_u32_unchecked(m >> i & 1)))
                    .collect();
                values.insert(execute, F::from_u32_unchecked(is_executing as u32));
                let f2_flag = |b: usize| m >> (FAMILY_2_FLAG_OFFSET + b) & 1 == 1;
                let [jal, jalr, slt, branch, rd_is_zero] =
                    [JAL_BIT, JALR_BIT, SLT_BIT, BRANCH_BIT, RD_IS_ZERO_BIT].map(f2_flag);
                let family_2 = jal || jalr || slt || branch;
                let semantics = [
                    (jal || jalr) && !rd_is_zero,
                    slt && !rd_is_zero,
                    family_2 && rd_is_zero,
                    is_executing && !family_2,
                    false,
                ];
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

    /// The committed layouts and witness graphs of both fields: each scratch slot that holds
    /// another family's u16 limb (the shared register and the Family 2 PC temporary) has
    /// exactly one bare RC-16 lookup and no u8 or bool writer. The generated witness function
    /// reads a masked-off target back at the writer's own width, so a narrow writer would
    /// truncate the limb.
    #[test]
    fn aliased_scratch_slots_are_range_checked_and_written_at_least_u16() {
        use crate::gkr_compiler::GKRCircuitArtifact;
        use crate::witness_placer::graph_description::{Expression, RawExpression};
        use ::field::baby_bear::base::BabyBearField;
        use ::field::proth120::Proth120;

        fn read_json<T: serde::de::DeserializeOwned>(path: &str) -> T {
            let file = std::fs::File::open(path).unwrap_or_else(|e| panic!("{path}: {e}"));
            serde_json::from_reader(std::io::BufReader::new(file)).unwrap()
        }

        fn check<F: PrimeField + serde::de::DeserializeOwned>(layout: &str, ssa: &str) {
            let artifact: GKRCircuitArtifact<F> = read_json(layout);
            let ssa: Vec<Vec<RawExpression<F>>> = read_json(ssa);
            let slot_var = |slot: usize| {
                let name = format!("shared scratch var[{slot}]");
                let vars: Vec<Variable> = artifact
                    .variable_names
                    .iter()
                    .filter(|(_, n)| **n == name)
                    .map(|(v, _)| *v)
                    .collect();
                assert_eq!(vars.len(), 1, "{layout}: {name}");
                vars[0]
            };
            let writer_types = |slot: usize| -> Vec<&'static str> {
                let var = slot_var(slot);
                ssa.iter()
                    .flatten()
                    .filter_map(|e| match e {
                        RawExpression::WriteVariable {
                            into_variable,
                            source_subexpr,
                            ..
                        } if *into_variable == var => Some(match source_subexpr {
                            Expression::Bool(_) => "bool",
                            Expression::Field(_) => "field",
                            Expression::U8(_) => "u8",
                            Expression::U16(_) => "u16",
                            Expression::U32(_) => "u32",
                        }),
                        _ => None,
                    })
                    .collect()
            };
            for slot in SHARED_REGISTER_SLOTS.into_iter().chain([F2_PC_TMP_SLOT]) {
                let addr = artifact.placement_data[&slot_var(slot)];
                let range_checks = artifact
                    .range_check_16_lookup_expressions
                    .iter()
                    .filter(|l| {
                        l.input.is_trivial_single_input() && l.input.linear_terms[0].1 == addr
                    })
                    .count();
                assert_eq!(range_checks, 1, "{layout} slot {slot}: RC-16 lookups");
                let types = writer_types(slot);
                assert!(types.len() >= 2, "{layout} slot {slot}: writers {types:?}");
                assert!(
                    types.iter().all(|t| !matches!(*t, "u8" | "bool")),
                    "{layout} slot {slot}: writers {types:?}"
                );
            }
            let byte_slot = F3_RS2_BYTE_SPLIT_SLOTS[0];
            assert!(
                writer_types(byte_slot).contains(&"u8"),
                "{layout}: slot {byte_slot}'s byte writer not seen"
            );
        }

        check::<BabyBearField>(
            "compiled_circuits/unified_reduced_machine_layout_gkr.json",
            "compiled_circuits/unified_reduced_machine_ssa_gkr.json",
        );
        check::<Proth120>(
            "compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
            "compiled_circuits/unified_reduced_machine_ssa_gkr_proth120.json",
        );
    }

    #[test]
    fn unified_rs2_sign_lookup_reads_slt_sign_source_scratch() {
        use crate::cs::circuit_impl::BasicAssembly;
        use crate::tables::TableType;
        use ::field::baby_bear::base::BabyBearField;

        let mut cs = BasicAssembly::<BabyBearField>::new();
        unified_register_all_tables(&mut cs);
        unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr(&mut cs);
        let (output, _) = cs.finalize();

        let var_by_name = |name: &str| {
            output
                .variable_names
                .iter()
                .find(|(_, n)| n.as_str() == name)
                .map(|(v, _)| *v)
        };
        // Pooled lookup intermediates are now defined from `Expr` via
        // `add_intermediate_named_variable_from_expr`; `variables_from_constraints` maps the
        // variable to the index of its `Define` statement, which carries the lowered
        // (max-quadratic) `compiled_constraint`.
        let defining_constraint = |var: Variable| -> &crate::constraint::Constraint<BabyBearField> {
            let idx = output.variables_from_constraints[&var];
            match &output.structured_statements[idx] {
                crate::structured_expr::StructuredStatement::Define {
                    compiled_constraint,
                    ..
                } => compiled_constraint,
                other => panic!("expected a Define statement for {var:?}, got {other:?}"),
            }
        };
        let slt_sign_source =
            var_by_name("shared scratch var[3]").expect("F2 sign-source scratch var must exist");
        let u16getsign_id =
            BabyBearField::from_u32(TableType::U16GetSign as u32).expect("table id fits");

        // Walk the pooled lookup slots by their generated names; stop at the first gap.
        let mut found = false;
        for k in 0..UNIFIED_LOOKUP_WIDTH * 8 {
            let Some(tid_var) = var_by_name(&format!("pooled lookup table_id (slot {k})")) else {
                break;
            };
            let tid_c = defining_constraint(tid_var);
            // F2's contribution to the slot's table id is `is_fam2_sum() * U16GetSign`,
            // i.e. degree-1 terms with the table id as coefficient.
            let has_u16getsign = tid_c.terms.iter().any(|t| {
                matches!(t, Term::Expression { coeff, degree: 1, .. } if *coeff == u16getsign_id)
            });
            let Some(in0_var) = var_by_name(&format!("pooled lookup input (slot {k}, pos 0)"))
            else {
                continue;
            };
            let in0_c = defining_constraint(in0_var);
            let reads_sign_source = in0_c
                .terms
                .iter()
                .any(|t| t.as_slice().contains(&slt_sign_source));
            if has_u16getsign && reads_sign_source {
                found = true;
                break;
            }
        }
        assert!(
            found,
            "some pooled lookup slot must extract the rs2 sign via U16GetSign fed by \
             the F2 sign-source scratch var (slt_sign_source), not by raw rs2_high"
        );
    }

    /// Sanity-check the artifact shape: both output channels present + i/t
    /// teardown_sets populated. Doesn't write anything to disk.
    #[test]
    fn compile_unified_reduced_machine_with_inline_inits_and_teardowns() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let artifact =
            build_unified_artifact::<BabyBearField>(true, UNIFIED_CIRCUIT_TRACE_LEN_LOG2, 1);

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

        let artifact =
            build_unified_artifact::<BabyBearField>(true, UNIFIED_CIRCUIT_TRACE_LEN_LOG2, 1);
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

        let artifact =
            build_unified_artifact::<BabyBearField>(false, UNIFIED_CIRCUIT_TRACE_LEN_LOG2, 1);
        serialize_to_file(
            &artifact,
            "compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json",
        );
    }

    /// SSA witness graph dump for the unified circuit. Needed by
    /// `witness_eval_generator::gen_for_gkr` to produce
    /// `prover/compiled_circuits/unified_reduced_machine_generated_gkr.rs`
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

    #[test]
    fn compile_unified_reduced_machine_into_gkr_large_field() {
        skip_if_ci!();
        use ::field::proth120::Proth120;

        let artifact =
            build_unified_artifact::<Proth120>(true, LARGE_FIELD_UNIFIED_CIRCUIT_TRACE_LEN_LOG2, 1);
        serialize_to_file(
            &artifact,
            "compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
        );
    }

    #[test]
    fn compile_unified_reduced_machine_gkr_witness_graph_large_field() {
        skip_if_ci!();
        use crate::gkr_compiler::dump_ssa_witness_eval_form;
        use ::field::proth120::Proth120;

        let ssa_forms =
            dump_ssa_witness_eval_form::<Proth120>(&|cs| unified_register_all_tables(cs), &|cs| {
                unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr(cs)
            });
        serialize_to_file(
            &ssa_forms,
            "compiled_circuits/unified_reduced_machine_ssa_gkr_proth120.json",
        );
    }
}
