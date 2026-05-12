use super::*;
use cs::cs::circuit::DisjunctiveLookup;
use cs::cs::circuit::DisjunctiveLookupGuard;
use cs::types::Boolean;
use cs::types::Num;

const U16_BOUND: u64 = 1 << 16;
const U12_BOUND: u64 = 1 << 12;
const U14_BOUND: u64 = 1 << 14;
const U8_BOUND: u64 = 1 << 8;
const U4_BOUND: u64 = 1 << 4;
const PICUS_CHUNK_BOUND: u64 = 1 << 30;

/// Allocates `width` boolean indicators and constrains them to be one-hot.
///
/// This helper is used by table handlers that need an explicit one-hot
/// decomposition in PCL.
fn add_one_hot_bits(
    module: &mut PicusModule,
    width: usize,
    next_fresh_var_id: &mut usize,
) -> Vec<PicusExpr> {
    let mut bits = Vec::with_capacity(width);
    for _ in 0..width {
        let b = fresh_picus_var_expr(next_fresh_var_id);
        module.constraints.push(PicusConstraint::new_bit(b.clone()));
        bits.push(b);
    }

    let sum = bits
        .iter()
        .cloned()
        .fold(PicusExpr::Const(0), |acc, b| acc + b);
    module
        .constraints
        .push(PicusConstraint::new_equality(sum, PicusExpr::Const(1)));

    bits
}

/// Translation for `JumpCleanupOffset` lookup.
///
/// Table intent: decompose a low PC limb into aligned and bit components used
/// when cleaning up jump targets.
///
/// Extraction strategy: keep the arithmetic decomposition (`a = cleaned + 2*bit_1 + bit_0`)
/// and alignment relation (`cleaned = 4*k`) with appropriate bit/range guards.
fn add_jump_cleanup_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
) {
    let a = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let bit_1 = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let cleaned = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);

    let bit_0 = fresh_picus_var_expr(next_fresh_var_id);
    let k = fresh_picus_var_expr(next_fresh_var_id);

    module
        .constraints
        .push(PicusConstraint::new_lt(a.clone(), U16_BOUND.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(cleaned.clone(), U16_BOUND.into()));
    module
        .constraints
        .push(PicusConstraint::new_bit(bit_0.clone()));
    module
        .constraints
        .push(PicusConstraint::new_bit(bit_1.clone()));
    module
        .constraints
        .push(PicusConstraint::new_lt(k.clone(), U14_BOUND.into()));

    // a = cleaned + 2*bit_1 + bit_0
    module.constraints.push(PicusConstraint::new_equality(
        a,
        cleaned.clone() + PicusExpr::Const(2) * bit_1 + bit_0,
    ));
    // cleaned = 4*k
    module.constraints.push(PicusConstraint::new_equality(
        cleaned,
        PicusExpr::Const(4) * k,
    ));
}

/// Translation for `ConditionalJmpBranchSlt` lookup.
///
/// Table intent: resolve branch/SLT condition flags from packed condition inputs.
///
/// Extraction strategy: preserve the full logical/arithmetic encoding because the
/// table captures control-sensitive semantics that are not represented by a simple
/// determinism summary.
fn add_conditional_jmp_branch_slt_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
) {
    let a = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let f3 = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let flag = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);

    let uf = fresh_picus_var_expr(next_fresh_var_id);
    let out_is_zero = fresh_picus_var_expr(next_fresh_var_id);
    let sign1 = fresh_picus_var_expr(next_fresh_var_id);
    let sign2 = fresh_picus_var_expr(next_fresh_var_id);

    module
        .constraints
        .push(PicusConstraint::new_lt(a.clone(), 16u64.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(f3.clone(), 8u64.into()));
    module
        .constraints
        .push(PicusConstraint::new_bit(uf.clone()));
    module
        .constraints
        .push(PicusConstraint::new_bit(out_is_zero.clone()));
    module
        .constraints
        .push(PicusConstraint::new_bit(sign1.clone()));
    module
        .constraints
        .push(PicusConstraint::new_bit(sign2.clone()));
    module
        .constraints
        .push(PicusConstraint::new_bit(flag.clone()));

    // a = uf + 2*out_is_zero + 4*sign1 + 8*sign2
    module.constraints.push(PicusConstraint::new_equality(
        a,
        uf.clone()
            + PicusExpr::Const(2) * out_is_zero.clone()
            + PicusExpr::Const(4) * sign1.clone()
            + PicusExpr::Const(8) * sign2.clone(),
    ));

    let signs_different =
        sign1.clone() + sign2.clone() - (PicusExpr::Const(2) * sign1.clone() * sign2.clone());
    let unsigned_lt = uf.clone();
    let signed_lt = sign1.clone() * signs_different.clone()
        + unsigned_lt.clone() * (PicusExpr::Const(1) - signs_different);
    let eq = out_is_zero;

    // one-hot for funct3
    let mut f3_one_hot = Vec::with_capacity(8);
    for _ in 0..8 {
        let b = fresh_picus_var_expr(next_fresh_var_id);
        module.constraints.push(PicusConstraint::new_bit(b.clone()));
        f3_one_hot.push(b);
    }
    let one_hot_sum = f3_one_hot
        .iter()
        .cloned()
        .fold(PicusExpr::Const(0), |acc, x| acc + x);
    module.constraints.push(PicusConstraint::new_equality(
        one_hot_sum,
        PicusExpr::Const(1),
    ));

    let f3_reconstructed = f3_one_hot
        .iter()
        .enumerate()
        .fold(PicusExpr::Const(0), |acc, (i, b)| {
            acc + PicusExpr::Const(i as u64) * b.clone()
        });
    module
        .constraints
        .push(PicusConstraint::new_equality(f3, f3_reconstructed));

    let expected_flag = f3_one_hot[0].clone() * eq.clone()
        + f3_one_hot[1].clone() * (PicusExpr::Const(1) - eq.clone())
        + f3_one_hot[2].clone() * signed_lt.clone()
        + f3_one_hot[3].clone() * unsigned_lt.clone()
        + f3_one_hot[4].clone() * signed_lt.clone()
        + f3_one_hot[5].clone() * (PicusExpr::Const(1) - signed_lt.clone())
        + f3_one_hot[6].clone() * unsigned_lt.clone()
        + f3_one_hot[7].clone() * (PicusExpr::Const(1) - unsigned_lt);
    module
        .constraints
        .push(PicusConstraint::new_equality(flag, expected_flag));
}

/// Translation for `MemoryGetOffsetAndMaskWithTrap` lookup.
///
/// Table intent: map packed memory access metadata to offset and trap/mask bits.
///
/// Extraction strategy: use a compact summary with input/output range bounds and a
/// determinism axiom `det(input) => (det(offset) && det(bitmask))`.
fn add_memory_get_offset_and_mask_with_trap_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    _next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
) {
    let input = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let offset = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let bitmask = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);

    module
        .constraints
        .push(PicusConstraint::new_lt(input.clone(), (1u64 << 21).into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(offset.clone(), U4_BOUND.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(bitmask.clone(), U8_BOUND.into()));

    // det(input) => (det(offset) && det(bitmask))
    let det_input = PicusConstraint::new_det(input);
    let det_offset = PicusConstraint::new_det(offset);
    let det_bitmask = PicusConstraint::new_det(bitmask);
    module.constraints.push(PicusConstraint::Implies(
        Box::new(det_input),
        Box::new(PicusConstraint::And(
            Box::new(det_offset),
            Box::new(det_bitmask),
        )),
    ));
}

fn add_conditional_op_resolution_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
    support_signed: bool,
) {
    let input = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let should_branch = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let should_store = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);

    let funct3 = fresh_picus_var_expr(next_fresh_var_id);
    let unsigned_lt = fresh_picus_var_expr(next_fresh_var_id);
    let eq = fresh_picus_var_expr(next_fresh_var_id);

    module
        .constraints
        .push(PicusConstraint::new_lt(funct3.clone(), 8u64.into()));
    module
        .constraints
        .push(PicusConstraint::new_bit(unsigned_lt.clone()));
    module
        .constraints
        .push(PicusConstraint::new_bit(eq.clone()));

    let mut reconstructed = funct3.clone()
        + PicusExpr::Const(8) * unsigned_lt.clone()
        + PicusExpr::Const(16) * eq.clone();

    let (signed_lt, not_signed_lt, signed_store) = if support_signed {
        let src1_sign = fresh_picus_var_expr(next_fresh_var_id);
        let src2_sign = fresh_picus_var_expr(next_fresh_var_id);
        let diff_signs = fresh_picus_var_expr(next_fresh_var_id);
        let not_diff_signs = PicusExpr::Const(1) - diff_signs.clone();
        let signed_lt = fresh_picus_var_expr(next_fresh_var_id);

        module
            .constraints
            .push(PicusConstraint::new_bit(src1_sign.clone()));
        module
            .constraints
            .push(PicusConstraint::new_bit(src2_sign.clone()));
        module
            .constraints
            .push(PicusConstraint::new_bit(diff_signs.clone()));
        module
            .constraints
            .push(PicusConstraint::new_bit(signed_lt.clone()));

        module.constraints.push(PicusConstraint::new_equality(
            diff_signs.clone(),
            src1_sign.clone() + src2_sign.clone()
                - PicusExpr::Const(2) * src1_sign.clone() * src2_sign.clone(),
        ));
        module.constraints.push(PicusConstraint::new_equality(
            signed_lt.clone(),
            diff_signs.clone() * src1_sign.clone() + not_diff_signs * unsigned_lt.clone(),
        ));

        reconstructed =
            reconstructed + PicusExpr::Const(32) * src1_sign + PicusExpr::Const(64) * src2_sign;

        (
            signed_lt.clone(),
            PicusExpr::Const(1) - signed_lt.clone(),
            signed_lt.clone(),
        )
    } else {
        (
            unsigned_lt.clone(),
            PicusExpr::Const(1) - unsigned_lt.clone(),
            unsigned_lt.clone(),
        )
    };

    module
        .constraints
        .push(PicusConstraint::new_equality(input, reconstructed));

    module
        .constraints
        .push(PicusConstraint::new_bit(should_branch.clone()));
    module
        .constraints
        .push(PicusConstraint::new_bit(should_store.clone()));

    let funct_is =
        |value: u64| PicusConstraint::new_equality(funct3.clone(), PicusExpr::Const(value));

    let branch_expr =
        |value: PicusExpr| PicusConstraint::new_equality(should_branch.clone(), value);
    let store_expr = |value: PicusExpr| PicusConstraint::new_equality(should_store.clone(), value);
    let zero_expr = PicusExpr::Const(0);

    for (value, branch_value, store_value) in [
        (0b000, eq.clone(), zero_expr.clone()),
        (0b001, PicusExpr::Const(1) - eq.clone(), zero_expr.clone()),
        (0b010, zero_expr.clone(), signed_store),
        (0b011, zero_expr.clone(), unsigned_lt.clone()),
        (0b100, signed_lt.clone(), zero_expr.clone()),
        (0b101, not_signed_lt, zero_expr.clone()),
        (0b110, unsigned_lt.clone(), zero_expr.clone()),
        (
            0b111,
            PicusExpr::Const(1) - unsigned_lt.clone(),
            zero_expr.clone(),
        ),
    ] {
        let cond = funct_is(value);
        module.constraints.push(PicusConstraint::Implies(
            Box::new(cond.clone()),
            Box::new(branch_expr(branch_value)),
        ));
        module.constraints.push(PicusConstraint::Implies(
            Box::new(cond),
            Box::new(store_expr(store_value)),
        ));
    }
}

fn add_u16_get_sign_and_high_byte_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
) {
    let input = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let sign = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let high_byte = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);
    let low_byte = fresh_picus_var_expr(next_fresh_var_id);
    let high_byte_low7 = fresh_picus_var_expr(next_fresh_var_id);

    module
        .constraints
        .push(PicusConstraint::new_lt(input.clone(), U16_BOUND.into()));
    module
        .constraints
        .push(PicusConstraint::new_bit(sign.clone()));
    module
        .constraints
        .push(PicusConstraint::new_lt(high_byte.clone(), U8_BOUND.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(low_byte.clone(), U8_BOUND.into()));
    module.constraints.push(PicusConstraint::new_lt(
        high_byte_low7.clone(),
        128u64.into(),
    ));
    module.constraints.push(PicusConstraint::new_equality(
        high_byte.clone(),
        high_byte_low7 + PicusExpr::Const(128) * sign.clone(),
    ));
    module.constraints.push(PicusConstraint::new_equality(
        input,
        low_byte + PicusExpr::Const(256) * high_byte,
    ));
}

/// Translation for `RomAddressSpaceSeparator` lookup.
///
/// Table intent: split a high address limb into `(is_ram_range, rom_chunk)`.
///
/// Extraction strategy: keep explicit decomposition constraints linking
/// `address_high`, `rom_chunk`, and `is_ram_range`.
fn add_rom_address_space_separator_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
) {
    let address_high = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let is_ram_range = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let rom_chunk = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);
    let rom_bound = 1u64 << common_constants::ROM_SECOND_WORD_BITS;
    let q_bound = 1u64 << (16 - common_constants::ROM_SECOND_WORD_BITS);

    let q_tail = fresh_picus_var_expr(next_fresh_var_id);
    let q = fresh_picus_var_expr(next_fresh_var_id);

    module.constraints.push(PicusConstraint::new_lt(
        address_high.clone(),
        U16_BOUND.into(),
    ));
    module
        .constraints
        .push(PicusConstraint::new_bit(is_ram_range.clone()));
    module
        .constraints
        .push(PicusConstraint::new_lt(rom_chunk.clone(), rom_bound.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(q_tail.clone(), q_bound.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(q.clone(), q_bound.into()));

    // Address decomposition by ROM chunk size.
    module.constraints.push(PicusConstraint::new_equality(
        address_high,
        rom_chunk + PicusExpr::Const(rom_bound) * q.clone(),
    ));
    // Link is_ram_range to q != 0 by construction:
    // q = is_ram_range * (q_tail + 1).
    module.constraints.push(PicusConstraint::new_equality(
        q,
        is_ram_range * (q_tail + PicusExpr::Const(1)),
    ));
}

/// Translation for `MemoryLoadHalfwordOrByte` lookup.
///
/// Table intent: compute the `(low, high)` loaded value limbs for subword loads.
///
/// Extraction strategy: summarize with range bounds and determinism
/// `det(input) => (det(out_low) && det(out_high))`.
fn add_memory_load_halfword_or_byte_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    _next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
) {
    let input = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let out_low = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let out_high = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);

    module.constraints.push(PicusConstraint::new_lt(
        input.clone(),
        (1u64 << (16 + 2 + 3)).into(),
    ));
    module
        .constraints
        .push(PicusConstraint::new_lt(out_low.clone(), U16_BOUND.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(out_high.clone(), U16_BOUND.into()));

    let det_input = PicusConstraint::new_det(input);
    let det_out_low = PicusConstraint::new_det(out_low);
    let det_out_high = PicusConstraint::new_det(out_high);
    module.constraints.push(PicusConstraint::Implies(
        Box::new(det_input),
        Box::new(PicusConstraint::And(
            Box::new(det_out_low),
            Box::new(det_out_high),
        )),
    ));
}

/// Translation for `MemStoreClearOriginalRamValueLimb` lookup.
///
/// Table intent: clear the relevant bytes in the original RAM limb before merge.
///
/// Extraction strategy: summarize with range bounds and determinism
/// `det(input) => (det(cleaned) && det(unused))`.
fn add_mem_store_clear_original_ram_value_limb_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    _next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
) {
    let input = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let cleaned = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let unused = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);

    module.constraints.push(PicusConstraint::new_lt(
        input.clone(),
        (1u64 << (16 + 2 + 3)).into(),
    ));
    module
        .constraints
        .push(PicusConstraint::new_lt(cleaned.clone(), U16_BOUND.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(unused.clone(), U16_BOUND.into()));

    // det(input) => (det(cleaned) && det(unused))
    let det_input = PicusConstraint::new_det(input);
    let det_cleaned = PicusConstraint::new_det(cleaned);
    let det_unused = PicusConstraint::new_det(unused);
    module.constraints.push(PicusConstraint::Implies(
        Box::new(det_input),
        Box::new(PicusConstraint::And(
            Box::new(det_cleaned),
            Box::new(det_unused),
        )),
    ));
}

/// Translation for `MemStoreClearWrittenValueLimb` lookup.
///
/// Table intent: normalize/position the written value limb before merging into RAM.
///
/// Extraction strategy: summarize with range bounds and determinism
/// `det(input) => (det(cleaned) && det(unused))`.
fn add_mem_store_clear_written_value_limb_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    _next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
) {
    let input = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let cleaned = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let unused = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);

    module.constraints.push(PicusConstraint::new_lt(
        input.clone(),
        (1u64 << (16 + 2 + 3)).into(),
    ));
    module
        .constraints
        .push(PicusConstraint::new_lt(cleaned.clone(), U16_BOUND.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(unused.clone(), U16_BOUND.into()));

    // det(input) => (det(cleaned) && det(unused))
    let det_input = PicusConstraint::new_det(input);
    let det_cleaned = PicusConstraint::new_det(cleaned);
    let det_unused = PicusConstraint::new_det(unused);
    module.constraints.push(PicusConstraint::Implies(
        Box::new(det_input),
        Box::new(PicusConstraint::And(
            Box::new(det_cleaned),
            Box::new(det_unused),
        )),
    ));
}

/// Translation for `AlignedRomRead` lookup.
///
/// Table intent: map ROM word index to low/high 16-bit instruction limbs.
///
/// Extraction strategy: bound index/output ranges and enforce determinism
/// `det(word_index) => (det(low) && det(high))`.
fn add_aligned_rom_read_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    row_multiplier: Option<&PicusExpr>,
) {
    let word_index = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let low = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let high = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);

    // Aligned ROM table is keyed by word index in [0, 2^(16 + ROM_SECOND_WORD_BITS - 2)).
    let max_word_index = 1u64 << (16 + common_constants::ROM_SECOND_WORD_BITS - 2);
    module.constraints.push(PicusConstraint::new_lt(
        word_index.clone(),
        max_word_index.into(),
    ));
    module
        .constraints
        .push(PicusConstraint::new_lt(low.clone(), U16_BOUND.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(high.clone(), U16_BOUND.into()));

    // det(word_index) => (det(low) && det(high))
    let det_word_index = PicusConstraint::new_det(word_index);
    let det_low = PicusConstraint::new_det(low);
    let det_high = PicusConstraint::new_det(high);
    module.constraints.push(PicusConstraint::Implies(
        Box::new(det_word_index),
        Box::new(PicusConstraint::And(Box::new(det_low), Box::new(det_high))),
    ));

    // NOTE: exact (word_index -> low/high) value linkage still requires
    // embedding the concrete ROM table contents.
}

/// Translation for `TruncateShiftAmount` lookup.
///
/// Table intent: truncate a 16-bit value to a 5-bit shift amount.
///
/// Extraction strategy: bound input/outputs and enforce
/// `det(input) => (det(shift_amount) && det(padded))`.
fn add_truncate_shift_amount_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
) {
    let input = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let shift_amount = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let padded = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);

    module
        .constraints
        .push(PicusConstraint::new_lt(input.clone(), U16_BOUND.into()));
    module.constraints.push(PicusConstraint::new_lt(
        shift_amount.clone(),
        PicusExpr::Const(1u64 << 5),
    ));
    module
        .constraints
        .push(PicusConstraint::new_lt(padded.clone(), U16_BOUND.into()));

    if row_multiplier.is_some() {
        let det_input = PicusConstraint::new_det(input);
        let det_shift = PicusConstraint::new_det(shift_amount);
        let det_padded = PicusConstraint::new_det(padded);
        module.constraints.push(PicusConstraint::Implies(
            Box::new(det_input),
            Box::new(PicusConstraint::And(
                Box::new(det_shift),
                Box::new(det_padded),
            )),
        ));
        return;
    }

    let quotient = fresh_picus_var_expr(next_fresh_var_id);
    module.constraints.push(PicusConstraint::new_lt(
        quotient.clone(),
        (1u64 << 11).into(),
    ));
    module
        .constraints
        .push(PicusConstraint::new_equality(padded, PicusExpr::Const(0)));
    module.constraints.push(PicusConstraint::new_equality(
        input,
        PicusExpr::Const(32) * quotient + shift_amount,
    ));
}

/// Translation for logical/arithmetic 16-bit shift lookup families (`Sll*`, `Srl*`, `Sra*`).
///
/// Table intent: map packed `(word16, shift5)` input into two 16-bit result limbs.
///
/// Extraction strategy: bound packed input/result limbs and enforce
/// `det(input) => (det(out_low) && det(out_high))`.
fn add_shift_16bit_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
) {
    let input = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let out_low = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let out_high = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);

    module.constraints.push(PicusConstraint::new_lt(
        input.clone(),
        PicusExpr::Const(1u64 << (16 + 5)),
    ));
    module
        .constraints
        .push(PicusConstraint::new_lt(out_low.clone(), U16_BOUND.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(out_high.clone(), U16_BOUND.into()));

    if row_multiplier.is_some() {
        let det_input = PicusConstraint::new_det(input);
        let det_out_low = PicusConstraint::new_det(out_low);
        let det_out_high = PicusConstraint::new_det(out_high);
        module.constraints.push(PicusConstraint::Implies(
            Box::new(det_input),
            Box::new(PicusConstraint::And(
                Box::new(det_out_low),
                Box::new(det_out_high),
            )),
        ));
        return;
    }

    let word = fresh_picus_var_expr(next_fresh_var_id);
    let shift = fresh_picus_var_expr(next_fresh_var_id);
    let is_right = fresh_picus_var_expr(next_fresh_var_id);
    let result_word = PicusExpr::Const(U16_BOUND) * out_low.clone() + out_high.clone();
    let shift_bits = add_one_hot_bits(module, 32, next_fresh_var_id);
    let shift_reconstructed = shift_bits
        .iter()
        .enumerate()
        .fold(PicusExpr::Const(0), |acc, (k, bit)| {
            acc + PicusExpr::Const(k as u64) * bit.clone()
        });
    let pow2 = shift_bits
        .iter()
        .enumerate()
        .fold(PicusExpr::Const(0), |acc, (k, bit)| {
            acc + PicusExpr::Const(1u64 << k) * bit.clone()
        });

    module
        .constraints
        .push(PicusConstraint::new_lt(word.clone(), U16_BOUND.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(shift.clone(), (1u64 << 5).into()));
    module
        .constraints
        .push(PicusConstraint::new_bit(is_right.clone()));
    module.constraints.push(PicusConstraint::new_equality(
        input,
        word.clone()
            + PicusExpr::Const(U16_BOUND) * shift.clone()
            + PicusExpr::Const(1u64 << 21) * is_right.clone(),
    ));
    module
        .constraints
        .push(PicusConstraint::new_equality(shift, shift_reconstructed));

    let left_guard = PicusConstraint::new_equality(is_right.clone(), PicusExpr::Const(0));
    let left_relation =
        PicusConstraint::new_equality(word.clone() * pow2.clone(), result_word.clone());
    module.constraints.push(PicusConstraint::Implies(
        Box::new(left_guard),
        Box::new(left_relation),
    ));

    let mut masked_remainder = PicusExpr::Const(0);
    for (k, bit) in shift_bits.iter().enumerate() {
        let remainder_k = fresh_picus_var_expr(next_fresh_var_id);
        module.constraints.push(PicusConstraint::new_lt(
            remainder_k.clone(),
            PicusExpr::Const(1u64 << k),
        ));
        masked_remainder = masked_remainder + remainder_k * bit.clone();
    }

    let right_guard = PicusConstraint::new_equality(is_right, PicusExpr::Const(1));
    let right_relation = PicusConstraint::new_equality(
        PicusExpr::Const(U16_BOUND) * word,
        result_word * pow2 + masked_remainder,
    );
    module.constraints.push(PicusConstraint::Implies(
        Box::new(right_guard),
        Box::new(right_relation),
    ));
}

/// Translation for byte-wise bitwise lookup families (`Xor`, `And`, `Or`).
///
/// Table intent: map two 8-bit inputs to a single 8-bit bitwise result.
///
/// Extraction strategy: bound inputs/output and enforce
/// `(det(in1) && det(in2)) => det(out)`.
fn add_bitop_byte_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    _next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
) {
    let in1 = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let in2 = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let out = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);

    module
        .constraints
        .push(PicusConstraint::new_lt(in1.clone(), U8_BOUND.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(in2.clone(), U8_BOUND.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(out.clone(), U8_BOUND.into()));

    let det_in1 = PicusConstraint::new_det(in1);
    let det_in2 = PicusConstraint::new_det(in2);
    let det_out = PicusConstraint::new_det(out);
    module.constraints.push(PicusConstraint::Implies(
        Box::new(PicusConstraint::And(Box::new(det_in1), Box::new(det_in2))),
        Box::new(det_out),
    ));
}

fn add_xor_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    _next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
    width: usize,
) {
    let in1 = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let in2 = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let out = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);
    let bound = 1u64 << width;

    module
        .constraints
        .push(PicusConstraint::new_lt(in1.clone(), bound.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(in2.clone(), bound.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(out.clone(), bound.into()));

    let det_in1 = PicusConstraint::new_det(in1);
    let det_in2 = PicusConstraint::new_det(in2);
    let det_out = PicusConstraint::new_det(out);
    module.constraints.push(PicusConstraint::Implies(
        Box::new(PicusConstraint::And(Box::new(det_in1), Box::new(det_in2))),
        Box::new(det_out),
    ));
}

/// Translation for `RangeCheck16WithZeroPads` lookup.
///
/// Table intent: enforce `(a, 0, 0)` with `a < 2^16`.
fn add_range_check_16_with_zero_pads_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    _next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
) {
    let input = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let pad_1 = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let pad_2 = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);

    module
        .constraints
        .push(PicusConstraint::new_lt(input, U16_BOUND.into()));
    module
        .constraints
        .push(PicusConstraint::new_equality(pad_1, PicusExpr::Const(0)));
    module
        .constraints
        .push(PicusConstraint::new_equality(pad_2, PicusExpr::Const(0)));
}

/// Translation for `QuickDecodeDecompositionCheck4x4x4`.
///
/// Table intent: certify that the three tuple entries are independent 4-bit limbs.
fn add_quick_decode_decomposition_4x4x4_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    _next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
) {
    let a = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let b = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let c = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);

    module
        .constraints
        .push(PicusConstraint::new_lt(a, U4_BOUND.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(b, U4_BOUND.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(c, U4_BOUND.into()));
}

/// Translation for `QuickDecodeDecompositionCheck7x3x6`.
///
/// Table intent: certify `(opcode, funct3, imm10_5)` chunk widths during decode.
fn add_quick_decode_decomposition_7x3x6_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    _next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
) {
    let a = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let b = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let c = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);

    module
        .constraints
        .push(PicusConstraint::new_lt(a, 128u64.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(b, 8u64.into()));
    module
        .constraints
        .push(PicusConstraint::new_lt(c, 64u64.into()));
}

/// Translation for `OpTypeBitmask`.
///
/// Table intent: map `(opcode, funct3, funct7)` into the decoder bitmask chunks.
///
/// Extraction strategy: keep a coarse summary. The lookup output is deterministic
/// for a fixed packed opcode key, and the bitmask chunks are consumed elsewhere
/// through explicit boolean decompositions in the circuit.
fn add_op_type_bitmask_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    _next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
) {
    let packed_opcode = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let first_chunk = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let second_chunk = lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);

    module.constraints.push(PicusConstraint::new_lt(
        packed_opcode.clone(),
        (1u64 << 17).into(),
    ));
    module.constraints.push(PicusConstraint::new_lt(
        first_chunk.clone(),
        PICUS_CHUNK_BOUND.into(),
    ));
    module.constraints.push(PicusConstraint::new_lt(
        second_chunk.clone(),
        PICUS_CHUNK_BOUND.into(),
    ));

    let det_input = PicusConstraint::new_det(packed_opcode);
    let det_first = PicusConstraint::new_det(first_chunk.clone());
    let det_second = PicusConstraint::new_det(second_chunk.clone());
    module.constraints.push(PicusConstraint::Implies(
        Box::new(det_input),
        Box::new(PicusConstraint::And(
            Box::new(det_first),
            Box::new(det_second),
        )),
    ));
}

/// Translation for `SpecialCSRProperties` lookup.
///
/// Table intent: map `csr_index` to `(is_supported, is_allowed_for_delegation)`.
fn add_special_csr_properties_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    _next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
) {
    let csr_index = lookup_input_to_picus_expr_with_multiplier(&query.row[0], row_multiplier);
    let is_supported = lookup_input_to_picus_expr_with_multiplier(&query.row[1], row_multiplier);
    let is_allowed_for_delegation =
        lookup_input_to_picus_expr_with_multiplier(&query.row[2], row_multiplier);

    module
        .constraints
        .push(PicusConstraint::new_lt(csr_index.clone(), U12_BOUND.into()));
    module
        .constraints
        .push(PicusConstraint::new_bit(is_supported.clone()));
    module
        .constraints
        .push(PicusConstraint::new_bit(is_allowed_for_delegation.clone()));
    module.constraints.push(PicusConstraint::new_leq(
        is_allowed_for_delegation.clone(),
        is_supported.clone(),
    ));

    let det_index = PicusConstraint::new_det(csr_index);
    let det_supported = PicusConstraint::new_det(is_supported);
    let det_allowed = PicusConstraint::new_det(is_allowed_for_delegation);
    module.constraints.push(PicusConstraint::Implies(
        Box::new(det_index),
        Box::new(PicusConstraint::And(
            Box::new(det_supported),
            Box::new(det_allowed),
        )),
    ));
}

/// Converts a lookup input into a Picus expression and optionally scales it by a
/// row multiplier (used for flag-multiplied disjunctive encodings).
fn lookup_input_to_picus_expr_with_multiplier<F: PrimeField>(
    input: &cs::definitions::LookupInput<F>,
    row_multiplier: Option<&PicusExpr>,
) -> PicusExpr {
    let expr = lookup_input_to_picus_expr(input);
    if let Some(multiplier) = row_multiplier {
        multiplier.clone() * expr
    } else {
        expr
    }
}

/// Converts circuit boolean flavor (`Is`, `Not`, `Constant`) into a Picus expression.
fn boolean_to_picus_expr(flag: Boolean) -> PicusExpr {
    match flag {
        Boolean::Is(v) => variable_to_picus_expr(v),
        Boolean::Not(v) => PicusExpr::Const(1) - variable_to_picus_expr(v),
        Boolean::Constant(c) => PicusExpr::Const(c as u64),
    }
}

/// Returns true when row-multiplication by an activation flag is safe for the table.
///
/// Safety criterion here is that the multiplied inactive row still corresponds to a
/// valid table behavior for the summarization strategy.
fn table_supports_zero_row_multiply_in(table: TableType) -> bool {
    matches!(
        table,
        TableType::MemoryLoadHalfwordOrByte | TableType::MemStoreClearOriginalRamValueLimb
    )
}

/// Dispatches one constant-table lookup query to its table-specific translator.
///
/// `row_multiplier` is used for the "multiply-in" disjunctive variant when enabled.
fn add_lookup_constraints_for_table<F: PrimeField>(
    module: &mut PicusModule,
    query: &LookupQuery<F>,
    table: TableType,
    next_fresh_var_id: &mut usize,
    row_multiplier: Option<&PicusExpr>,
) {
    match table {
        TableType::ConditionalJmpBranchSlt => {
            add_conditional_jmp_branch_slt_lookup_constraints(
                module,
                query,
                next_fresh_var_id,
                row_multiplier,
            );
        }
        TableType::ConditionalOpAllConditionsResolver => {
            add_conditional_op_resolution_lookup_constraints(
                module,
                query,
                next_fresh_var_id,
                row_multiplier,
                true,
            );
        }
        TableType::ConditionalOpUnsignedConditionsResolver => {
            add_conditional_op_resolution_lookup_constraints(
                module,
                query,
                next_fresh_var_id,
                row_multiplier,
                false,
            );
        }
        TableType::U16GetSignAndHighByte => {
            add_u16_get_sign_and_high_byte_lookup_constraints(
                module,
                query,
                next_fresh_var_id,
                row_multiplier,
            );
        }
        TableType::JumpCleanupOffset => {
            add_jump_cleanup_lookup_constraints(module, query, next_fresh_var_id, row_multiplier);
        }
        TableType::MemoryGetOffsetAndMaskWithTrap => {
            add_memory_get_offset_and_mask_with_trap_lookup_constraints(
                module,
                query,
                next_fresh_var_id,
                row_multiplier,
            );
        }
        TableType::RomAddressSpaceSeparator => {
            add_rom_address_space_separator_lookup_constraints(
                module,
                query,
                next_fresh_var_id,
                row_multiplier,
            );
        }
        TableType::MemoryLoadHalfwordOrByte => {
            add_memory_load_halfword_or_byte_lookup_constraints(
                module,
                query,
                next_fresh_var_id,
                row_multiplier,
            );
        }
        TableType::MemStoreClearOriginalRamValueLimb => {
            add_mem_store_clear_original_ram_value_limb_lookup_constraints(
                module,
                query,
                next_fresh_var_id,
                row_multiplier,
            );
        }
        TableType::MemStoreClearWrittenValueLimb => {
            add_mem_store_clear_written_value_limb_lookup_constraints(
                module,
                query,
                next_fresh_var_id,
                row_multiplier,
            );
        }
        TableType::TruncateShiftAmount => {
            add_truncate_shift_amount_lookup_constraints(
                module,
                query,
                next_fresh_var_id,
                row_multiplier,
            );
        }
        TableType::ShiftImplementation
        | TableType::SllWith16BitInputLow
        | TableType::SllWith16BitInputHigh
        | TableType::SrlWith16BitInputLow
        | TableType::SrlWith16BitInputHigh
        | TableType::Sra16BitInputSignFill => {
            add_shift_16bit_lookup_constraints(module, query, next_fresh_var_id, row_multiplier);
        }
        TableType::Xor => {
            add_xor_lookup_constraints(module, query, next_fresh_var_id, row_multiplier, 8);
        }
        TableType::Xor3 => {
            add_xor_lookup_constraints(module, query, next_fresh_var_id, row_multiplier, 3);
        }
        TableType::Xor4 => {
            add_xor_lookup_constraints(module, query, next_fresh_var_id, row_multiplier, 4);
        }
        TableType::Xor7 => {
            add_xor_lookup_constraints(module, query, next_fresh_var_id, row_multiplier, 7);
        }
        TableType::Xor9 => {
            add_xor_lookup_constraints(module, query, next_fresh_var_id, row_multiplier, 9);
        }
        TableType::And | TableType::Or => {
            add_bitop_byte_lookup_constraints(module, query, next_fresh_var_id, row_multiplier);
        }
        TableType::RangeCheck16WithZeroPads => {
            add_range_check_16_with_zero_pads_lookup_constraints(
                module,
                query,
                next_fresh_var_id,
                row_multiplier,
            );
        }
        TableType::QuickDecodeDecompositionCheck4x4x4 => {
            add_quick_decode_decomposition_4x4x4_lookup_constraints(
                module,
                query,
                next_fresh_var_id,
                row_multiplier,
            );
        }
        TableType::QuickDecodeDecompositionCheck7x3x6 => {
            add_quick_decode_decomposition_7x3x6_lookup_constraints(
                module,
                query,
                next_fresh_var_id,
                row_multiplier,
            );
        }
        TableType::OpTypeBitmask => {
            add_op_type_bitmask_lookup_constraints(
                module,
                query,
                next_fresh_var_id,
                row_multiplier,
            );
        }
        TableType::SpecialCSRProperties => {
            add_special_csr_properties_lookup_constraints(
                module,
                query,
                next_fresh_var_id,
                row_multiplier,
            );
        }
        TableType::AlignedRomRead => {
            add_aligned_rom_read_lookup_constraints(module, query, row_multiplier);
        }
        _ => {}
    }
}

/// Adds translated constraints for regular (non-disjunctive) constant-table lookups.
pub(super) fn add_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    lookups: &[LookupQuery<F>],
    next_fresh_var_id: &mut usize,
) {
    for query in lookups {
        let LookupQueryTableType::Constant(table) = query.table else {
            continue;
        };

        add_lookup_constraints_for_table(module, query, table, next_fresh_var_id, None);
    }
}

/// Adds translated constraints for disjunctive lookup metadata emitted by optimization context.
///
/// For each disjunctive relation this function:
/// - adds postconditions that flags are boolean and satisfy `sum(flags) <= 1`,
/// - dispatches each case through the same table translator,
/// - either multiplies row expressions by flag for safe tables or guards case constraints under
///   `(flag = 1) => ...`.
pub(super) fn add_disjunctive_lookup_constraints<F: PrimeField>(
    module: &mut PicusModule,
    disjunctive_lookups: &[DisjunctiveLookup<F>],
    next_fresh_var_id: &mut usize,
) {
    fn guard_to_picus_condition<F: PrimeField>(
        guard: &DisjunctiveLookupGuard<F>,
    ) -> PicusConstraint {
        match guard {
            DisjunctiveLookupGuard::EqConst { var, value } => PicusConstraint::new_equality(
                variable_to_picus_expr(*var),
                PicusExpr::Const(value.as_u64_reduced()),
            ),
            DisjunctiveLookupGuard::And(guards) => {
                let mut iter = guards.iter();
                let first = iter
                    .next()
                    .map(guard_to_picus_condition)
                    .unwrap_or_else(|| {
                        PicusConstraint::new_equality(PicusExpr::Const(0), PicusExpr::Const(0))
                    });
                iter.fold(first, |acc, el| {
                    PicusConstraint::And(Box::new(acc), Box::new(guard_to_picus_condition(el)))
                })
            }
        }
    }

    fn and_conditions(lhs: PicusConstraint, rhs: PicusConstraint) -> PicusConstraint {
        PicusConstraint::And(Box::new(lhs), Box::new(rhs))
    }

    for relation in disjunctive_lookups {
        let mut unique_case_flags: Vec<Boolean> = Vec::new();
        for case in &relation.cases {
            if unique_case_flags.contains(&case.flag) == false {
                unique_case_flags.push(case.flag);
            }
        }
        let flags: Vec<PicusExpr> = unique_case_flags
            .iter()
            .map(|flag| boolean_to_picus_expr(*flag))
            .collect();

        for flag in &flags {
            module
                .constraints
                .push(PicusConstraint::new_bit(flag.clone()));
        }
        let flag_sum = flags
            .iter()
            .cloned()
            .fold(PicusExpr::Const(0), |acc, f| acc + f);
        module
            .constraints
            .push(PicusConstraint::new_leq(flag_sum, PicusExpr::Const(1)));

        for case in &relation.cases {
            let Num::Constant(table_id) = case.table else {
                continue;
            };
            let table = TableType::get_table_from_id(table_id.as_u64_reduced() as u32);
            let query = LookupQuery {
                row: case.row.clone(),
                table: LookupQueryTableType::Constant(table),
            };
            let flag_expr = boolean_to_picus_expr(case.flag);
            let base_cond = PicusConstraint::new_equality(flag_expr.clone(), PicusExpr::Const(1));
            let case_cond = if let Some(guard) = &case.guard {
                and_conditions(base_cond, guard_to_picus_condition(guard))
            } else {
                base_cond
            };

            if case.guard.is_none() && table_supports_zero_row_multiply_in(table) {
                add_lookup_constraints_for_table(
                    module,
                    &query,
                    table,
                    next_fresh_var_id,
                    Some(&flag_expr),
                );
            } else {
                let base = module.constraints.len();
                add_lookup_constraints_for_table(module, &query, table, next_fresh_var_id, None);
                let added = module.constraints.split_off(base);
                for c in added {
                    module.constraints.push(PicusConstraint::Implies(
                        Box::new(case_cond.clone()),
                        Box::new(c),
                    ));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cs::cs::circuit::LookupQuery;
    use cs::cs::circuit::LookupQueryTableType;
    use cs::definitions::LookupInput;
    use cs::machine::machine_configurations::create_csr_table_for_delegation;
    use cs::machine::machine_configurations::full_isa_no_exceptions::FullIsaMachineNoExceptionHandling;
    use cs::machine::Machine;
    use cs::tables::LookupWrapper;
    use field::Field;
    use field::Mersenne31Field;
    use picus::partial_evaluate;
    use picus::PicusConstraint;
    use picus::PicusExpr;
    use std::collections::BTreeMap;

    fn variable_query(table: TableType) -> LookupQuery<Mersenne31Field> {
        LookupQuery {
            row: [
                LookupInput::Variable(Variable(0)),
                LookupInput::Variable(Variable(1)),
                LookupInput::Variable(Variable(2)),
            ],
            table: LookupQueryTableType::Constant(table),
        }
    }

    fn emitted_lookup_constraints(table: TableType) -> Vec<PicusConstraint> {
        let mut module = PicusModule::new(format!("isolated_lookup_{table:?}"));
        let query = variable_query(table);
        let mut next_fresh_var_id = 3;
        add_lookup_constraints_for_table(&mut module, &query, table, &mut next_fresh_var_id, None);
        module.constraints
    }

    fn reconstructed_witness_env(
        table: TableType,
        row: &[Mersenne31Field],
    ) -> Option<BTreeMap<usize, u64>> {
        let input = row[0].as_u64_reduced();
        let out1 = row[1].as_u64_reduced();
        let out2 = row[2].as_u64_reduced();

        let env = match table {
            TableType::JumpCleanupOffset => {
                let bit_0 = input & 1;
                let k = out2 / 4;
                BTreeMap::from([(3usize, bit_0), (4usize, k)])
            }
            TableType::U16GetSignAndHighByte => {
                let low_byte = input & 0xff;
                let high_byte_low7 = out2 & 0x7f;
                BTreeMap::from([(3usize, low_byte), (4usize, high_byte_low7)])
            }
            TableType::TruncateShiftAmount => {
                let quotient = input >> 5;
                BTreeMap::from([(3usize, quotient)])
            }
            TableType::ConditionalOpUnsignedConditionsResolver => {
                let funct3 = input & 0x7;
                let unsigned_lt = (input >> 3) & 1;
                let eq = (input >> 4) & 1;
                BTreeMap::from([(3usize, funct3), (4usize, unsigned_lt), (5usize, eq)])
            }
            TableType::ConditionalOpAllConditionsResolver => {
                let funct3 = input & 0x7;
                let unsigned_lt = (input >> 3) & 1;
                let eq = (input >> 4) & 1;
                let src1_sign = (input >> 5) & 1;
                let src2_sign = (input >> 6) & 1;
                let diff_signs = src1_sign ^ src2_sign;
                let signed_lt = if diff_signs == 1 {
                    src1_sign
                } else {
                    unsigned_lt
                };
                BTreeMap::from([
                    (3usize, funct3),
                    (4usize, unsigned_lt),
                    (5usize, eq),
                    (6usize, src1_sign),
                    (7usize, src2_sign),
                    (8usize, diff_signs),
                    (9usize, signed_lt),
                ])
            }
            TableType::ConditionalJmpBranchSlt => {
                let uf = input & 1;
                let out_is_zero = (input >> 1) & 1;
                let sign1 = (input >> 2) & 1;
                let sign2 = (input >> 3) & 1;
                let funct3 = out1;
                let mut env = BTreeMap::from([
                    (3usize, uf),
                    (4usize, out_is_zero),
                    (5usize, sign1),
                    (6usize, sign2),
                ]);
                for idx in 0..8usize {
                    env.insert(7 + idx, u64::from(idx as u64 == funct3));
                }
                env
            }
            _ => return None,
        };

        debug_assert_eq!(out1, row[1].as_u64_reduced());
        debug_assert_eq!(out2, row[2].as_u64_reduced());
        Some(env)
    }

    fn eval_expr(expr: &PicusExpr) -> u64 {
        const MODULUS: u64 = 2_147_483_647;
        match expr {
            PicusExpr::Const(c) => c % MODULUS,
            PicusExpr::Var(v) => panic!("unsubstituted variable in test evaluation: {v}"),
            PicusExpr::Add(a, b) => (eval_expr(a) + eval_expr(b)) % MODULUS,
            PicusExpr::Sub(a, b) => (MODULUS + eval_expr(a) - eval_expr(b)) % MODULUS,
            PicusExpr::Mul(a, b) => {
                ((eval_expr(a) as u128 * eval_expr(b) as u128) % MODULUS as u128) as u64
            }
            PicusExpr::Div(a, b) => {
                let numerator = eval_expr(a);
                let denominator = eval_expr(b);
                assert_ne!(denominator, 0, "division by zero in Picus test evaluation");
                let inv = Mersenne31Field::from_u64_unchecked(denominator)
                    .inverse()
                    .unwrap();
                ((numerator as u128 * inv.as_u64_reduced() as u128) % MODULUS as u128) as u64
            }
            PicusExpr::Neg(a) => (MODULUS - eval_expr(a)) % MODULUS,
            PicusExpr::Pow(k, a) => {
                let mut acc = 1u64;
                let mut base = eval_expr(a);
                let mut exp = *k;
                while exp > 0 {
                    if exp & 1 == 1 {
                        acc = ((acc as u128 * base as u128) % MODULUS as u128) as u64;
                    }
                    base = ((base as u128 * base as u128) % MODULUS as u128) as u64;
                    exp >>= 1;
                }
                acc
            }
        }
    }

    fn eval_constraint(constraint: &PicusConstraint) -> bool {
        match constraint {
            PicusConstraint::Lt(a, b) => eval_expr(a) < eval_expr(b),
            PicusConstraint::Leq(a, b) => eval_expr(a) <= eval_expr(b),
            PicusConstraint::Gt(a, b) => eval_expr(a) > eval_expr(b),
            PicusConstraint::Geq(a, b) => eval_expr(a) >= eval_expr(b),
            PicusConstraint::Implies(a, b) => !eval_constraint(a) || eval_constraint(b),
            PicusConstraint::Not(a) => !eval_constraint(a),
            PicusConstraint::Iff(a, b) => eval_constraint(a) == eval_constraint(b),
            PicusConstraint::And(a, b) => eval_constraint(a) && eval_constraint(b),
            PicusConstraint::Or(a, b) => eval_constraint(a) || eval_constraint(b),
            PicusConstraint::Det(expr) => matches!(expr.as_ref(), PicusExpr::Const(_)),
            PicusConstraint::Eq(expr) => eval_expr(expr) == 0,
        }
    }

    fn lookup_table_rows(table: TableType) -> LookupWrapper<Mersenne31Field> {
        match table {
            TableType::OpTypeBitmask => {
                LookupWrapper::Dimensional3(<FullIsaMachineNoExceptionHandling as Machine<
                    Mersenne31Field,
                >>::create_decoder_table(
                    TableType::OpTypeBitmask.to_table_id()
                ))
            }
            TableType::SpecialCSRProperties => {
                LookupWrapper::Dimensional3(create_csr_table_for_delegation::<Mersenne31Field>(
                    true,
                    &[],
                    TableType::SpecialCSRProperties.to_table_id(),
                ))
            }
            _ => table.generate_table::<Mersenne31Field>(),
        }
    }

    fn assert_emitted_constraints_accept_all_rows(table: TableType) {
        let constraints = emitted_lookup_constraints(table);
        let table_rows = lookup_table_rows(table);

        for row_idx in 0..table_rows.get_size() {
            let row = table_rows.data_at_row(row_idx);
            let (holds, reduced) = emitted_constraints_hold_for_row(table, &constraints, row);
            assert!(
                holds,
                "lookup {:?} rejected row {} = {:?}: {:?}",
                table,
                row_idx,
                &row[..3],
                reduced
            );
        }
    }

    fn emitted_constraints_hold_for_row(
        table: TableType,
        constraints: &[PicusConstraint],
        row: &[Mersenne31Field],
    ) -> (bool, Vec<PicusConstraint>) {
        let mut env = BTreeMap::from([
            (0usize, row[0].as_u64_reduced()),
            (1usize, row[1].as_u64_reduced()),
            (2usize, row[2].as_u64_reduced()),
        ]);
        if let Some(witness_env) = reconstructed_witness_env(table, row) {
            env.extend(witness_env);
        }
        let reduced = partial_evaluate(constraints, &env);
        let holds = reduced.iter().all(eval_constraint);
        (holds, reduced)
    }

    #[test]
    fn emitted_constraints_accept_all_rows_of_summary_tables() {
        for table in [
            TableType::And,
            TableType::Or,
            TableType::Xor,
            TableType::Xor3,
            TableType::Xor4,
            TableType::Xor7,
            TableType::Xor9,
            TableType::RangeCheck16WithZeroPads,
            TableType::QuickDecodeDecompositionCheck4x4x4,
            TableType::QuickDecodeDecompositionCheck7x3x6,
            TableType::OpTypeBitmask,
            TableType::SpecialCSRProperties,
            TableType::MemoryGetOffsetAndMaskWithTrap,
            TableType::MemoryLoadHalfwordOrByte,
            TableType::MemStoreClearOriginalRamValueLimb,
            TableType::MemStoreClearWrittenValueLimb,
        ] {
            assert_emitted_constraints_accept_all_rows(table);
        }
    }

    #[test]
    fn emitted_constraints_accept_all_rows_with_basic_witness_reconstruction() {
        for table in [
            TableType::JumpCleanupOffset,
            TableType::U16GetSignAndHighByte,
            TableType::TruncateShiftAmount,
            TableType::ConditionalJmpBranchSlt,
        ] {
            assert_emitted_constraints_accept_all_rows(table);
        }
    }

    #[test]
    fn conditional_op_all_conditions_resolver_summary_has_real_counterexample() {
        let constraints = emitted_lookup_constraints(TableType::ConditionalOpAllConditionsResolver);
        let row = [
            Mersenne31Field::from_u64_unchecked(42),
            Mersenne31Field::ZERO,
            Mersenne31Field::ZERO,
        ];
        let (holds, reduced) = emitted_constraints_hold_for_row(
            TableType::ConditionalOpAllConditionsResolver,
            &constraints,
            &row,
        );
        assert!(
            !holds,
            "expected ConditionalOpAllConditionsResolver row 42 to violate the emitted summary"
        );
        assert!(
            reduced
                .iter()
                .any(|constraint| !eval_constraint(constraint)),
            "expected a failing reduced constraint for ConditionalOpAllConditionsResolver row 42"
        );
    }
}
