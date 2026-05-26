use super::decoder::DivMulDecoder;
use super::*;
use crate::cs::circuit_trait::*;
use crate::oracle::Placeholder;
use crate::structured_expr::Expr;
use crate::tables::TableDriver;
use crate::types::*;
use crate::witness_placer::*;
use field::PrimeField;

const TABLES_TOTAL_WIDTH: usize = 8;

// NOTE: this circuit should specify non-dummy CSR table in proving/setup. while compilation in tests
// takes case of properly computing offsets by using dummy table

pub fn mul_div_tables<const SUPPORT_SIGNED: bool>() -> Vec<TableType> {
    vec![
        TableType::U16GetLowByte,
        TableType::RegIsZero,
        TableType::RangeCheck8x8,
        TableType::RangeCheck13,
    ]
}

pub fn mul_div_table_addition_fn<F: PrimeField, CS: Circuit<F>, const SUPPORT_SIGNED: bool>(
    cs: &mut CS,
) {
    for el in mul_div_tables::<SUPPORT_SIGNED>() {
        cs.materialize_table::<TABLES_TOTAL_WIDTH>(el);
    }
}

pub fn mul_div_table_driver_fn<F: PrimeField, const SUPPORT_SIGNED: bool>(
    table_driver: &mut TableDriver<F>,
) {
    for el in mul_div_tables::<SUPPORT_SIGNED>() {
        table_driver.materialize_table::<TABLES_TOTAL_WIDTH>(el);
    }
}

fn apply_mul_div_inner<F: PrimeField, CS: Circuit<F>, const SUPPORT_SIGNED: bool>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
    decoder: <DivMulDecoder<SUPPORT_SIGNED> as OpcodeFamilyDecoder>::BitmaskCircuitParser,
) {
    // TODO: skip IMM from decoder completely

    if let Some(circuit_family_extra_mask) =
        cs.get_value(inputs.decoder_data.circuit_family_extra_mask)
    {
        println!(
            "circuit_family_extra_mask = 0b{:08b}",
            circuit_family_extra_mask.as_u32_reduced()
        );
    }

    // read inputs and prepare outputs
    let rs1_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterRead {
            reg_idx: inputs.decoder_data.rs1_index,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(0),
            split_as_u8: false,
        },
        "rs1",
        0,
    );

    let rs2_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterRead {
            reg_idx: inputs.decoder_data.rs2_index,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(1),
            split_as_u8: false,
        },
        "rs2",
        1,
    );

    let rd_access = cs.request_mem_access(
        MemoryAccessRequest::RegisterReadWrite {
            reg_idx: inputs.decoder_data.rd_index,
            read_value_placeholder: Placeholder::ShuffleRamReadValue(2),
            write_value_placeholder: Placeholder::ShuffleRamWriteValue(2),
            split_read_as_u8: false,
            split_write_as_u8: false,
        },
        "rd",
        2,
    );

    let MemoryAccess::RegisterOnly(rs1_access) = rs1_access else {
        unreachable!()
    };
    let MemoryAccess::RegisterOnly(rs2_access) = rs2_access else {
        unreachable!()
    };
    let MemoryAccess::RegisterOnly(rd_access) = rd_access else {
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

    let shift_left_16_bits = F::from_u32_with_reduction(1 << 16);
    let shift_left_8_bits = F::from_u32_with_reduction(1 << 8);
    let shift_right_8_bits = F::from_u32_with_reduction(1 << 8).inverse().unwrap();

    // we need range checks on the output to ensure proper addition
    let [out_low, out_high] = rd_write_limbs;
    cs.require_invariant(out_low, Invariant::RangeChecked { width: 16 });
    cs.require_invariant(out_high, Invariant::RangeChecked { width: 16 });

    if let Some(rs1_reg) = Register(rs1_limbs.map(|el| Num::Var(el))).get_value_unsigned(cs) {
        println!("RS1 value = 0x{:08x}", rs1_reg);
    }

    if let Some(rs2_reg) = Register(rs2_limbs.map(|el| Num::Var(el))).get_value_unsigned(cs) {
        println!("RS2 value = 0x{:08x}", rs2_reg);
    }

    if SUPPORT_SIGNED == false {
        let is_mul = decoder.is_mul();
        let is_mulhu = decoder.is_mulhu();
        let is_divu = decoder.is_divu();
        let is_remu = decoder.is_remu();

        // as usual we enforce division via witness and multiplication,
        // and should analyze exceptional cases. For unsigned ops only there is just divu/remu
        // with divisor being 0
        // - for DIVU quotient is u32::MAX
        // - for REMU remainder is dividend

        // it works well in our multiplication enforcement case: we enforce dividend = q * divisor + remainder,
        // and can set quotient witness to u32::MAX and remainder to dividend

        // for all other cases we check that remainder < divisor

        // we do not need any sign information, but we still need to break everything into u8 chunks (do via lookup that outputs exact lowest 8 bits),
        // and test if divisor is 0 (via lookup of the sum of limbs)

        if is_mul.get_value(cs).unwrap_or(false) {
            println!("MUL");
        }
        if is_mulhu.get_value(cs).unwrap_or(false) {
            println!("MULHU");
        }
        if is_divu.get_value(cs).unwrap_or(false) {
            println!("DIVU");
        }
        if is_remu.get_value(cs).unwrap_or(false) {
            println!("REMU");
        }

        let is_mul_expr = Expr::<F>::from(is_mul);
        let is_mulhu_expr = Expr::<F>::from(is_mulhu);
        let is_divu_expr = Expr::<F>::from(is_divu);
        let is_remu_expr = Expr::<F>::from(is_remu);
        let is_multiplication_group_expr = is_mul_expr.clone() + is_mulhu_expr.clone();
        let is_division_group_expr = is_divu_expr.clone() + is_remu_expr.clone();
        let active_opcode_group_expr =
            is_multiplication_group_expr.clone() + is_division_group_expr.clone();

        // Generic strategy:
        // - choose variables for (high, low) = q * divisor + remainder pattern
        // - split `q` and `divisor` equivalents into u8 limbs
        // - allocate witness variables for carries
        // - perform schoolbook multiplication + enforcement

        let rs2_is_zero = cs.add_named_variable("RS2 is zero out var");
        cs.set_variables_from_lookup_constrained(
            &[LookupInput::from(
                Expr::<F>::var(rs2_limbs[0]) + Expr::var(rs2_limbs[1]),
            )],
            &[rs2_is_zero],
            cs::circuit::LookupQueryTableType::Constant(TableType::RegIsZero),
        );

        // divisor is always rs2, and quotient is either rs1 for multiplication, or extra witness for REMU,
        // or RD for DIVU

        // allocate splitting of future `q` and `divisor` and allocate witness for them
        let divisor_byte_0 = cs.add_named_variable("Divisor byte 0");
        cs.set_variables_from_lookup_constrained(
            &[LookupInput::from(Expr::<F>::var(rs2_limbs[0]))],
            &[divisor_byte_0],
            cs::circuit::LookupQueryTableType::Constant(TableType::U16GetLowByte),
        );

        let divisor_byte_2 = cs.add_named_variable("Divisor byte 2");
        cs.set_variables_from_lookup_constrained(
            &[LookupInput::from(Expr::<F>::var(rs2_limbs[1]))],
            &[divisor_byte_2],
            cs::circuit::LookupQueryTableType::Constant(TableType::U16GetLowByte),
        );

        // for quotient we can only allocate it, and copy to the next layer
        let quotient_byte_0 = cs.add_named_variable("Quotient byte 0");
        let quotient_byte_2 = cs.add_named_variable("Quotient byte 2");

        // we also need 2 variables of extra witness
        let extra_u16_witness_low = cs.add_named_variable("Extra U16 witness low");
        let extra_u16_witness_high = cs.add_named_variable("Extra U16 witness high");
        cs.require_invariant(extra_u16_witness_low, Invariant::RangeChecked { width: 16 });
        cs.require_invariant(
            extra_u16_witness_high,
            Invariant::RangeChecked { width: 16 },
        );
        let extra_witness = [extra_u16_witness_low, extra_u16_witness_high];

        let remainder_comparison_u16_witness_low =
            cs.add_named_variable("Remainder comparison U16 witness low");
        let remainder_comparison_u16_witness_high =
            cs.add_named_variable("Remainder comparison U16 witness high");
        cs.require_invariant(
            remainder_comparison_u16_witness_low,
            Invariant::RangeChecked { width: 16 },
        );
        cs.require_invariant(
            remainder_comparison_u16_witness_high,
            Invariant::RangeChecked { width: 16 },
        );

        // we do not need exact ranges for carry witnesses, just some range checks that fit
        // worst case option, and do NOT overflow the field
        let intermedaite_carry_witness: [Variable; 3] = std::array::from_fn(|i| {
            let var = cs.add_named_variable(&format!("Intermediate carry witness[{}]", i));
            var
        });

        // set witness for all those variables
        {
            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                // NOTE: it is UNCONDITIONAL assignment, even though we select across multiple variants

                let mut rd_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
                let mut extra_witness_value =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
                let mut remainder_comparison_value =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);

                let intermediate_carry_0_value;
                let intermediate_carry_1_value;
                let intermediate_carry_2_value;

                let mut quotient_byte_0_value =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U8::constant(0);
                let mut quotient_byte_1_value =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U8::constant(0);
                let mut quotient_byte_2_value =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U8::constant(0);
                let mut quotient_byte_3_value =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U8::constant(0);

                let rs1_u32 = placer.get_u32_from_u16_parts(rs1_limbs);
                let rs2_u32 = placer.get_u32_from_u16_parts(rs2_limbs);
                let rs2_is_zero = rs2_u32.is_zero();

                let is_mul = placer.get_boolean(is_mul.get_variable().unwrap());
                let is_mulhu = placer.get_boolean(is_mulhu.get_variable().unwrap());
                let is_mul_family = is_mul.or(&is_mulhu);

                let is_divu = placer.get_boolean(is_divu.get_variable().unwrap());
                let is_remu = placer.get_boolean(is_remu.get_variable().unwrap());
                let is_div_family = is_divu.or(&is_remu);

                let mut low_for_enforcement =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
                let mut high_for_enforcement =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
                let mut remainder_for_enforcement =
                    <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);

                // first we need to get extra/rd values, to then get u8 splits,
                // and perform comparisons

                {
                    // both multiplications are easy - we only need to set low/high into RD or extra witness
                    let (low, high) = rs1_u32.split_widening_product(&rs2_u32);
                    rd_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_mul, &low, &rd_value,
                    );
                    extra_witness_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_mul,
                        &high,
                        &extra_witness_value,
                    );

                    rd_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_mulhu, &high, &rd_value,
                    );
                    extra_witness_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_mulhu,
                        &low,
                        &extra_witness_value,
                    );

                    low_for_enforcement = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_mul_family,
                        &low,
                        &low_for_enforcement,
                    );
                    high_for_enforcement = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_mul_family,
                        &high,
                        &high_for_enforcement,
                    );
                }

                // DIVU and REMU are more involved as they require masking
                {
                    // default case as if we divide by 0
                    let masked_divisor = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &rs2_is_zero,
                        &<CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(u32::MAX),
                        &rs2_u32,
                    );

                    let (maybe_quotient, maybe_remainder) = <CS::WitnessPlacer as WitnessTypeSet<
                        F,
                    >>::U32::div_rem_assume_nonzero_divisor(
                        &rs1_u32, &masked_divisor
                    );
                    let quotient = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &rs2_is_zero,
                        &<CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(u32::MAX),
                        &maybe_quotient,
                    );
                    let remainder = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &rs2_is_zero,
                        &rs1_u32,
                        &maybe_remainder,
                    );

                    remainder_for_enforcement =
                        <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                            &is_div_family,
                            &remainder,
                            &remainder_for_enforcement,
                        );
                    low_for_enforcement = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_div_family,
                        &rs1_u32,
                        &low_for_enforcement,
                    );

                    rd_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_divu, &quotient, &rd_value,
                    );
                    extra_witness_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_divu,
                        &remainder,
                        &extra_witness_value,
                    );

                    rd_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_remu, &remainder, &rd_value,
                    );
                    extra_witness_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                        &is_remu,
                        &quotient,
                        &extra_witness_value,
                    );
                }

                // quickly decide on the byte splitting - we have all the values
                {
                    let rs1_byte_0 = rs1_u32.truncate().truncate();
                    let rs1_byte_1 = rs1_u32.shr(8).truncate().truncate();
                    let rs1_byte_2 = rs1_u32.shr(16).truncate().truncate();
                    let rs1_byte_3 = rs1_u32.shr(24).truncate().truncate();
                    quotient_byte_0_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U8::select(
                        &is_mul_family,
                        &rs1_byte_0,
                        &quotient_byte_0_value,
                    );
                    quotient_byte_1_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U8::select(
                        &is_mul_family,
                        &rs1_byte_1,
                        &quotient_byte_1_value,
                    );
                    quotient_byte_2_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U8::select(
                        &is_mul_family,
                        &rs1_byte_2,
                        &quotient_byte_2_value,
                    );
                    quotient_byte_3_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U8::select(
                        &is_mul_family,
                        &rs1_byte_3,
                        &quotient_byte_3_value,
                    );

                    // if we do DIVU, then we need RD
                    let rd_byte_0 = rd_value.truncate().truncate();
                    let rd_byte_1 = rd_value.shr(8).truncate().truncate();
                    let rd_byte_2 = rd_value.shr(16).truncate().truncate();
                    let rd_byte_3 = rd_value.shr(24).truncate().truncate();
                    quotient_byte_0_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U8::select(
                        &is_divu,
                        &rd_byte_0,
                        &quotient_byte_0_value,
                    );
                    quotient_byte_1_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U8::select(
                        &is_divu,
                        &rd_byte_1,
                        &quotient_byte_1_value,
                    );
                    quotient_byte_2_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U8::select(
                        &is_divu,
                        &rd_byte_2,
                        &quotient_byte_2_value,
                    );
                    quotient_byte_3_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U8::select(
                        &is_divu,
                        &rd_byte_3,
                        &quotient_byte_3_value,
                    );

                    // if we do REMU, then we need extra witness
                    let extra_witness_byte_0 = extra_witness_value.truncate().truncate();
                    let extra_witness_byte_1 = extra_witness_value.shr(8).truncate().truncate();
                    let extra_witness_byte_2 = extra_witness_value.shr(16).truncate().truncate();
                    let extra_witness_byte_3 = extra_witness_value.shr(24).truncate().truncate();
                    quotient_byte_0_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U8::select(
                        &is_remu,
                        &extra_witness_byte_0,
                        &quotient_byte_0_value,
                    );
                    quotient_byte_2_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U8::select(
                        &is_remu,
                        &extra_witness_byte_1,
                        &quotient_byte_2_value,
                    );
                    quotient_byte_2_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U8::select(
                        &is_remu,
                        &extra_witness_byte_2,
                        &quotient_byte_2_value,
                    );
                    quotient_byte_3_value = <CS::WitnessPlacer as WitnessTypeSet<F>>::U8::select(
                        &is_remu,
                        &extra_witness_byte_3,
                        &quotient_byte_3_value,
                    );
                }

                let divisor_byte_0_value = rs2_u32.truncate().truncate();
                let divisor_byte_1_value = rs2_u32.shr(8).truncate().truncate();
                let divisor_byte_2_value = rs2_u32.shr(16).truncate().truncate();
                let divisor_byte_3_value = rs2_u32.shr(24).truncate().truncate();

                // and finally we can compute intermediate witness values
                {
                    // 0-16
                    let mut bits_0_to_16_carry =
                        <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
                    bits_0_to_16_carry.add_assign(
                        &quotient_byte_0_value
                            .widening_product(&divisor_byte_0_value)
                            .widen(),
                    );
                    bits_0_to_16_carry.add_assign(
                        &quotient_byte_1_value
                            .widening_product(&divisor_byte_0_value)
                            .widen()
                            .shl(8),
                    );
                    bits_0_to_16_carry.add_assign(
                        &quotient_byte_0_value
                            .widening_product(&divisor_byte_1_value)
                            .widen()
                            .shl(8),
                    );
                    bits_0_to_16_carry.add_assign(&remainder_for_enforcement.truncate().widen());
                    bits_0_to_16_carry.sub_assign(&low_for_enforcement.truncate().widen());
                    bits_0_to_16_carry = bits_0_to_16_carry.shr(16);
                    intermediate_carry_0_value = bits_0_to_16_carry.truncate();

                    // 16-32
                    let mut bits_16_to_32_carry =
                        <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
                    bits_16_to_32_carry.add_assign(
                        &quotient_byte_1_value
                            .widening_product(&divisor_byte_1_value)
                            .widen(),
                    );
                    bits_16_to_32_carry.add_assign(
                        &quotient_byte_2_value
                            .widening_product(&divisor_byte_0_value)
                            .widen(),
                    );
                    bits_16_to_32_carry.add_assign(
                        &quotient_byte_0_value
                            .widening_product(&divisor_byte_2_value)
                            .widen(),
                    );
                    bits_16_to_32_carry.add_assign(
                        &quotient_byte_3_value
                            .widening_product(&divisor_byte_0_value)
                            .widen()
                            .shl(8),
                    );
                    bits_16_to_32_carry.add_assign(
                        &quotient_byte_0_value
                            .widening_product(&divisor_byte_3_value)
                            .widen()
                            .shl(8),
                    );
                    bits_16_to_32_carry.add_assign(
                        &quotient_byte_2_value
                            .widening_product(&divisor_byte_1_value)
                            .widen()
                            .shl(8),
                    );
                    bits_16_to_32_carry.add_assign(
                        &quotient_byte_1_value
                            .widening_product(&divisor_byte_2_value)
                            .widen()
                            .shl(8),
                    );
                    bits_16_to_32_carry.add_assign(&remainder_for_enforcement.shr(16));
                    bits_16_to_32_carry.add_assign(&bits_0_to_16_carry);
                    bits_16_to_32_carry.sub_assign(&low_for_enforcement.shr(16));
                    bits_16_to_32_carry = bits_16_to_32_carry.shr(16);
                    intermediate_carry_1_value = bits_16_to_32_carry.truncate();

                    // 32-48
                    let mut bits_32_to_48_carry =
                        <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
                    bits_32_to_48_carry.add_assign(
                        &quotient_byte_3_value
                            .widening_product(&divisor_byte_1_value)
                            .widen(),
                    );
                    bits_32_to_48_carry.add_assign(
                        &quotient_byte_2_value
                            .widening_product(&divisor_byte_2_value)
                            .widen(),
                    );
                    bits_32_to_48_carry.add_assign(
                        &quotient_byte_1_value
                            .widening_product(&divisor_byte_3_value)
                            .widen(),
                    );
                    bits_32_to_48_carry.add_assign(
                        &quotient_byte_3_value
                            .widening_product(&divisor_byte_2_value)
                            .widen()
                            .shl(8),
                    );
                    bits_32_to_48_carry.add_assign(
                        &quotient_byte_3_value
                            .widening_product(&divisor_byte_2_value)
                            .widen()
                            .shl(8),
                    );
                    bits_32_to_48_carry.add_assign(&bits_16_to_32_carry);
                    bits_32_to_48_carry.sub_assign(&high_for_enforcement.truncate().widen());
                    bits_32_to_48_carry = bits_32_to_48_carry.shr(16);
                    intermediate_carry_2_value = bits_32_to_48_carry.truncate();

                    // we do not need to continue the carry chain
                }

                // and the last one - is to assign something to the aux variables
                // for remainder < divisor check
                {
                    let (t, _) = rd_value.overflowing_sub(&rs2_u32);
                    remainder_comparison_value =
                        <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                            &is_remu,
                            &t,
                            &remainder_comparison_value,
                        );

                    let (t, _) = extra_witness_value.overflowing_sub(&rs2_u32);
                    remainder_comparison_value =
                        <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                            &is_divu,
                            &t,
                            &remainder_comparison_value,
                        );

                    let (t, _) = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0)
                        .overflowing_sub(&rs2_u32);
                    remainder_comparison_value =
                        <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                            &is_mul_family,
                            &t,
                            &remainder_comparison_value,
                        );
                }

                // actually assign
                if CS::ASSUME_MEMORY_VALUES_ASSIGNED == false {
                    placer.assign_u32_from_u16_parts(rd_write_limbs, &rd_value);
                }

                placer.assign_u8(quotient_byte_0, &quotient_byte_0_value);
                placer.assign_u8(quotient_byte_2, &quotient_byte_2_value);

                placer.assign_u32_from_u16_parts(extra_witness, &extra_witness_value);
                placer.assign_u32_from_u16_parts(
                    [
                        remainder_comparison_u16_witness_low,
                        remainder_comparison_u16_witness_high,
                    ],
                    &remainder_comparison_value,
                );

                placer.assign_u16(intermedaite_carry_witness[0], &intermediate_carry_0_value);
                placer.assign_u16(intermedaite_carry_witness[1], &intermediate_carry_1_value);
                placer.assign_u16(intermedaite_carry_witness[2], &intermediate_carry_2_value);
            };
            cs.set_values(value_fn);
        }

        // range-check intermediate carries
        {
            assert!(F::CHAR_BITS > 16 + 13);
            intermedaite_carry_witness.iter().for_each(|var| {
                cs.enforce_lookup_tuple_for_fixed_table(
                    &[LookupInput::from(Expr::<F>::var(*var))],
                    TableType::RangeCheck13,
                    false,
                );
            });
        }

        // now we push everything to the intermediate layer
        let divisor_is_zero_if_division_layer_1 = cs.add_intermediate_named_variable_from_expr(
            is_division_group_expr.clone() * Expr::var(rs2_is_zero),
            "divisor is zero if division at layer 1",
        );

        // select all variables and push them to layer 1
        let low_at_layer_1: [Variable; 2] = std::array::from_fn(|i| {
            cs.add_intermediate_named_variable_from_expr(
                Expr::var(rd_write_limbs[i]).mask(is_mul)
                    + Expr::var(extra_witness[i]).mask(is_mulhu)
                    + is_division_group_expr.clone() * Expr::var(rs1_limbs[i]),
                &format!("low[{}] at layer 1", i),
            )
        });
        let high_at_layer_1: [Variable; 2] = std::array::from_fn(|i| {
            cs.add_intermediate_named_variable_from_expr(
                Expr::var(rd_write_limbs[i]).mask(is_mulhu)
                    + Expr::var(extra_witness[i]).mask(is_mul),
                // 0 if any division group
                &format!("high[{}] at layer 1", i),
            )
        });
        let quotient_at_layer_1: [Variable; 2] = std::array::from_fn(|i| {
            cs.add_intermediate_named_variable_from_expr(
                is_multiplication_group_expr.clone() * Expr::var(rs1_limbs[i])
                    + Expr::var(rd_write_limbs[i]).mask(is_divu)
                    + Expr::var(extra_witness[i]).mask(is_remu),
                &format!("quotient[{}] at layer 1", i),
            )
        });
        let remainder_at_layer_1: [Variable; 2] = std::array::from_fn(|i| {
            cs.add_intermediate_named_variable_from_expr(
                // 0 for any mul
                Expr::var(extra_witness[i]).mask(is_divu)
                    + Expr::var(rd_write_limbs[i]).mask(is_remu),
                &format!("remainder[{}] at layer 1", i),
            )
        });
        // it'll select 0, so padding rows are fine
        let divisor_at_layer_1: [Variable; 2] = std::array::from_fn(|i| {
            cs.add_intermediate_named_variable_from_expr(
                active_opcode_group_expr.clone() * Expr::var(rs2_limbs[i]),
                &format!("divisor[{}] at layer 1", i),
            )
        });

        let is_division_family_at_layer_1 = cs.add_intermediate_named_variable_from_expr(
            is_division_group_expr.clone(),
            "is division family at layer 1",
        );

        let remainder_comparison_u16_witness_low_at_layer_1 = cs
            .add_intermediate_named_variable_from_expr(
                Expr::var(remainder_comparison_u16_witness_low),
                "Remainder comparison U16 witness low at layer 1",
            );
        let remainder_comparison_u16_witness_high_at_layer_1 = cs
            .add_intermediate_named_variable_from_expr(
                Expr::var(remainder_comparison_u16_witness_high),
                "Remainder comparison U16 witness high at layer 1",
            );

        let divisor_byte_0_at_layer_1 = cs.add_intermediate_named_variable_from_expr(
            Expr::var(divisor_byte_0),
            "divisor byte 0 at layer 1",
        );
        let divisor_byte_2_at_layer_1 = cs.add_intermediate_named_variable_from_expr(
            Expr::var(divisor_byte_2),
            "divisor byte 2 at layer 1",
        );
        let quotient_byte_0_at_layer_1 = cs.add_intermediate_named_variable_from_expr(
            Expr::var(quotient_byte_0),
            "quotient byte 0 at layer 1",
        );
        let quotient_byte_2_at_layer_1 = cs.add_intermediate_named_variable_from_expr(
            Expr::var(quotient_byte_2),
            "quotient byte 2 at layer 1",
        );
        let intermedaite_carry_witness_layer_1 = {
            let mut i = 0;
            intermedaite_carry_witness.map(|el| {
                let t = cs.add_intermediate_named_variable_from_expr(
                    Expr::var(el),
                    &format!("intermediate carry witness[{}] at layer 1", i),
                );
                i += 1;

                t
            })
        };

        // enforce decomposition on the layer 1 for bytes
        cs.enforce_lookup_tuple_for_fixed_table(
            &[
                LookupInput::from(quotient_at_layer_1[0]),
                LookupInput::from(quotient_byte_0_at_layer_1),
            ],
            TableType::U16GetLowByte,
            false,
        );
        cs.enforce_lookup_tuple_for_fixed_table(
            &[
                LookupInput::from(quotient_at_layer_1[1]),
                LookupInput::from(quotient_byte_2_at_layer_1),
            ],
            TableType::U16GetLowByte,
            false,
        );

        // simply enforce the schoolbook multiplication relation
        {
            let quotient_bytes = [
                Expr::<F>::var(quotient_byte_0_at_layer_1),
                (Expr::<F>::var(quotient_at_layer_1[0]) - Expr::var(quotient_byte_0_at_layer_1))
                    * shift_right_8_bits,
                Expr::<F>::var(quotient_byte_2_at_layer_1),
                (Expr::<F>::var(quotient_at_layer_1[1]) - Expr::var(quotient_byte_2_at_layer_1))
                    * shift_right_8_bits,
            ];

            let divisor_bytes = [
                Expr::<F>::var(divisor_byte_0_at_layer_1),
                (Expr::<F>::var(divisor_at_layer_1[0]) - Expr::var(divisor_byte_0_at_layer_1))
                    * shift_right_8_bits,
                Expr::<F>::var(divisor_byte_2_at_layer_1),
                (Expr::<F>::var(divisor_at_layer_1[1]) - Expr::var(divisor_byte_2_at_layer_1))
                    * shift_right_8_bits,
            ];

            let target_u16_words = [
                low_at_layer_1[0],
                low_at_layer_1[1],
                high_at_layer_1[0],
                high_at_layer_1[1],
            ];

            let addends_u16_words = [
                Some(remainder_at_layer_1[0]),
                Some(remainder_at_layer_1[1]),
                None,
                None,
            ];

            let carry_out_u16_words = [
                Some(intermedaite_carry_witness_layer_1[0]),
                Some(intermedaite_carry_witness_layer_1[1]),
                Some(intermedaite_carry_witness_layer_1[2]),
                None,
            ];

            let carry_in_u16_words = [
                None,
                Some(intermedaite_carry_witness_layer_1[0]),
                Some(intermedaite_carry_witness_layer_1[1]),
                Some(intermedaite_carry_witness_layer_1[2]),
            ];

            for i in 0..4 {
                // `i` marks u16-ish chunks over which we accumulate
                // schoolbook multplication terms
                println!("Computing enforcement on limb {}", i);

                let mut expr = Expr::<F>::zero();

                for j in 0..4 {
                    let q_byte = &quotient_bytes[j];
                    for k in 0..4 {
                        let d_byte = &divisor_bytes[k];
                        if j + k == 2 * i {
                            // println!(" + {:?} * {:?}", q_byte.get_value(cs), d_byte.get_value(cs));
                            expr = expr + q_byte.clone() * d_byte.clone();
                        } else if j + k == 2 * i + 1 {
                            // println!(
                            //     " + 256 * {:?} * {:?}",
                            //     q_byte.get_value(cs),
                            //     d_byte.get_value(cs)
                            // );
                            expr = expr + q_byte.clone() * d_byte.clone() * shift_left_8_bits;
                        }
                    }
                }

                if let Some(addend) = addends_u16_words[i] {
                    // println!(" + {:?}", cs.get_value(addend));
                    expr = expr + Expr::var(addend);
                }
                if let Some(carry_in) = carry_in_u16_words[i] {
                    // println!(" + {:?}", cs.get_value(carry_in));
                    expr = expr + Expr::var(carry_in);
                }
                if let Some(carry_out) = carry_out_u16_words[i] {
                    // println!(" - 2^16 * {:?}", cs.get_value(carry_out));
                    expr = expr - Expr::var(carry_out) * shift_left_16_bits;
                }
                // println!(" - {:?}", cs.get_value(target_u16_words[i]));
                expr = expr - Expr::var(target_u16_words[i]);
                cs.add_constraint_expr(expr);
            }
        }

        // and the last thing to do is to check that remainder < divisor unless divisor is 0,
        // and if divisor is 0 - then quotient is u32::MAX

        // NOTE: first boolean check is unconditional, so we should place there something even in case of multiplication.
        // In this case remainder is 0

        // 2^16 * of + remainder - divisor = witness
        let remainder_comparison_carry =
            (Expr::<F>::var(remainder_comparison_u16_witness_low_at_layer_1)
                - Expr::var(remainder_at_layer_1[0])
                + Expr::var(divisor_at_layer_1[0]))
                * shift_left_16_bits.inverse().unwrap();
        cs.add_constraint_expr(
            remainder_comparison_carry.clone()
                * (remainder_comparison_carry.clone() - Expr::<F>::one()),
        );

        // 2^16*(1 - divisor_is_zero) + remainder - divisor - carry = witness
        let high_remainder_comparison = (Expr::<F>::one()
            - Expr::var(divisor_is_zero_if_division_layer_1))
            * shift_left_16_bits
            + Expr::var(remainder_at_layer_1[1])
            - Expr::var(divisor_at_layer_1[1])
            - remainder_comparison_carry
            - Expr::var(remainder_comparison_u16_witness_high_at_layer_1);
        cs.add_constraint_expr(
            high_remainder_comparison * Expr::var(is_division_family_at_layer_1),
        );

        cs.add_constraint_expr(
            (Expr::<F>::var(low_at_layer_1[0]) - Expr::var(remainder_at_layer_1[0]))
                * Expr::var(divisor_is_zero_if_division_layer_1),
        );
        cs.add_constraint_expr(
            (Expr::<F>::var(low_at_layer_1[1]) - Expr::var(remainder_at_layer_1[1]))
                * Expr::var(divisor_is_zero_if_division_layer_1),
        );

        cs.add_constraint_expr(
            (Expr::<F>::from(u16::MAX as u32) - Expr::var(quotient_at_layer_1[0]))
                * Expr::var(divisor_is_zero_if_division_layer_1),
        );
        cs.add_constraint_expr(
            (Expr::<F>::from(u16::MAX as u32) - Expr::var(quotient_at_layer_1[1]))
                * Expr::var(divisor_is_zero_if_division_layer_1),
        );
    } else {
        todo!("support signed ops")
    }

    if let Some(rd_reg) = Register(rd_write_limbs.map(|el| Num::Var(el))).get_value_unsigned(cs) {
        println!("RD value = 0x{:08x}", rd_reg);
    }

    // bump PC
    use crate::gkr_circuits::utils::calculate_pc_next_no_overflows_with_range_checks;
    calculate_pc_next_no_overflows_with_range_checks(
        cs,
        inputs.cycle_start_state.pc,
        inputs.cycle_end_state.pc,
    );
}

pub fn mul_div_circuit_with_preprocessed_bytecode_for_gkr<
    F: PrimeField,
    CS: Circuit<F>,
    const SUPPORT_SIGNED: bool,
>(
    cs: &mut CS,
) {
    let num_flags = if SUPPORT_SIGNED {
        MUL_DIV_FAMILY_NUM_FLAGS
    } else {
        UNSIGNED_MUL_DIV_FAMILY_NUM_FLAGS
    };
    let (input, bitmask) = cs.allocate_machine_state(false, false, num_flags);
    let bitmask: Vec<_> = bitmask.into_iter().map(|el| Boolean::Is(el)).collect();
    let decoder = DivMulFamilyCircuitMask::<SUPPORT_SIGNED>::from_mask(&bitmask);
    apply_mul_div_inner::<F, CS, SUPPORT_SIGNED>(cs, input, decoder);
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use crate::cs::circuit_impl::BasicAssembly;
    use crate::cs::circuit_output::CircuitOutput;
    use crate::gkr_compiler::compile_unrolled_circuit_state_transition_into_gkr;
    use crate::gkr_compiler::compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches;
    use crate::gkr_compiler::dump_ssa_witness_eval_form;
    use crate::structured_expr::StructuredStatement;
    use crate::utils::serialize_to_file;

    type F = ::field::Mersenne31Field;

    // fn named_variable(output: &CircuitOutput<F>, expected_name: &str) -> Variable {
    //     output
    //         .variable_names
    //         .iter()
    //         .find_map(|(variable, name)| (name == expected_name).then_some(*variable))
    //         .expect("named variable must exist")
    // }

    // fn defined_expr_for<'a>(output: &'a CircuitOutput<F>, expected_name: &str) -> &'a Expr<F> {
    //     let variable = named_variable(output, expected_name);

    //     output
    //         .structured_statements
    //         .iter()
    //         .find_map(|statement| match statement {
    //             StructuredStatement::Define { dst, expr } if *dst == variable => Some(expr),
    //             StructuredStatement::Define { .. } | StructuredStatement::AssertZero { .. } => None,
    //         })
    //         .expect("named variable must have structured definition")
    // }

    // fn contains_product_with_sum_factor(expr: &Expr<F>) -> bool {
    //     match expr {
    //         Expr::Product(factors) => {
    //             factors.iter().any(|factor| matches!(factor, Expr::Sum(_)))
    //                 || factors.iter().any(contains_product_with_sum_factor)
    //         }
    //         Expr::Sum(terms) => terms.iter().any(contains_product_with_sum_factor),
    //         Expr::Constant(_) | Expr::Var(_) => false,
    //     }
    // }

    // fn grouped_schoolbook_terms_count(expr: &Expr<F>) -> usize {
    //     let Expr::Sum(terms) = expr else {
    //         return 0;
    //     };

    //     terms
    //         .iter()
    //         .filter(|term| contains_product_with_sum_factor(term))
    //         .count()
    // }

    // #[test]
    // fn unsigned_mul_div_records_grouped_layer_1_selectors() {
    //     let mut cs = BasicAssembly::<F>::new();
    //     mul_div_circuit_with_preprocessed_bytecode_for_gkr::<_, _, false>(&mut cs);
    //     let (output, _) = cs.finalize();

    //     let divisor_is_zero = defined_expr_for(&output, "divisor is zero if division at layer 1");
    //     let quotient = defined_expr_for(&output, "quotient[0] at layer 1");
    //     let divisor = defined_expr_for(&output, "divisor[0] at layer 1");

    //     assert!(contains_product_with_sum_factor(divisor_is_zero));
    //     assert!(contains_product_with_sum_factor(quotient));
    //     assert!(contains_product_with_sum_factor(divisor));
    // }

    // #[test]
    // fn unsigned_mul_div_records_grouped_schoolbook_terms() {
    //     let mut cs = BasicAssembly::<F>::new();
    //     mul_div_circuit_with_preprocessed_bytecode_for_gkr::<_, _, false>(&mut cs);
    //     let (output, _) = cs.finalize();

    //     assert!(output
    //         .structured_statements
    //         .iter()
    //         .any(|statement| matches!(
    //             statement,
    //             StructuredStatement::AssertZero { expr, .. }
    //                 if grouped_schoolbook_terms_count(expr) >= 2
    //         )));
    // }

    #[test]
    fn compile_unsigned_mul_div_into_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let gkr_compiled = compile_unrolled_circuit_state_transition_into_gkr::<BabyBearField>(
            &|cs| mul_div_table_addition_fn::<_, _, false>(cs),
            &|cs| mul_div_circuit_with_preprocessed_bytecode_for_gkr::<_, _, false>(cs),
            common_constants::ROM_WORD_SIZE,
            24,
        );

        serialize_to_file(
            &gkr_compiled,
            "compiled_circuits/unsigned_mul_div_layout_gkr.json",
        );
    }

    #[test]
    fn compile_unsigned_mul_div_gkr_witness_graph() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let ssa_forms = dump_ssa_witness_eval_form::<BabyBearField>(
            &|cs| mul_div_table_addition_fn::<_, _, false>(cs),
            &|cs| mul_div_circuit_with_preprocessed_bytecode_for_gkr::<_, _, false>(cs),
        );
        serialize_to_file(
            &ssa_forms,
            "compiled_circuits/unsigned_mul_div_ssa_gkr.json",
        );
    }

    #[test]
    fn compile_unsigned_mul_div_into_no_caches_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let gkr_compiled =
            compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches::<
                BabyBearField,
            >(
                &|cs| mul_div_table_addition_fn::<_, _, false>(cs),
                &|cs| mul_div_circuit_with_preprocessed_bytecode_for_gkr::<_, _, false>(cs),
                common_constants::ROM_WORD_SIZE,
                24,
            );

        serialize_to_file(
            &gkr_compiled,
            "compiled_circuits/unsigned_mul_div_layout_no_caches_gkr.json",
        );
    }
}
