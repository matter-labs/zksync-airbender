use super::*;
use crate::machine::Term;
use crate::one_row_compiler::LookupInput;
use crate::tables::TableType;
use crate::types::Boolean;
use crate::{constraint::Constraint, machine::read_opcode_from_rom, types::Register};

const OPCODE_TYPES_BITS: usize = NUM_INSTRUCTION_TYPES - 1;

pub fn describe_decoder_cycle<
    F: PrimeField,
    CS: Circuit<F>,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    circuit: &mut CS,
) {
    let decoder_circuit_state = circuit.allocate_decoder_circuit_state();

    // first we read opcode

    let pc = Register(
        decoder_circuit_state
            .cycle_start_state
            .pc
            .map(|el| Num::Var(el)),
    );

    let next_opcode =
        read_opcode_from_rom::<F, CS, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(circuit, pc);

    if let Some(opcode) = next_opcode.get_value_unsigned(circuit) {
        println!("Opcode = 0x{:08x}", opcode);
    }

    // now we can parse the opcode. Note that many variables are already pre-allocated for us,
    // so we will want to use them as much as possible

    // instruction set of variables: low: [15:0], high: [31:16]
    // the most shredded instruction type is B-type (with additional splitting of rs_2, required for J-type):
    // all other instruction types can be constructed from
    // chunks of split instruction are:
    // opcode [6:0], imm11: [7], imm[4-1]: [11:8], func3: [14:12], rs1: [19:15],
    // rs2_low: [20], rs2_high: [24:21], imm[10-5]: [30:25], imm12: [31]
    // rs1 crosses the border of register, so we will allocate an extra boolean variable
    // and feed part of rs1 into lookup expression for 4-bit range check

    // NOTE: we DO range check opcode (7 bits) so we can later on use a single table lookup to get all our opcode properties

    let opcode = Num::Var(circuit.add_variable()); // doesn't go into decoder output

    // we have rd from decoder output, but we need to split a low bit
    let rd_from_decoder = Num::Var(decoder_circuit_state.decoder_data.decoder_data.rd_index);
    let imm11 = circuit.add_boolean_variable();
    // NOTE: the fact that rd = (imm4_1 << 1) + imm11 is enforced
    // when we perform lookup over the relation
    let mut imm4_1: Constraint<F> = Constraint::from(rd_from_decoder);
    imm4_1 -= Term::from(imm11);
    imm4_1.scale(F::from_u64_unchecked(1 << 1).inverse().unwrap());
    // funct3 comes from decoder
    let funct3 = Num::Var(decoder_circuit_state.decoder_data.decoder_data.funct3);
    // rs1 crosses the boundary, and we could need to split lowest bit. Instead - we rewrite it as
    // linear constraint

    // insn_low <=> opcode [6:0], rd: [11:7], func3: [14:12], rs1_low: [15],
    let [low_insn, high_insn] = next_opcode.get_terms();
    let mut rs1_low_constraint = {
        low_insn
            - Term::from(opcode) // 7 bits
            - Term::from(1 << 7) * Term::from(rd_from_decoder) // 5 bits
            - Term::from(1 << 12) * Term::from(funct3) // 3 bits
    };
    rs1_low_constraint.scale(F::from_u64_unchecked(1 << 15).inverse().unwrap());
    // ensure that it's boolean
    circuit
        .add_constraint(rs1_low_constraint.clone() * (rs1_low_constraint.clone() - Term::from(1)));

    let rs1_from_decoder = Num::Var(decoder_circuit_state.decoder_data.decoder_data.rs1_index);

    let mut rs1_high: Constraint<F> = Constraint::from(rs1_from_decoder);
    rs1_high = rs1_high - rs1_low_constraint.clone();
    rs1_high.scale(F::from_u64_unchecked(1 << 1).inverse().unwrap());
    // rs2 doesn't cross the word boundary, but we need it's 1 bit to parse immediate
    let rs2_from_decoder = Num::Var(decoder_circuit_state.decoder_data.decoder_data.rs2_index);

    // NOTE: the fact that rs2 = (rs2_high << 1) + rs2_low is enforced
    // when we perform lookup over the relation
    let rs2_low = circuit.add_boolean_variable();
    let mut rs2_high: Constraint<F> = Constraint::from(rs2_from_decoder);
    rs2_high -= Term::from(rs2_low);
    rs2_high.scale(F::from_u64_unchecked(1 << 1).inverse().unwrap());
    let imm10_5 = Num::Var(circuit.add_variable());

    // and we do not need sign bit, as we can span a linear constraint on it
    // insn_high <=> rs1_high: [19:16], rs2: [24:20], imm[10-5]: [30:25], imm12: [31]
    let mut sign_bit_constraint = {
        Constraint::from(high_insn)
            - rs1_high.clone()
            - Term::from(rs1_from_decoder) * Term::from(1 << 4)
            - Term::from(imm10_5) * Term::from(1 << 9)
    };
    sign_bit_constraint.scale(F::from_u64_unchecked(1 << 16).inverse().unwrap());
    circuit.add_constraint(
        sign_bit_constraint.clone() * (sign_bit_constraint.clone() - Term::from(1)),
    );
    let funct7_from_decoder = Num::Var(
        decoder_circuit_state
            .decoder_data
            .decoder_data
            .funct7
            .expect("funct7 must be allocated in decoder circuit"),
    );

    // here we will have to write value-fn manually

    let input = next_opcode.0.map(|el| el.get_variable());

    let opcode_var = opcode.get_variable();
    let imm11_var = imm11.get_variable().unwrap();
    let rd_full_var = rd_from_decoder.get_variable();
    let funct3_var = funct3.get_variable();
    let rs1_full_var = rs1_from_decoder.get_variable();
    let rs2_full_var = rs2_from_decoder.get_variable();
    let rs2_low_var = rs2_low.get_variable().unwrap();
    let imm10_5_var = imm10_5.get_variable();
    let funct7_full_var = funct7_from_decoder.get_variable();

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        use crate::cs::witness_placer::*;

        let mut low_word = placer.get_u16(input[0]);
        let mut high_word = placer.get_u16(input[1]);

        let opcode = low_word.get_lowest_bits(7);
        low_word = low_word.shr(7);
        let rd = low_word.get_lowest_bits(5);
        let imm_11 = low_word.get_bit(0);
        low_word = low_word.shr(5);
        let funct3 = low_word.get_lowest_bits(3);
        low_word = low_word.shr(3);
        let rs1_low_integer = low_word.get_lowest_bits(1);

        let rs1_high = high_word.get_lowest_bits(4);
        high_word = high_word.shr(4);
        let rs2_low = high_word.get_bit(0);
        let rs2 = high_word.get_lowest_bits(5);
        high_word = high_word.shr(5);
        let imm10_5 = high_word.get_lowest_bits(6);
        let funct7 = high_word;

        let mut rs1 = rs1_high.clone();
        rs1 = rs1.shl(1);
        rs1.add_assign(&rs1_low_integer);

        placer.assign_u16(opcode_var, &opcode);
        placer.assign_mask(imm11_var, &imm_11);
        placer.assign_u16(rd_full_var, &rd);
        placer.assign_u16(funct3_var, &funct3);

        placer.assign_u16(rs1_full_var, &rs1);
        placer.assign_mask(rs2_low_var, &rs2_low);
        placer.assign_u16(rs2_full_var, &rs2);
        placer.assign_u16(imm10_5_var, &imm10_5);
        placer.assign_u16(funct7_full_var, &funct7);
    };

    circuit.set_values(value_fn);

    // range check decomposition pieces
    circuit.enforce_lookup_tuple_for_fixed_table(
        &[
            LookupInput::from(imm4_1.clone()),
            LookupInput::from(rs1_high.clone()),
            LookupInput::from(rs2_high.clone()),
        ],
        TableType::QuickDecodeDecompositionCheck4x4x4,
        false,
    );

    circuit.enforce_lookup_tuple_for_fixed_table(
        &[
            opcode.get_variable(),
            funct3.get_variable(),
            imm10_5.get_variable(),
        ]
        .map(|el| LookupInput::from(el)),
        TableType::QuickDecodeDecompositionCheck7x3x6,
        false,
    );

    // we still have a linear constraint here - just to collect funct7
    circuit.add_constraint_allow_explicit_linear(
        sign_bit_constraint.clone() * Term::from(1 << 6) + Term::from(imm10_5)
            - Term::from(funct7_from_decoder),
    );

    // now we can feed [opcode || funct_3 || funct 7] (all are range checked, so concatenation IS allowed)
    // to get basic bitmask that will tell whether the opcode is valid or not, and provide aux properties
    // like belonging to opcode family, etc
    let (
        is_invalid,
        [i_insn, s_insn, b_insn, u_insn, j_insn], // no r_inst
    ) = opcode_lookup(
        circuit,
        opcode,
        funct3,
        funct7_from_decoder,
        decoder_circuit_state.decoder_data.circuit_family,
        decoder_circuit_state
            .decoder_data
            .decoder_data
            .circuit_family_extra_mask,
    );

    // We do not support invalid opcodes
    circuit
        .add_constraint_allow_explicit_linear_prevent_optimizations(Constraint::from(is_invalid));

    // now we need to construct the right constant from different constant chunks
    // the actual constant is dependent on the opcode type:
    // -------------------------------------------------------------------------------------------------------|
    // |       chunk5[31-16]    |   chunk4[15-12]   | chunk3[11] | chunk2[10-5] | chunk1[4-1] | chunk0[0] |   |
    // |========================|===================|============|==============|=============|===========|===|
    // |         sign_bit       |    sign_bit       |  sign_bit  |   imm[10-5]  |   rs2_high  |  rs2_low  | I |
    // |------------------------|-------------------|------------|--------------|-------------|-----------|---|
    // |         sign_bit       |    sign_bit       |  sign_bit  |   imm[10-5]  |   imm4_1    |   imm11   | S |
    // |------------------------|-------------------|------------|--------------|-------------|-----------|---|
    // |         sign_bit       |    sign_bit       |   imm11    |   imm[10-5]  |   imm4_1    |     0     | B |
    // |------------------------|-------------------|------------|--------------|-------------|-----------|---|
    // |         insn_high      | rs1_low || funct3 |      0     |      0       |      0      |     0     | U |
    // |------------------------|-------------------|------------|--------------|-------------|-----------|---|
    // |  sign_bit || rs1_high  | rs1_low || funct3 |  rs2_low   |   imm[10-5]  |   rs2_high  |     0     | J |
    // |========================|===================|============|==============|=============|===========|===|
    // hence:
    // chunk0 = i_insn * rs2_low +  s_insn * imm11
    // chunk1 = (i_insn + j_insn) * rs2_high + (s_insn + b_insn) * imm4_1
    // chunk2 = (1 - u_insn) * imm10_5
    // chunk3 = (i_insn + s_insn) * sign_bit + b_insn * imm11 + j_insn * rs2_low
    // chunk4 = (i_insn + s_insn + b_insn) * sign_bit * 0b1111 + (u_insn + j_insn) * (rs1_low << 3 + funct3)
    // chunk5 = {
    //      j_insn * (sign_bit * 0xfff0 + rs1_high) + u_insn * insn_high +
    //      (1 - j_insn - b_insn) * sign_bit * 0xffff
    // }

    // chunks 0..4 are used for linear constraint later on to form imm_low
    let chunks_defining_constraints: [Constraint<F>; 5] = [
        // 0
        Term::from(i_insn) * Term::from(rs2_low) + Term::from(s_insn) * Term::from(imm11),
        // 1
        (Term::from(i_insn) + Term::from(j_insn)) * rs2_high
            + (Term::from(s_insn) + Term::from(b_insn)) * imm4_1.clone(),
        // 2
        (Term::from(1) - Term::from(u_insn)) * Term::from(imm10_5),
        // 3
        (Term::from(i_insn) + Term::from(s_insn)) * sign_bit_constraint.clone()
            + Term::from(b_insn) * Term::from(imm11)
            + Term::from(j_insn) * Term::from(rs2_low),
        // 4
        (Term::from(i_insn) + Term::from(s_insn) + Term::from(b_insn))
            * sign_bit_constraint.clone()
            * Term::from(0b1111u64)
            + (Term::from(u_insn) + Term::from(j_insn))
                * (rs1_low_constraint * Term::from(1 << 3) + (Term::from(funct3))),
    ];

    let [chunk0, chunk1, chunk2, chunk3, chunk4] = chunks_defining_constraints;

    // now we just need to link it to decoder vars
    let imm_low = decoder_circuit_state.decoder_data.decoder_data.imm[0];
    circuit.add_constraint(
        chunk0
            + chunk1 * Term::from(1 << 1)
            + chunk2 * Term::from(1 << 5)
            + chunk3 * Term::from(1 << 11)
            + chunk4 * Term::from(1 << 12)
            - Term::from(imm_low),
    );

    // chunk 5 is just higher part of the immediate
    let imm_high = decoder_circuit_state.decoder_data.decoder_data.imm[1];
    circuit.add_constraint(
        Term::from(j_insn) * (sign_bit_constraint.clone() * Term::from(0xfff0) + rs1_high)
            + Term::from(u_insn) * Term::from(next_opcode.0[1])
            + (Term::from(1) - Term::from(j_insn) - Term::from(u_insn))
                * sign_bit_constraint
                * Term::from(0xffff)
            - Term::from(imm_high),
    );

    // funct_12 is used only by:
    // SYSTEM CSR - there we can use single table lookup to validate if 12-bit index is valid and trap (along with R/W info if we want)
    // SYSTEM ECALL/EBREAK - again, we can check validity in there, because if it's not a valid 12-bit index we will trap anyway, but with different code

    // and just need to check if RD is 0 (it's just a check for a value being 0, and can be meaningless for some opcodes)
    {
        // var * zero_flag = 0;
        // var * var_inv = 1 - zero_flag;
        let var_inv = circuit.add_variable();
        let zero_flag_var = decoder_circuit_state.decoder_data.decoder_data.rd_is_zero;

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            use crate::cs::witness_placer::WitnessComputationalField;
            use crate::cs::witness_placer::WitnessPlacer;
            let a = placer.get_field(rd_full_var);
            let is_zero = a.is_zero();
            let inverse_witness = a.inverse_or_zero();
            placer.assign_mask(zero_flag_var, &is_zero);
            placer.assign_field(var_inv, &inverse_witness);
        };
        circuit.set_values(value_fn);

        circuit.add_constraint(Term::from(rd_full_var) * Term::from(zero_flag_var));
        circuit.add_constraint(
            Term::from(rd_full_var) * Term::from(var_inv) + Term::from(zero_flag_var)
                - Term::from(1),
        );
    }

    // And we are done - all variables are linked and values were assigned
}

#[track_caller]
fn opcode_lookup<F: PrimeField, CS: Circuit<F>>(
    circuit: &mut CS,
    opcode: Num<F>,
    funct3: Num<F>,
    funct7: Num<F>,
    opcode_family_type_var: Variable,
    opcode_family_bitmask_var: Variable,
) -> (Boolean, [Boolean; OPCODE_TYPES_BITS]) {
    let table_input_constraint = Constraint::empty()
        + Term::from(opcode)
        + Term::from(funct3) * Term::from(1 << 7)
        + Term::from(funct7) * Term::from(1 << (7 + 3));

    // here we will merge bit decomposition AND splitting, by putting linear constraints into everything

    let is_invalid = circuit.add_boolean_variable();
    let opcode_formats_except_r: [Boolean; OPCODE_TYPES_BITS] =
        std::array::from_fn(|_| circuit.add_boolean_variable());

    let mut splitting_constraint = Constraint::empty();
    splitting_constraint += Term::from(is_invalid);
    for (i, src) in opcode_formats_except_r.iter().enumerate() {
        splitting_constraint = splitting_constraint + Term::from(*src) * Term::from(1 << (1 + i));
    }
    splitting_constraint = splitting_constraint
        + Term::from(opcode_family_bitmask_var) * Term::from(1 << NUM_DEFAULT_DECODER_BITS);

    assert_eq!(InstructionType::RType as u32, 0);

    {
        let outputs = [
            is_invalid.get_variable().unwrap(),
            opcode_formats_except_r[0].get_variable().unwrap(),
            opcode_formats_except_r[1].get_variable().unwrap(),
            opcode_formats_except_r[2].get_variable().unwrap(),
            opcode_formats_except_r[3].get_variable().unwrap(),
            opcode_formats_except_r[4].get_variable().unwrap(),
        ];

        let opcode = opcode.get_variable();
        let funct3 = funct3.get_variable();
        let funct7 = funct7.get_variable();

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            use crate::cs::witness_placer::*;

            let mut result = placer.get_field(opcode);
            let funct3 = placer.get_field(funct3);
            let funct7 = placer.get_field(funct7);
            let coeff = <CS::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(
                F::from_u64_unchecked(1 << 7),
            );
            result.add_assign_product(&coeff, &funct3);
            let coeff = <CS::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(
                F::from_u64_unchecked(1 << (7 + 3)),
            );
            result.add_assign_product(&coeff, &funct7);

            let table_id = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                TableType::OpTypeBitmask.to_table_id() as u16,
            );
            let [family, joined_bitmask] = placer.lookup::<1, 2>(&[result], &table_id);
            let joined_bitmask = joined_bitmask.as_integer();
            let props_bits = joined_bitmask.get_lowest_bits(NUM_DEFAULT_DECODER_BITS as u32);
            let family_bits = joined_bitmask.shr(NUM_DEFAULT_DECODER_BITS as u32);

            for i in 0..NUM_DEFAULT_DECODER_BITS {
                let bit = props_bits.get_bit(i as u32);
                placer.assign_mask(outputs[i], &bit);
            }

            placer.assign_field(opcode_family_type_var, &family);
            placer.assign_u16(opcode_family_bitmask_var, &family_bits.truncate());
        };

        circuit.set_values(value_fn);
    }

    circuit.enforce_lookup_tuple_for_fixed_table(
        &[
            LookupInput::from(table_input_constraint),
            LookupInput::from(opcode_family_type_var),
            LookupInput::from(splitting_constraint),
        ],
        TableType::OpTypeBitmask,
        true, // we used lookup in the query above, so we record a relation,
              // but do not need to auto-generate multiplicity counting function
    );

    // We need to range-check `opcode_family_bitmask_var` coarsely (8 bits or 16 bits, just to avoid overflowing a field)
    assert!(F::CHAR_BITS - 1 >= NUM_DEFAULT_DECODER_BITS + 16);

    (is_invalid, opcode_formats_except_r)
}
