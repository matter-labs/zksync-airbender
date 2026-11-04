pub mod decode_optimized_must_handle_csr;

use super::*;
use crate::devices::risc_v_types::NUM_INSTRUCTION_TYPES;

// We will base our decoder on the following observations and limitations for now:
// - unsupported instructions == unsatisfiable circuit
// - UNIMP instruction (csrrw x0, cycle, x0) is checked before decoding by the main circuit, and leads to being unsatisiable
// - any CSR number check is done in CSRRW instruction, even though we can check 7-bit combinations
// - CSR writes are no-op effectively, as we only support non-determinism CSR and delegation via special CSR indexes
// - that means that CSRRWI and similar options do not need to be supported yet
// in this case we just need
// - 1 boolean to mark apriori-invalid instruction
// - 6 bits to decode instruction type, so we can assemble the immediate
// - immediates are always decoded as operand-2 for purposes of bit decomposition and sign splitting
// - some number of bits to decode "major" family type
// - some number of bits that are like a "scratch space" and each instruction interprets them as it wants

pub const NUM_INSTRUCTION_TYPES_IN_DECODE_BITS: usize = NUM_INSTRUCTION_TYPES;

pub struct DecoderInput<F: PrimeField> {
    pub instruction: Register<F>,
}

// pub struct BaseDecoder;

// pub struct BaseDecoderOutput<F: PrimeField> {
//     // pub opcode: Num<F>,
//     pub rd: Num<F>,
//     pub rs1: Num<F>,
//     pub rs2: Num<F>,

//     pub imm: Register<F>,

//     pub funct3: Num<F>,
//     pub funct7: Num<F>,
//     pub funct12: Constraint<F>,
// }

// impl BaseDecoder {
//     pub fn decode<F: PrimeField, C: Circuit<F>>(
//         inputs: &DecoderInput<F>,
//         circuit: &mut C,
//         splitting: [usize; 2],
//     ) -> (
//         Boolean,
//         BaseDecoderOutput<F>,
//         [Boolean; NUM_INSTRUCTION_TYPES],
//         Vec<Boolean>,
//     ) {
//         // instruction set of variables: low: [15:0], high: [31:16]
//         // the most shredded instruction type is B-type (with additional splitting of rs_2, required for J-type):
//         // all other instruction types can be constructed from
//         // chunks of split instruction are:
//         // opcode [6:0], imm11: [7], imm[4-1]: [11:8], func3: [14:12], rs1: [19:15],
//         // rs2_low: [20], rs2_high: [24:21], imm[10-5]: [30:25], imm12: [31]
//         // rs1 crosses the border of register, so we need to additionally split it as
//         // rs1_low: [15], rs1_high: [16-19]

//         // NOTE: we DO range check opcode (7 bits) so we can later on use a single table lookup to get all our opcode properties

//         let opcode = Num::Var(circuit.add_variable());
//         let imm11 = circuit.add_boolean_variable();
//         let imm4_1 = Num::Var(circuit.add_variable());
//         let funct3 = Num::Var(circuit.add_variable());
//         let rs1_low = circuit.add_boolean_variable();
//         let rs1_high = Num::Var(circuit.add_variable());
//         let rs2_low = circuit.add_boolean_variable();
//         let rs2_high = Num::Var(circuit.add_variable());
//         let imm10_5 = Num::Var(circuit.add_variable());
//         let sign_bit = circuit.add_boolean_variable();

//         // here we will have to write value-fn manually

//         //setting values
//         let value_fn = move |placer: &mut CS::WitnessPlacer| {
//             debug_assert!(constants.is_empty());

//             let instruction = Register::get_u32_from_source(input, 0);

//             use crate::utils::*;

//             let opcode = instruction & setbits(7);
//             let imm11 = (instruction >> 7) & setbits(1);
//             let imm4_1 = (instruction >> 8) & setbits(4);
//             let funct3 = (instruction >> 12) & setbits(3);
//             let rs1_low = (instruction >> 15) & setbits(1);
//             let rs1_high = (instruction >> 16) & setbits(4);
//             let rs2_low = (instruction >> 20) & setbits(1);
//             let rs2_high = (instruction >> 21) & setbits(4);
//             let imm10_5 = (instruction >> 25) & setbits(6);
//             let sign_bit = instruction >> 31;

//             output[0] = PrimeField::from_u64(opcode as u64).unwrap();
//             output[1] = PrimeField::from_u64(imm11 as u64).unwrap();
//             output[2] = PrimeField::from_u64(imm4_1 as u64).unwrap();
//             output[3] = PrimeField::from_u64(funct3 as u64).unwrap();
//             output[4] = PrimeField::from_u64(rs1_low as u64).unwrap();
//             output[5] = PrimeField::from_u64(rs1_high as u64).unwrap();
//             output[6] = PrimeField::from_u64(rs2_low as u64).unwrap();
//             output[7] = PrimeField::from_u64(rs2_high as u64).unwrap();
//             output[8] = PrimeField::from_u64(imm10_5 as u64).unwrap();
//             output[9] = PrimeField::from_u64(sign_bit as u64).unwrap();
//         };
//         let outputs = [
//             opcode.get_variable(),
//             imm11.get_variable().unwrap(),
//             imm4_1.get_variable(),
//             funct3.get_variable(),
//             rs1_low.get_variable().unwrap(),
//             rs1_high.get_variable(),
//             rs2_low.get_variable().unwrap(),
//             rs2_high.get_variable(),
//             imm10_5.get_variable(),
//             sign_bit.get_variable().unwrap(),
//         ];
//         let input = inputs.instruction.0.map(|x| x.get_variable());
//         circuit.set_values(&input, &outputs, &[], TableType::ZeroEntry, value_fn);

//         // constraint range checks
//         let _ = circuit.get_variables_from_lookup_constrained::<3, 0>(
//             &[
//                 imm4_1.get_variable(),
//                 rs1_high.get_variable(),
//                 rs2_high.get_variable(),
//             ]
//             .map(|el| LookupInput::from(el)),
//             TableType::QuickDecodeDecompositionCheck4x4x4,
//         );
//         let _ = circuit.get_variables_from_lookup_constrained::<3, 0>(
//             &[
//                 opcode.get_variable(),
//                 funct3.get_variable(),
//                 imm10_5.get_variable(),
//             ]
//             .map(|el| LookupInput::from(el)),
//             TableType::QuickDecodeDecompositionCheck7x3x6,
//         );

//         // insn_low <=> opcode [6:0], imm11: [7], imm[4-1]: [11:8], func3: [14:12], rs1_low: [15],
//         let [low_insn, high_insn] = inputs.instruction.get_terms();
//         let low_split_constraint = {
//             low_insn
//                 - Term::from(opcode)
//                 - Term::from(1 << 7) * Term::from(imm11)
//                 - Term::from(1 << 8) * Term::from(imm4_1)
//                 - Term::from(1 << 12) * Term::from(funct3)
//                 - Term::from(rs1_low) * Term::from(1 << 15)
//         };
//         // insn_high <=> rs1_high: [19:16], rs2: [24:20], imm[10-5]: [30:25], imm12: [31]
//         let high_split_constraint = {
//             high_insn
//                 - Term::from(rs1_high)
//                 - Term::from(rs2_low) * Term::from(1 << 4)
//                 - Term::from(rs2_high) * Term::from(1 << 5)
//                 - Term::from(imm10_5) * Term::from(1 << 9)
//                 - Term::from(sign_bit) * Term::from(1 << 15)
//         };

//         circuit.add_constraint_allow_explicit_linear(low_split_constraint);
//         circuit.add_constraint_allow_explicit_linear(high_split_constraint);

//         // we can already get some parts
//         let rd = Num::Var(circuit.add_variable_from_constraint_allow_explicit_linear(
//             Term::from(imm4_1) * Term::from(1 << 1) + Term::from(imm11),
//         ));
//         let rs1 = Num::Var(circuit.add_variable_from_constraint_allow_explicit_linear(
//             Term::from(rs1_high) * Term::from(1 << 1) + Term::from(rs1_low),
//         ));
//         let rs2 = Num::Var(circuit.add_variable_from_constraint_allow_explicit_linear(
//             Term::from(rs2_high) * Term::from(1 << 1) + Term::from(rs2_low),
//         ));

//         // funct_7 = sign_bit[1] | imm_10-5[6]
//         let funct7 = Num::Var(circuit.add_variable_from_constraint_allow_explicit_linear(
//             Term::from(sign_bit) * Term::from(1 << 6) + Term::from(imm10_5),
//         ));

//         // now we can feed [opcode || funct_3 || funct 7] (all are range checked, so concatenation IS allowed)
//         // to get basic bitmask that will tell whether the opcode is valid or not, and provide aux properties
//         // like belonging to opcode family, etc
//         let (
//             is_invalid,
//             [r_insn, i_insn, s_insn, b_insn, u_insn, j_insn],
//             opcode_type_and_variant_bits,
//         ) = Self::opcode_lookup::<F, C>(opcode, funct3, funct7, circuit, splitting);

//         // now we need to construct the right constant from different constant chunks
//         // the actual constant is dependent on the opcode type:
//         // -------------------------------------------------------------------------------------------------------|
//         // |       chunk5[31-16]    |   chunk4[15-12]   | chunk3[11] | chunk2[10-5] | chunk1[4-1] | chunk0[0] |   |
//         // |========================|===================|============|==============|=============|===========|===|
//         // |         sign_bit       |    sign_bit       |  sign_bit  |   imm[10-5]  |   rs2_high  |  rs2_low  | I |
//         // |------------------------|-------------------|------------|--------------|-------------|-----------|---|
//         // |         sign_bit       |    sign_bit       |  sign_bit  |   imm[10-5]  |   imm4_1    |   imm11   | S |
//         // |------------------------|-------------------|------------|--------------|-------------|-----------|---|
//         // |         sign_bit       |    sign_bit       |   imm11    |   imm[10-5]  |   imm4_1    |     0     | B |
//         // |------------------------|-------------------|------------|--------------|-------------|-----------|---|
//         // |         insn_high      | rs1_low || funct3 |      0     |      0       |      0      |     0     | U |
//         // |------------------------|-------------------|------------|--------------|-------------|-----------|---|
//         // |  sign_bit || rs1_high  | rs1_low || funct3 |  rs2_low   |   imm[10-5]  |   rs2_high  |     0     | J |
//         // |========================|===================|============|==============|=============|===========|===|
//         // hence:
//         // chunk0 = i_insn * rs2_low +  s_insn * imm11
//         // chunk1 = (i_insn + j_insn) * rs2_high + (s_insn + b_insn) * imm4_1
//         // chunk2 = (1 - u_insn) * imm10_5
//         // chunk3 = (i_insn + s_insn) * sign_bit + b_insn * imm11 + j_insn * rs2_low
//         // chunk4 = (i_insn + s_insn + b_insn) * sign_bit * 0b1111 + (u_insn + j_insn) * (rs1_low << 3 + funct3)
//         // chunk5 = {
//         //      j_insn * (sign_bit * 0xfff0 + rs1_high) + u_insn * insn_high +
//         //      (1 - j_insn - b_insn) * sign_bit * 0xffff
//         // }

//         // chunks 0..4 are used for linear constraint later on to form imm_low
//         let chunks_defining_constraints: [Constraint<F>; 5] = [
//             // 0
//             Term::from(i_insn) * Term::from(rs2_low) + Term::from(s_insn) * Term::from(imm11),
//             // 1
//             (Term::from(i_insn) + Term::from(j_insn)) * Term::from(rs2_high)
//                 + (Term::from(s_insn) + Term::from(b_insn)) * Term::from(imm4_1),
//             // 2
//             (Term::from(1) - Term::from(u_insn)) * Term::from(imm10_5),
//             // 3
//             (Term::from(i_insn) + Term::from(s_insn)) * Term::from(sign_bit)
//                 + Term::from(b_insn) * Term::from(imm11)
//                 + Term::from(j_insn) * Term::from(rs2_low),
//             // 4
//             (Term::from(i_insn) + Term::from(s_insn) + Term::from(b_insn))
//                 * Term::from(sign_bit)
//                 * Term::from(0b1111u64)
//                 + (Term::from(u_insn) + Term::from(j_insn))
//                     * (Term::from(rs1_low) * Term::from(1 << 3) + (Term::from(funct3))),
//         ];

//         let [chunk0, chunk1, chunk2, chunk3, chunk4] = chunks_defining_constraints;

//         let imm_low = Num::Var(circuit.add_variable_from_constraint(
//             chunk0
//                 + chunk1 * Term::from(1 << 1)
//                 + chunk2 * Term::from(1 << 5)
//                 + chunk3 * Term::from(1 << 11)
//                 + chunk4 * Term::from(1 << 12),
//         ));

//         // chunk 5 is just higher part of the immediate
//         let imm_high = Num::Var(circuit.add_variable_from_constraint(
//             Term::from(j_insn) * (Term::from(sign_bit) * Term::from(0xfff0) + Term::from(rs1_high))
//                 + Term::from(u_insn) * Term::from(inputs.instruction.0[1])
//                 + (Term::from(1) - Term::from(j_insn) - Term::from(u_insn))
//                     * Term::from(sign_bit)
//                     * Term::from(0xffff),
//         ));

//         let imm = Register([imm_low, imm_high]);

//         // funct_12 is used only by:
//         // SYSTEM CSR - there we can use single table lookup to validate if 12-bit index is valid and trap (along with R/W info if we want)
//         // SYSTEM ECALL/EBREAK - again, we can check validity in there, because if it's not a valid 12-bit index we will trap anyway, but with different code

//         // funct_12 = sign_bit[1] | imm_10-5[6] | rs2_high[4] | rs2_low[1]
//         let funct12 =
//             Constraint::empty() + Term::from(rs2) + Term::from(funct7) * Term::from(1 << 5);

//         let decoder_output = BaseDecoderOutput {
//             // opcode,
//             rd,
//             rs1,
//             rs2,
//             funct3,
//             funct7,
//             funct12,
//             imm,
//         };

//         (
//             is_invalid,
//             decoder_output,
//             [r_insn, i_insn, s_insn, b_insn, u_insn, j_insn],
//             opcode_type_and_variant_bits,
//         )
//     }

//     #[track_caller]
//     fn opcode_lookup<F: PrimeField, C: Circuit<F>>(
//         opcode: Num<F>,
//         funct3: Num<F>,
//         funct7: Num<F>,
//         circuit: &mut C,
//         splitting: [usize; 2],
//     ) -> (
//         Boolean,
//         [Boolean; NUM_INSTRUCTION_TYPES_IN_DECODE_BITS],
//         Vec<Boolean>,
//     ) {
//         // let table_input: Num<F> =
//         //     Num::Var(circuit.add_variable_from_constraint_allow_explicit_linear(
//         //         ,
//         //     ));
//         let table_input_constraint = Constraint::empty()
//             + Term::from(opcode)
//             + Term::from(funct3) * Term::from(1 << 7)
//             + Term::from(funct7) * Term::from(1 << (7 + 3));
//         let [first_word, second_word] = circuit.get_variables_from_lookup_constrained::<1, 2>(
//             &[LookupInput::from(table_input_constraint)],
//             TableType::OpTypeBitmask,
//         );

//         let mut all_bits =
//             Boolean::split_into_bitmask_vec(Num::Var(first_word), circuit, splitting[0]);

//         if splitting[1] > 0 {
//             let second_word =
//                 Boolean::split_into_bitmask_vec(Num::Var(second_word), circuit, splitting[1]);

//             all_bits.extend(second_word);
//         }

//         assert!(all_bits.len() >= 1 + NUM_INSTRUCTION_TYPES);

//         let is_invalid = all_bits[0];

//         let format_bits: [Boolean; NUM_INSTRUCTION_TYPES_IN_DECODE_BITS] =
//             all_bits[1..][..NUM_INSTRUCTION_TYPES].try_into().unwrap();
//         let other_bits = all_bits[1..][NUM_INSTRUCTION_TYPES_IN_DECODE_BITS..].to_vec();

//         (is_invalid, format_bits, other_bits)
//     }

//     pub fn select_src1_and_src2_values<F: PrimeField, C: Circuit<F>>(
//         cs: &mut C,
//         opcode_format_bits: &[Boolean; NUM_INSTRUCTION_TYPES],
//         rs1_value: Register<F>,
//         decoded_imm: Register<F>,
//         rs2_value: Register<F>,
//     ) -> (Register<F>, Register<F>, Boolean) {
//         let [r_insn, i_insn, s_insn, b_insn, u_insn, j_insn] = *opcode_format_bits;
//         // R, I, S, B instruction formats use RS1 value as the first operand,
//         // otherwise we do not need to put anything anything there - U can access IMM from the decoder directly,
//         // same as J format
//         let src1 = Register::choose_from_orthogonal_variants(
//             cs,
//             &[r_insn, i_insn, s_insn, b_insn],
//             &[rs1_value, rs1_value, rs1_value, rs1_value],
//         );
//         // R, S and B use RS2 value as second operand, otherwise - I format supplies immediate
//         // We do R/I mixing here to save on register value decomposition for instructions
//         // such as ADD/ADDI or XOR/XORI
//         let src2 = Register::choose_from_orthogonal_variants(
//             cs,
//             &[r_insn, i_insn, s_insn, b_insn],
//             &[rs2_value, decoded_imm, rs2_value, rs2_value],
//         );

//         // opcode formats are orthogonal flags, so a boolean to update RD is just a linear combination
//         let update_rd = cs.add_variable_from_constraint_allow_explicit_linear(
//             Constraint::from(r_insn.get_variable().unwrap())
//                 + Constraint::from(i_insn.get_variable().unwrap())
//                 + Constraint::from(j_insn.get_variable().unwrap())
//                 + Constraint::from(u_insn.get_variable().unwrap()),
//         );

//         (src1, src2, Boolean::Is(update_rd))
//     }
// }
