use super::*;
use crate::cs::circuit::*;
use crate::cs::witness_placer::WitnessComputationCore;
use crate::cs::witness_placer::WitnessComputationalInteger;
use crate::cs::witness_placer::WitnessComputationalU16;
use crate::cs::witness_placer::WitnessComputationalU32;
use crate::cs::witness_placer::WitnessPlacer;
use crate::one_row_compiler::LookupInput;
use crate::types::Boolean;
use crate::types::Num;

use core::array::from_fn;
use crate::cs::witness_placer::WitnessTypeSet;
use crate::cs::witness_placer::WitnessComputationalU8;
use crate::cs::witness_placer::WitnessComputationalField;
use crate::cs::witness_placer::WitnessMask;

// INFO:
// - 5 "precompiles" (ops) packed into one circuit
// - max of 5 u64 bitwise operations
// - max of 6 u64 R/W memory accesses
// - repeatedly called (1 keccak = 504 such calls + few extra cycles)

// ABI:
// - 1 register (x10) for state pointer (aligned s.t. state[29] does not overflow low 16 bits)
// - 1 register (x11.high) for control info (precompile bitmask || i bitmask || round)

// TABLES:
// - one table for special xor with round constant
// - one table normal xor with rotation constant
// - one table for andn
// - two tables for extraction of 6 5-bit indexes (could be better)

// CIRCUIT:
// to keep it simple we will not hyper optimise without OptCtx for now
// - get state ptr + control param with 2 mem. accesses
// - extract precompile bitmask flags, to make using OptCtx easy
// - extract i bitmask bits, to make rotations cheap (b0..b7 become linear combination)
// - extract the 6 indices to fixed positions -> get 6 u64 R/W (word1..word6) inputs + create outputs
// - dynamic logic across precompiles is cheaply encoded using OptCtx with precompile flags
// - the precompile with round constant is managed through special xor table
// - the precompiles with xor+rotation receive rotation const + rotation shift amt. encoded using i bits

// TODO: as it currently stands, delegation prover only supports batched contiguous mem. accesses
//       because it is encoded as constant offset constraints
//       so, it will need to be amended to support variable constraints
// TODO: we need to add value_fn everywhere (before constraints are evaluated)

#[derive(Copy,Clone)]
struct LongRegister<F: PrimeField>{
    low32: Register<F>,
    high32: Register<F>
}
impl<F: PrimeField> LongRegister<F>{
    fn new(cs: &mut impl Circuit<F>) -> LongRegister<F> {
        let low32_vars = from_fn(|_| cs.add_variable());
        let high32_vars = from_fn(|_| cs.add_variable());
        LongRegister { 
            low32: Register(low32_vars.map(Num::Var)), 
            high32: Register(high32_vars.map(Num::Var)) 
        }
    }
}

struct LongRegisterDecomposition<F: PrimeField>{
    low32: [Num<F>; 4],
    high32: [Num<F>; 4]
}
impl<F: PrimeField> LongRegisterDecomposition<F>{
    fn new(cs: &mut impl Circuit<F>) -> LongRegisterDecomposition<F> {
        let low32_vars = from_fn(|_| cs.add_variable());
        let high32_vars = from_fn(|_| cs.add_variable());
        LongRegisterDecomposition{
            low32: low32_vars.map(Num::Var),
            high32: high32_vars.map(Num::Var),
        }
    }
    fn complete_composition(&self) -> [Constraint<F>; 4] {
        [
            Constraint::from(self.low32[0]) + Term::from(1<<8)*Term::from(self.low32[1]),
            Constraint::from(self.low32[2]) + Term::from(1<<8)*Term::from(self.low32[3]),
            Constraint::from(self.high32[0]) + Term::from(1<<8)*Term::from(self.high32[1]),
            Constraint::from(self.high32[2]) + Term::from(1<<8)*Term::from(self.high32[3]),
        ]
    }
}
struct LongRegisterRotation<F: PrimeField>{
    chunks_u16: [[Num<F>; 2]; 4],      // output of splitting rotation across u16 boundaries
}
impl<F: PrimeField> LongRegisterRotation<F>{
    fn new(cs: &mut impl Circuit<F>) -> LongRegisterRotation<F> {
        let vars = from_fn(|_| from_fn(|_| Num::Var(cs.add_variable())));
        LongRegisterRotation { chunks_u16: vars }
    }
    fn complete_rotation(&self, u16_boundary_flags: [Constraint<F>; 4]) -> [Constraint<F>; 4] {
        debug_assert!(u16_boundary_flags.iter().all(|x| x.degree()<=1));
        let [is_rot_lt16, is_rot_lt32, is_rot_lt48, is_rot_lt64] = u16_boundary_flags; // orthogonal flags
        // gotta consider the chunks separately
        // each chunk's base ("_right") takes a small rotational component ("_left") from the "previous" chunk
        // no shift needed because shift is already applied by the rotl lookup table
        let [a, b, c, d] = {
            let [a_left, a_right] = self.chunks_u16[0];
            let [b_left, b_right] = self.chunks_u16[1];
            let [c_left, c_right] = self.chunks_u16[2];
            let [d_left, d_right] = self.chunks_u16[3];
            [
                Constraint::from(a_right) + Term::from(d_left),
                Constraint::from(b_right) + Term::from(a_left),
                Constraint::from(c_right) + Term::from(b_left),
                Constraint::from(d_right) + Term::from(c_left)
            ]
        };
        // IF is_rot_lt16 THEN rotation is  0..16, SO take the chunk that fits that exact spot
        // IF is_rot_lt32 THEN rotation is 16..32, SO take the chunk that 1 spot over
        // IF is_rot_lt48 THEN rotation is 32..48, SO take the chunk that 2 spots over
        // IF is_rot_lt64 THEN rotation is 48..64, SO take the chunk that 3 spots over
        let low32_low16 = is_rot_lt16.clone()*a.clone() + is_rot_lt32.clone()*d.clone() + is_rot_lt48.clone()*c.clone() + is_rot_lt64.clone()*b.clone();
        let low32_high16 = is_rot_lt16.clone()*b.clone() + is_rot_lt32.clone()*a.clone() + is_rot_lt48.clone()*d.clone() + is_rot_lt64.clone()*c.clone();
        let high32_low16 = is_rot_lt16.clone()*c.clone() + is_rot_lt32.clone()*b.clone() + is_rot_lt48.clone()*a.clone() + is_rot_lt64.clone()*d.clone();
        let high32_high16 = is_rot_lt16*d + is_rot_lt32*c + is_rot_lt48*b + is_rot_lt64*a;
        [low32_low16, low32_high16, high32_low16, high32_high16]
    }
}


pub fn all_table_types() -> Vec<TableType> {
    vec![
        TableType::KeccakPermutationIndices12,
        TableType::KeccakPermutationIndices34,
        TableType::KeccakPermutationIndices56,
        TableType::Xor,
        TableType::XorSpecialIota,
        TableType::AndN,
        TableType::RotL,
    ]
}

pub fn keccak_special5_delegation_circuit_create_table_driver<F: PrimeField>(
) -> TableDriver<F> {
    let mut table_driver = TableDriver::new();
    for el in all_table_types() {
        table_driver.materialize_table(el);
    }

    table_driver
}

pub fn materialize_tables_into_cs<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    for el in all_table_types() {
        cs.materialize_table(el);
    }
}

pub fn define_keccak_special5_delegation_circuit<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    // add tables
    materialize_tables_into_cs(cs);

    // the only convention we must eventually satisfy is that if we do NOT process delegation request,
    // then all memory writes in ABI must be 0s
    // this is handled automatically by custom stage3 constraint to mask all mem accesses
    // then you just need to ensure that all 0 execute flags does not break/unsatisfy the circuit
    // therefore: you can safely ignore this variable, but the circuit author must be careful
    let _execute = cs.process_delegation_request();

    // STEP1: process all memory accesses
    let control = {
        let x11_request = RegisterAccessRequest {
            register_index: 11,
            register_write: false,
            indirects_alignment_log2: 0, // no indirects, contains explicit control value
            indirect_accesses: vec![],
        };
        let x11_and_indirects = cs.create_register_and_indirect_memory_accesses(x11_request);
        assert!(x11_and_indirects.indirect_accesses.is_empty());
        let RegisterAccessType::Read { read_value: control_reg } = x11_and_indirects.register_access else {unreachable!()};
        control_reg[1] // only the high 16 bits contain control info (to accomodate for LUI)
    };
    // TODO: state_indices are not currently being used
    let state_indexes = {
        let [s1, s2] = cs.get_variables_from_lookup_constrained(&[LookupInput::from(control)], TableType::KeccakPermutationIndices12);
        let [s3, s4] = cs.get_variables_from_lookup_constrained(&[LookupInput::from(control)], TableType::KeccakPermutationIndices34);
        let [s5, s6] = cs.get_variables_from_lookup_constrained(&[LookupInput::from(control)], TableType::KeccakPermutationIndices56);
        [s1, s2, s3, s4, s5, s6]
    };
    // TODO: is it ok that indirects_alignment_log2 and indirect_accesses.len() mismatch?
    let (state_inputs, state_outputs) = {
        let x10_request = RegisterAccessRequest {
            register_index: 10,
            register_write: true,
            indirects_alignment_log2: 8, // 256 bytes: 25 u64 state + 5 u64 scratch = 240 bytes
            indirect_accesses: vec![true; 12], // we just r/w 6 u64 words
        };
        let x10_and_indirects = cs.create_register_and_indirect_memory_accesses(x10_request);
        assert_eq!(x10_and_indirects.indirect_accesses.len(), 12);
        let mut state_inputs = [LongRegister{low32: Register([Num::Constant(F::ZERO); 2]), high32: Register([Num::Constant(F::ZERO); 2])}; 6];
        let mut state_outputs = [LongRegister{low32: Register([Num::Constant(F::ZERO); 2]), high32: Register([Num::Constant(F::ZERO); 2])}; 6];
        for i in 0..6 {
            let IndirectAccessType::Write { read_value: in_low, write_value: out_low } = x10_and_indirects.indirect_accesses[i*2] else {unreachable!()};
            let IndirectAccessType::Write { read_value: in_high, write_value: out_high } = x10_and_indirects.indirect_accesses[i*2 + 1] else {unreachable!()};
            state_inputs[i] = LongRegister{low32: Register(in_low.map(Num::Var)), high32: Register(in_high.map(Num::Var))};
            state_outputs[i] = LongRegister{low32: Register(out_low.map(Num::Var)), high32: Register(out_high.map(Num::Var))};
        }
        (state_inputs, state_outputs)
    };
    // TODO: not 100% sure about this optim...
    let (precompile_bitmask, iter_bitmask, round) = {
        let bitmask: [Boolean; 10] = from_fn(|_| cs.add_boolean_variable());
        let round = {
            let mut round = Constraint::from(control);
            for i in 0..10 {
                round = round - Term::from(1<<i)*Term::from(bitmask[i]);
            }
            round.scale(F::from_u64_unchecked(1<<10).inverse().unwrap());
            round
        };
        let out = cs.add_variable_with_range_check(16);

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let control_value = placer.get_u16(control);
            let bitmask_values: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask; 10] = from_fn(|i| control_value.get_bit(i as u32));
            for i in 0..10 {
                placer.assign_mask(bitmask[i].get_variable().unwrap(), &bitmask_values[i]);
            }
            let out_value = {
                let two5_value = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(1<<5);
                let round_value = control_value.shr(10);
                two5_value.overflowing_sub(&round_value).0
            };
            placer.assign_u16(out.get_variable(), &out_value);
        };
        cs.set_values(value_fn);

        cs.add_constraint_allow_explicit_linear((Constraint::from(1<<5) - round.clone()) - Term::from(out));
        (bitmask[..5].try_into().unwrap(), bitmask[5..].try_into().unwrap(), round)
    };
    let [is_iota_columnxor, is_columnmix, is_theta_rho, is_chi1, is_chi2] = precompile_bitmask;
    let [is_iter0, is_iter1, is_iter2, is_iter3, is_iter4] = iter_bitmask;
    let [is_theta_rho_iter0, is_theta_rho_iter1, is_theta_rho_iter2, is_theta_rho_iter3, is_theta_rho_iter4] =
        [Boolean::and(&is_theta_rho, &is_iter0, cs), Boolean::and(&is_theta_rho, &is_iter1, cs), Boolean::and(&is_theta_rho, &is_iter2, cs), Boolean::and(&is_theta_rho, &is_iter3, cs), Boolean::and(&is_theta_rho, &is_iter4, cs)];

    // need an easy way to identify positions later on during manual routing constraints...
    let [[p0_idx0, p0_idx5, p0_idx10, p0_idx15, p0_idx20, _p0_idcol],
        [p1_25, p1_26, p1_27, p1_28, p1_29, p1_0],
        [p2_idx0, p2_idx5, p2_idx10, p2_idx15, p2_idx20, p2_idcol],
        [p3_idx1, p3_idx2, p3_idx3, p3_idx4, _p3_25, _p3_26],
        [p4_idx0, p4_idx3, p4_idx4, p4_25, p4_26, _p4_27]
    ] = [state_inputs; 5];
    let [[p0_idx0_new, p0_idx5_new, p0_idx10_new, p0_idx15_new, p0_idx20_new, p0_idcol_new],
        [p1_25_new, p1_26_new, p1_27_new, p1_28_new, p1_29_new, p1_0_new],
        [p2_idx0_new, p2_idx5_new, p2_idx10_new, p2_idx15_new, p2_idx20_new, p2_idcol_new],
        [p3_idx1_new, p3_idx2_new, p3_idx3_new, p3_idx4_new, p3_25_new, p3_26_new],
        [p4_idx0_new, p4_idx3_new, p4_idx4_new, p4_25_new, p4_26_new, p4_27_new]
    ] = [state_outputs; 5];

    // TODO: not sure if 8bit mask is necessary (probably safer like this..)
    let p0_round_constant_control_reg = {
        let round_if_iter0 = cs.add_variable_from_constraint(round*Term::from(is_iter0));
        let chunks_u8: [Constraint<F>; 8] = from_fn(|i| Constraint::from(round_if_iter0) + Term::from(1<<5)*Term::from(i as u64));
        let chunks_u16: [Num<F>; 4] = from_fn(|i| cs.add_variable_from_constraint_allow_explicit_linear(chunks_u8[i*2].clone() + Term::from(1<<8)*chunks_u8[i*2+1].clone())).map(Num::Var);
        LongRegister{
            low32: Register([chunks_u16[0], chunks_u16[1]]),
            high32: Register([chunks_u16[2], chunks_u16[3]])
        }
    };
    let state_tmps: [LongRegister<F>; 3] = from_fn(|_| LongRegister::new(cs));
    let [p0_tmp1, p0_tmp2, p0_tmp3] = state_tmps;
    let [p3_tmp1, p3_tmp2, _] = state_tmps;
    let [p4_tmp1, p4_tmp2, _] = state_tmps;

    // UGLY WORKAROUND: IN ORDER TO ALLOW USING CONDITIONAL ASSIGNMENT
    cs.set_values(move |placer: &mut CS::WitnessPlacer| {
        let u32_zero = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
        let u1_false = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
        placer.conditionally_assign_u32(p0_tmp3.low32.0.map(|x| x.get_variable()), &u1_false, &u32_zero);
        placer.conditionally_assign_u32(p0_tmp3.high32.0.map(|x| x.get_variable()), &u1_false, &u32_zero);
    });

    // WORKAROUND: THE SECOND PRECOMPILE CONDITIONALLY NEEDS OUTPUTS TO BE ASSIGNED BEFOREHAND
    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let rotl1 = |u64_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32; 2]| {
            let low32_value = u64_value[0].shl(1).overflowing_add(&u64_value[1].shr(31)).0;
            let high32_value = u64_value[1].shl(1).overflowing_add(&u64_value[0].shr(31)).0;
            [low32_value, high32_value]
        };
        let xor = |placer: &mut CS::WitnessPlacer, a_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32; 2], b_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32; 2]| {
            let xoru8 = |placer: &mut CS::WitnessPlacer, au8_value: &<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8, bu8_value: &<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8| {
                let au8_field = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(au8_value.widen().widen());
                let bu8_field = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(bu8_value.widen().widen());
                let table_id = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(TableType::Xor.to_table_id() as u16);
                let [outu8_field] = placer.lookup(&[au8_field, bu8_field], &table_id);
                let outu8_value = outu8_field.as_integer().truncate().truncate();
                outu8_value
            };
            let tou8 = |u64_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32; 2]| {
                let zerou8 = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8::constant(0);
                let mut chunks: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8; 8] = from_fn(|_| zerou8.clone());
                chunks[0] = u64_value[0].truncate().truncate();
                chunks[1] = u64_value[0].truncate().shr(8).truncate();
                chunks[2] = u64_value[0].shr(16).truncate().truncate();
                chunks[3] = u64_value[0].shr(16).truncate().shr(8).truncate();
                chunks[4] = u64_value[1].truncate().truncate();
                chunks[5] = u64_value[1].truncate().shr(8).truncate();
                chunks[6] = u64_value[1].shr(16).truncate().truncate();
                chunks[7] = u64_value[1].shr(16).truncate().shr(8).truncate();
                chunks
            };
            let fromu8 = |u8_values: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8; 8]| {
                let low32_low16 = u8_values[0].widen().overflowing_add(&u8_values[1].widen().shl(8)).0;
                let low32_high16 = u8_values[2].widen().overflowing_add(&u8_values[3].widen().shl(8)).0;
                let high32_low16 = u8_values[4].widen().overflowing_add(&u8_values[5].widen().shl(8)).0;
                let high32_high16 = u8_values[6].widen().overflowing_add(&u8_values[7].widen().shl(8)).0;
                let low32 = low32_low16.widen().overflowing_add(&low32_high16.widen().shl(16)).0;
                let high32 = high32_low16.widen().overflowing_add(&high32_high16.widen().shl(16)).0;
                [low32, high32]
            };
            let au8_values = tou8(a_value);
            let bu8_values = tou8(b_value);
            let mut outu8_values: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8; 8] = from_fn(|_| <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8::constant(0));
            for i in 0..8 {
                outu8_values[i] = xoru8(placer, &au8_values[i], &bu8_values[i]);
            }
            fromu8(outu8_values)
        };
        let is_columnmix_value = placer.get_boolean(is_columnmix.get_variable().unwrap());
        let p1_25_value = [placer.get_u32_from_u16_parts(p1_25.low32.0.map(|x| x.get_variable())), placer.get_u32_from_u16_parts(p1_25.high32.0.map(|x| x.get_variable()))];
        let p1_26_value = [placer.get_u32_from_u16_parts(p1_26.low32.0.map(|x| x.get_variable())), placer.get_u32_from_u16_parts(p1_26.high32.0.map(|x| x.get_variable()))];
        let p1_27_value = [placer.get_u32_from_u16_parts(p1_27.low32.0.map(|x| x.get_variable())), placer.get_u32_from_u16_parts(p1_27.high32.0.map(|x| x.get_variable()))];
        let p1_28_value = [placer.get_u32_from_u16_parts(p1_28.low32.0.map(|x| x.get_variable())), placer.get_u32_from_u16_parts(p1_28.high32.0.map(|x| x.get_variable()))];
        let p1_29_value = [placer.get_u32_from_u16_parts(p1_29.low32.0.map(|x| x.get_variable())), placer.get_u32_from_u16_parts(p1_29.high32.0.map(|x| x.get_variable()))];
        let p1_25_new_value = xor(placer, &p1_25_value, &rotl1(&p1_27_value));
        let p1_26_new_value = xor(placer, &p1_26_value, &rotl1(&p1_28_value));
        let p1_27_new_value = xor(placer, &p1_27_value, &rotl1(&p1_29_value));
        let p1_28_new_value = xor(placer, &p1_28_value, &rotl1(&p1_25_value));
        let p1_29_new_value = xor(placer, &p1_26_value, &rotl1(&p1_26_value));
        placer.conditionally_assign_u32(p1_25_new.low32.0.map(|x| x.get_variable()), &is_columnmix_value, &p1_25_new_value[0]);
        placer.conditionally_assign_u32(p1_25_new.high32.0.map(|x| x.get_variable()), &is_columnmix_value, &p1_25_new_value[1]);
        
        placer.conditionally_assign_u32(p1_26_new.low32.0.map(|x| x.get_variable()), &is_columnmix_value, &p1_26_new_value[0]);
        placer.conditionally_assign_u32(p1_26_new.high32.0.map(|x| x.get_variable()), &is_columnmix_value, &p1_26_new_value[1]);
        
        placer.conditionally_assign_u32(p1_27_new.low32.0.map(|x| x.get_variable()), &is_columnmix_value, &p1_27_new_value[0]);
        placer.conditionally_assign_u32(p1_27_new.high32.0.map(|x| x.get_variable()), &is_columnmix_value, &p1_27_new_value[1]);
        
        placer.conditionally_assign_u32(p1_28_new.low32.0.map(|x| x.get_variable()), &is_columnmix_value, &p1_28_new_value[0]);
        placer.conditionally_assign_u32(p1_28_new.high32.0.map(|x| x.get_variable()), &is_columnmix_value, &p1_28_new_value[1]);
        
        placer.conditionally_assign_u32(p1_29_new.low32.0.map(|x| x.get_variable()), &is_columnmix_value, &p1_29_new_value[0]);
        placer.conditionally_assign_u32(p1_29_new.high32.0.map(|x| x.get_variable()), &is_columnmix_value, &p1_29_new_value[1]);
    };
    cs.set_values(value_fn);

    // STEP2: WE PERFORM EQUIVALENT OF 5 XORS + ROTATION (a, b, c)
    let precompile_flags = [is_iota_columnxor, is_columnmix, is_theta_rho, is_chi1, is_chi2];
    let precompile_rotation_flags = [is_iota_columnxor, is_columnmix, is_theta_rho_iter0, is_theta_rho_iter1, is_theta_rho_iter2, is_theta_rho_iter3, is_theta_rho_iter4, is_chi1, is_chi2];
    // 1
    enforce_binop(cs, 
        precompile_flags, 
        [TableType::XorSpecialIota, TableType::Xor, TableType::Xor, TableType::AndN, TableType::AndN], 
        precompile_rotation_flags, 
        [0, 63, 0, 1, 62, 28, 27, 0, 0], 
        [
            (p0_idx0, p0_round_constant_control_reg, p0_idx0_new),
            (p1_25_new, p1_25, p1_27),
            (p2_idx0, p2_idcol, p2_idx0_new),
            (p3_idx1, p3_idx2, p3_25_new),
            (p4_idx4, p4_idx0, p4_tmp1)
        ]);
    // 2
    enforce_binop(cs, 
        precompile_flags, 
        [TableType::Xor, TableType::Xor, TableType::Xor, TableType::AndN, TableType::Xor], 
        precompile_rotation_flags, 
        [0, 63, 36, 44, 6, 55, 20, 0, 0], 
        [
            (p0_idx0_new, p0_idx5, p0_tmp1),
            (p1_27_new, p1_27, p1_29),
            (p2_idx5, p2_idcol, p2_idx5_new),
            (p3_idx2, p3_idx3, p3_tmp1),
            (p4_idx3, p4_tmp1, p4_idx3_new)
        ]);
    // 3
    enforce_binop(cs, 
        precompile_flags, 
        [TableType::Xor, TableType::Xor, TableType::Xor, TableType::Xor, TableType::AndN], 
        precompile_rotation_flags, 
        [0, 63, 3, 10, 43, 25, 39, 0, 0], 
        [
            (p0_tmp1, p0_idx10, p0_tmp2),
            (p1_29_new, p1_29, p1_26),
            (p2_idx10, p2_idcol, p2_idx10_new),
            (p3_idx1, p3_tmp1, p3_idx1_new),
            (p4_idx0, p4_26, p4_tmp2)
        ]);
    // 4
    enforce_binop(cs, 
        precompile_flags, 
        [TableType::Xor, TableType::Xor, TableType::Xor, TableType::AndN, TableType::Xor], 
        precompile_rotation_flags, 
        [0, 63, 41, 45, 15, 21, 8, 0, 0], 
        [
            (p0_tmp2, p0_idx15, p0_tmp3),
            (p1_26_new, p1_26, p1_28),
            (p2_idx15, p2_idcol, p2_idx15_new),
            (p3_idx3, p3_idx4, p3_tmp2),
            (p4_idx4, p4_tmp2, p4_idx4_new)
        ]);
    // 5
    enforce_binop(cs, 
        precompile_flags, 
        [TableType::Xor, TableType::Xor, TableType::Xor, TableType::Xor, TableType::Xor], 
        precompile_rotation_flags, 
        [0, 63, 18, 2, 61, 56, 14, 0, 0], 
        [
            (p0_tmp3, p0_idx20, p0_idcol_new),
            (p1_28_new, p1_28, p1_25),
            (p2_idx20, p2_idcol, p2_idx20_new),
            (p3_idx2, p3_tmp2, p3_idx2_new),
            (p4_idx0, p4_25, p4_idx0_new)
        ]);

    // WE ALSO CANNOT FORGET TO COPY OVER UNTOUCHED VALUES BACK TO THEIR RAM ARGUMENT WRITE-SET
    enforce_copies(cs, 
        precompile_flags, 
        [
            Box::leak(Box::new([(p0_idx5, p0_idx5_new), (p0_idx10, p0_idx10_new), (p0_idx15, p0_idx15_new), (p0_idx20, p0_idx20_new)])),
            Box::leak(Box::new([(p1_0, p1_0_new)])),
            Box::leak(Box::new([(p2_idcol, p2_idcol_new)])),
            Box::leak(Box::new([(p3_idx3, p3_idx3_new), (p3_idx4, p3_idx4_new), (p3_idx1, p3_26_new)])),
            Box::leak(Box::new([(p4_25, p4_25_new), (p4_26, p4_26_new), (p4_idx0, p4_27_new)]))
        ]);


    // let _binop1 = {
    //     let in1_u8 = LongRegisterDecomposition::new(cs);
    //     let in2_u8 = LongRegisterDecomposition::new(cs);
    //     let value_fn = "todo";
        
    //     // FIRST we perform the main binary op lookups
    //     let bin_out_u8 = {
    //         // TODO: move this out_u8 into lookup get variable...
    //         let out_u8 = LongRegisterDecomposition::new(cs);
    //         let id = cs.choose_from_orthogonal_variants(
    //             &[is_iota_columnxor, is_columnmix, is_theta_rho, is_chi1, is_chi2], 
    //             &[table_iotaxor, table_xor, table_xor, table_andn, table_andn]
    //         ).get_variable();
    //         let tuples = [
    //             [in1_u8.low32.0[0], in2_u8.low32.0[0], out_u8.low32.0[0]],
    //             [in1_u8.low32.0[1], in2_u8.low32.0[1], out_u8.low32.0[1]],
    //             [in1_u8.low32.0[2], in2_u8.low32.0[2], out_u8.low32.0[2]],
    //             [in1_u8.low32.0[3], in2_u8.low32.0[3], out_u8.low32.0[3]],
    //             [in1_u8.high32.0[0], in2_u8.high32.0[0], out_u8.high32.0[0]],
    //             [in1_u8.high32.0[1], in2_u8.high32.0[1], out_u8.high32.0[1]],
    //             [in1_u8.high32.0[2], in2_u8.high32.0[2], out_u8.high32.0[2]],
    //             [in1_u8.high32.0[3], in2_u8.high32.0[3], out_u8.high32.0[3]],
    //         ];
    //         for tuple in tuples {
    //             let lookup_input = tuple.map(|x| LookupInput::from(x.get_variable()));
    //             cs.enforce_lookup_tuple_for_variable_table(&lookup_input, id);
    //         }
    //         out_u8
    //     };
    //     // SECOND we optionally rotate (this can be merged into above lookups once we upgrade air_compiler backend)
    //     let rot_out_u16 = {
    //         let rot_const = Constraint::from(is_iota_columnxor)*Term::from(0)
    //             + Term::from(is_columnmix)*Term::from(63 % 16)
    //             + Term::from(is_theta_rho_iter0)*Term::from(0)
    //             + Term::from(is_theta_rho_iter1)*Term::from(1)
    //             + Term::from(is_theta_rho_iter2)*Term::from(62 % 16)
    //             + Term::from(is_theta_rho_iter3)*Term::from(28 % 16)
    //             + Term::from(is_theta_rho_iter4)*Term::from(27 % 16)
    //             + Term::from(is_chi1)*Term::from(0)
    //             + Term::from(is_chi2)*Term::from(0);
    //         let [is_rot_lt16, is_rot_lt32, is_rot_lt48, is_rot_lt64] = [
    //             Constraint::from(is_iota_columnxor) + Term::from(is_theta_rho_iter0) + Term::from(is_theta_rho_iter1) + Term::from(is_chi1) + Term::from(is_chi2),
    //             Constraint::from(is_theta_rho_iter3) + Term::from(is_theta_rho_iter3),
    //             Constraint::from(0),
    //             Constraint::from(is_columnmix) + Term::from(is_theta_rho_iter2)
    //         ];
    //         let in_u16 = [
    //             Constraint::from(bin_out_u8.low32.0[0]) + Term::from(1<<8)*Term::from(bin_out_u8.low32.0[1]) + Term::from(1<<16)*rot_const,
    //             Constraint::from(bin_out_u8.low32.0[2]) + Term::from(1<<8)*Term::from(bin_out_u8.low32.0[3]) + Term::from(1<<16)*rot_const,
    //             Constraint::from(bin_out_u8.high32.0[0]) + Term::from(1<<8)*Term::from(bin_out_u8.high32.0[1]) + Term::from(1<<16)*rot_const,
    //             Constraint::from(bin_out_u8.high32.0[2]) + Term::from(1<<8)*Term::from(bin_out_u8.high32.0[3]) + Term::from(1<<16)*rot_const,
    //         ];
    //         // TODO: move this out_u16rot into lookup get variable...
    //         let out_u16rot = LongRegisterRotation::new(cs);
    //         let id = table_rotl;
    //         let tuples = [
    //             [in_u16[0], Constraint::from(out_u16rot.chunks_u16[0][0]), Constraint::from(out_u16rot.chunks_u16[0][1])],
    //             [in_u16[1], Constraint::from(out_u16rot.chunks_u16[1][0]), Constraint::from(out_u16rot.chunks_u16[1][1])],
    //             [in_u16[2], Constraint::from(out_u16rot.chunks_u16[2][0]), Constraint::from(out_u16rot.chunks_u16[2][1])],
    //             [in_u16[3], Constraint::from(out_u16rot.chunks_u16[3][0]), Constraint::from(out_u16rot.chunks_u16[3][1])],
    //         ];
    //         for tuple in tuples {
    //             let lookup_input = tuple.map(|x| LookupInput::from(x));
    //             cs.enforce_lookup_tuple_for_fixed_table(&lookup_input, id, false);
    //         }
    //         out_u16rot.complete_rotation([is_rot_lt16, is_rot_lt32, is_rot_lt48, is_rot_lt64])
    //     };
    //     // FINALLY, we enforce manual routing!
    //     let (in1, in2, out) = (in1_u8.complete_composition(), in2_u8.complete_composition(), rot_out_u16);
    //     let in1_candidate = [
    //         Constraint::from(is_iota_columnxor)*Term::from(p0_idx0.low32.0[0]) + Term::from(is_columnmix)*Term::from(p1_25_new.low32.0[0]) + Term::from(is_theta_rho)*Term::from(p2_idx0.low32.0[0]) + Term::from(is_chi1)*Term::from(p3_idx1.low32.0[0]) + Term::from(is_chi2)*Term::from(p4_idx4.low32.0[0]),
    //         Constraint::from(is_iota_columnxor)*Term::from(p0_idx0.low32.0[1]) + Term::from(is_columnmix)*Term::from(p1_25_new.low32.0[1]) + Term::from(is_theta_rho)*Term::from(p2_idx0.low32.0[1]) + Term::from(is_chi1)*Term::from(p3_idx1.low32.0[1]) + Term::from(is_chi2)*Term::from(p4_idx4.low32.0[1]),
    //         Constraint::from(is_iota_columnxor)*Term::from(p0_idx0.high32.0[0]) + Term::from(is_columnmix)*Term::from(p1_25_new.high32.0[0]) + Term::from(is_theta_rho)*Term::from(p2_idx0.high32.0[0]) + Term::from(is_chi1)*Term::from(p3_idx1.high32.0[0]) + Term::from(is_chi2)*Term::from(p4_idx4.high32.0[0]),
    //         Constraint::from(is_iota_columnxor)*Term::from(p0_idx0.high32.0[1]) + Term::from(is_columnmix)*Term::from(p1_25_new.high32.0[1]) + Term::from(is_theta_rho)*Term::from(p2_idx0.high32.0[1]) + Term::from(is_chi1)*Term::from(p3_idx1.high32.0[1]) + Term::from(is_chi2)*Term::from(p4_idx4.high32.0[1]),
    //     ];
    //     let in2_candidate = [
    //         Constraint::from(is_iota_columnxor)*Term::from(p0_round_constant_control_reg.low32.0[0]) + Term::from(is_columnmix)*Term::from(p1_25.low32.0[0]) + Term::from(is_theta_rho)*Term::from(p2_idcol.low32.0[0]) + Term::from(is_chi1)*Term::from(p3_idx2.low32.0[0]) + Term::from(is_chi2)*Term::from(p4_idx0.low32.0[0]),
    //         Constraint::from(is_iota_columnxor)*Term::from(p0_round_constant_control_reg.low32.0[1]) + Term::from(is_columnmix)*Term::from(p1_25.low32.0[1]) + Term::from(is_theta_rho)*Term::from(p2_idcol.low32.0[1]) + Term::from(is_chi1)*Term::from(p3_idx2.low32.0[1]) + Term::from(is_chi2)*Term::from(p4_idx0.low32.0[1]),
    //         Constraint::from(is_iota_columnxor)*Term::from(p0_round_constant_control_reg.high32.0[0]) + Term::from(is_columnmix)*Term::from(p1_25.high32.0[0]) + Term::from(is_theta_rho)*Term::from(p2_idcol.high32.0[0]) + Term::from(is_chi1)*Term::from(p3_idx2.high32.0[0]) + Term::from(is_chi2)*Term::from(p4_idx0.high32.0[0]),
    //         Constraint::from(is_iota_columnxor)*Term::from(p0_round_constant_control_reg.high32.0[1]) + Term::from(is_columnmix)*Term::from(p1_25.high32.0[1]) + Term::from(is_theta_rho)*Term::from(p2_idcol.high32.0[1]) + Term::from(is_chi1)*Term::from(p3_idx2.high32.0[1]) + Term::from(is_chi2)*Term::from(p4_idx0.high32.0[1]),
    //     ];
    //     let out_candidate = [
    //         Constraint::from(is_iota_columnxor)*Term::from(p0_idx0_new.low32.0[0]) + Term::from(is_columnmix)*Term::from(p1_27.low32.0[0]) + Term::from(is_theta_rho)*Term::from(p2_idx0_new.low32.0[0]) + Term::from(is_chi1)*Term::from(p3_25_new.low32.0[0]) + Term::from(is_chi2)*Term::from(p4_tmp1.low32.0[0]),
    //         Constraint::from(is_iota_columnxor)*Term::from(p0_idx0_new.low32.0[1]) + Term::from(is_columnmix)*Term::from(p1_27.low32.0[1]) + Term::from(is_theta_rho)*Term::from(p2_idx0_new.low32.0[1]) + Term::from(is_chi1)*Term::from(p3_25_new.low32.0[1]) + Term::from(is_chi2)*Term::from(p4_tmp1.low32.0[1]),
    //         Constraint::from(is_iota_columnxor)*Term::from(p0_idx0_new.high32.0[0]) + Term::from(is_columnmix)*Term::from(p1_27.high32.0[0]) + Term::from(is_theta_rho)*Term::from(p2_idx0_new.high32.0[0]) + Term::from(is_chi1)*Term::from(p3_25_new.high32.0[0]) + Term::from(is_chi2)*Term::from(p4_tmp1.high32.0[0]),
    //         Constraint::from(is_iota_columnxor)*Term::from(p0_idx0_new.high32.0[1]) + Term::from(is_columnmix)*Term::from(p1_27.high32.0[1]) + Term::from(is_theta_rho)*Term::from(p2_idx0_new.high32.0[1]) + Term::from(is_chi1)*Term::from(p3_25_new.high32.0[1]) + Term::from(is_chi2)*Term::from(p4_tmp1.high32.0[1]),
    //     ];
    //     for i in 0..4 {
    //         cs.add_constraint(in1[i] - in1_candidate[i]);
    //         cs.add_constraint(in2[i] - in2_candidate[i]);
    //         cs.add_constraint(out[i] - out_candidate[i]);
    //     }
    // };
}

fn enforce_binop<F: PrimeField, CS: Circuit<F>>(cs: &mut CS, precompile_flags: [Boolean; 5], precompile_table_ids: [TableType; 5], precompile_rotation_flags: [Boolean; 9], precompile_rotation_constants: [u64; 9], input_output_candidates: [(LongRegister<F>, LongRegister<F>, LongRegister<F>); 5]) {
    debug_assert!(precompile_rotation_constants.into_iter().all(|c| c<64));
    let in1_u8 = LongRegisterDecomposition::new(cs);
    let in2_u8 = LongRegisterDecomposition::new(cs);

    // first set in1/in2 u8 decompositions + conditional out u64 results
    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let rotl = |u64_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32; 2], rot_const: u32| {
            // WATCH OUT: U3::shr needs to behave like rust u32::unbounded_shr, otherwise rust's u32>>32 does not behave well
            let rot_const_mod32 = rot_const % 32;
            let [low32_value, high32_value];
            if rot_const < 32 {
                low32_value = u64_value[0].shl(rot_const_mod32).overflowing_add(&u64_value[1].shr(32 - rot_const_mod32)).0;
                high32_value = u64_value[1].shl(rot_const_mod32).overflowing_add(&u64_value[0].shr(32 - rot_const_mod32)).0;
            } else {
                low32_value = u64_value[1].shl(rot_const_mod32).overflowing_add(&u64_value[0].shr(32 - rot_const_mod32)).0;
                high32_value = u64_value[0].shl(rot_const_mod32).overflowing_add(&u64_value[1].shr(32 - rot_const_mod32)).0;
            }
            [low32_value, high32_value]
        };
        let xor = |placer: &mut CS::WitnessPlacer, a_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32; 2], b_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32; 2]| {
            let xoru8 = |placer: &mut CS::WitnessPlacer, au8_value: &<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8, bu8_value: &<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8| {
                let au8_field = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(au8_value.widen().widen());
                let bu8_field = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer(bu8_value.widen().widen());
                let table_id = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(TableType::Xor.to_table_id() as u16);
                let [outu8_field] = placer.lookup(&[au8_field, bu8_field], &table_id);
                let outu8_value = outu8_field.as_integer().truncate().truncate();
                outu8_value
            };
            let tou8 = |u64_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32; 2]| {
                let zerou8 = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8::constant(0);
                let mut chunks: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8; 8] = from_fn(|_| zerou8.clone());
                chunks[0] = u64_value[0].truncate().truncate();
                chunks[1] = u64_value[0].truncate().shr(8).truncate();
                chunks[2] = u64_value[0].shr(16).truncate().truncate();
                chunks[3] = u64_value[0].shr(16).truncate().shr(8).truncate();
                chunks[4] = u64_value[1].truncate().truncate();
                chunks[5] = u64_value[1].truncate().shr(8).truncate();
                chunks[6] = u64_value[1].shr(16).truncate().truncate();
                chunks[7] = u64_value[1].shr(16).truncate().shr(8).truncate();
                chunks
            };
            let fromu8 = |u8_values: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8; 8]| {
                let low32_low16 = u8_values[0].widen().overflowing_add(&u8_values[1].widen().shl(8)).0;
                let low32_high16 = u8_values[2].widen().overflowing_add(&u8_values[3].widen().shl(8)).0;
                let high32_low16 = u8_values[4].widen().overflowing_add(&u8_values[5].widen().shl(8)).0;
                let high32_high16 = u8_values[6].widen().overflowing_add(&u8_values[7].widen().shl(8)).0;
                let low32 = low32_low16.widen().overflowing_add(&low32_high16.widen().shl(16)).0;
                let high32 = high32_low16.widen().overflowing_add(&high32_high16.widen().shl(16)).0;
                [low32, high32]
            };
            let au8_values = tou8(a_value);
            let bu8_values = tou8(b_value);
            let mut outu8_values: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8; 8] = from_fn(|_| <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8::constant(0));
            for i in 0..8 {
                outu8_values[i] = xoru8(placer, &au8_values[i], &bu8_values[i]);
            }
            fromu8(outu8_values)
        };
        let zero_u32 = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
        let mut in1_low32_value = zero_u32.clone();
        let mut in1_high32_value = zero_u32.clone();
        let mut in2_low32_value = zero_u32.clone();
        let mut in2_high32_value = zero_u32;
        for (flag, (possible_in1, possible_in2, _)) in precompile_flags.into_iter().zip(input_output_candidates) {
            let flag_value = placer.get_boolean(flag.get_variable().unwrap());
            let possible_in1_low32_value = placer.get_u32_from_u16_parts(possible_in1.low32.0.map(|x| x.get_variable()));
            let possible_in1_high32_value = placer.get_u32_from_u16_parts(possible_in1.high32.0.map(|x| x.get_variable()));
            let possible_in2_low32_value = placer.get_u32_from_u16_parts(possible_in2.low32.0.map(|x| x.get_variable()));
            let possible_in2_high32_value = placer.get_u32_from_u16_parts(possible_in2.high32.0.map(|x| x.get_variable()));
            in1_low32_value.assign_masked(&flag_value, &possible_in1_low32_value);
            in1_high32_value.assign_masked(&flag_value, &possible_in1_high32_value);
            in2_low32_value.assign_masked(&flag_value, &possible_in2_low32_value);
            in2_high32_value.assign_masked(&flag_value, &possible_in2_high32_value);
        }
        let [mut out_low32_value, mut out_high32_value] = xor(placer, &[in1_low32_value.clone(), in1_high32_value.clone()], &[in2_low32_value.clone(), in2_high32_value.clone()]);
        let is_columnmix = precompile_flags[1];
        for (flag, rot_const) in precompile_rotation_flags.into_iter().zip(precompile_rotation_constants) {
            // SECOND PRECOMPILE OUTPUTS HAVE ALREADY BEEN SET
            if flag != is_columnmix {  
                let flag_value = placer.get_boolean(flag.get_variable().unwrap());
                let [possible_rot_low32_value, possible_rot_high32_value] = rotl(&[out_low32_value.clone(), out_high32_value.clone()], rot_const as u32);
                out_low32_value.assign_masked(&flag_value, &possible_rot_low32_value);
                out_high32_value.assign_masked(&flag_value, &possible_rot_high32_value);
            }
        }
        // now can assign
        let zero_u8 = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8::constant(0);
        let in1_u8_values = {
            let mut chunks: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8; 8] = from_fn(|_| zero_u8.clone());
            chunks[0] = in1_low32_value.truncate().truncate();
            chunks[1] = in1_low32_value.truncate().shr(8).truncate();
            chunks[2] = in1_low32_value.shr(16).truncate().truncate();
            chunks[3] = in1_low32_value.shr(16).truncate().shr(8).truncate();
            chunks[4] = in1_high32_value.truncate().truncate();
            chunks[5] = in1_high32_value.truncate().shr(8).truncate();
            chunks[6] = in1_high32_value.shr(16).truncate().truncate();
            chunks[7] = in1_high32_value.shr(16).truncate().shr(8).truncate();
            chunks
        };
        let in2_u8_values = {
            let mut chunks: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8; 8] = from_fn(|_| zero_u8.clone());
            chunks[0] = in2_low32_value.truncate().truncate();
            chunks[1] = in2_low32_value.truncate().shr(8).truncate();
            chunks[2] = in2_low32_value.shr(16).truncate().truncate();
            chunks[3] = in2_low32_value.shr(16).truncate().shr(8).truncate();
            chunks[4] = in2_high32_value.truncate().truncate();
            chunks[5] = in2_high32_value.truncate().shr(8).truncate();
            chunks[6] = in2_high32_value.shr(16).truncate().truncate();
            chunks[7] = in2_high32_value.shr(16).truncate().shr(8).truncate();
            chunks
        };
        placer.assign_u8(in1_u8.low32[0].get_variable(), &in1_u8_values[0]);
        placer.assign_u8(in1_u8.low32[1].get_variable(), &in1_u8_values[1]);
        placer.assign_u8(in1_u8.low32[2].get_variable(), &in1_u8_values[2]);
        placer.assign_u8(in1_u8.low32[3].get_variable(), &in1_u8_values[3]);
        placer.assign_u8(in1_u8.high32[0].get_variable(), &in1_u8_values[4]);
        placer.assign_u8(in1_u8.high32[1].get_variable(), &in1_u8_values[5]);
        placer.assign_u8(in1_u8.high32[2].get_variable(), &in1_u8_values[6]);
        placer.assign_u8(in1_u8.high32[3].get_variable(), &in1_u8_values[7]);
        placer.assign_u8(in2_u8.low32[0].get_variable(), &in2_u8_values[0]);
        placer.assign_u8(in2_u8.low32[1].get_variable(), &in2_u8_values[1]);
        placer.assign_u8(in2_u8.low32[2].get_variable(), &in2_u8_values[2]);
        placer.assign_u8(in2_u8.low32[3].get_variable(), &in2_u8_values[3]);
        placer.assign_u8(in2_u8.high32[0].get_variable(), &in2_u8_values[4]);
        placer.assign_u8(in2_u8.high32[1].get_variable(), &in2_u8_values[5]);
        placer.assign_u8(in2_u8.high32[2].get_variable(), &in2_u8_values[6]);
        placer.assign_u8(in2_u8.high32[3].get_variable(), &in2_u8_values[7]);
        for (flag, (_, _, possible_out)) in precompile_flags.into_iter().zip(input_output_candidates) {
            // SECOND PRECOMPILE OUTPUTS HAVE ALREADY BEEN SET
            if flag != is_columnmix {
                let flag_value = placer.get_boolean(flag.get_variable().unwrap());
                placer.conditionally_assign_u32(possible_out.low32.0.map(|x| x.get_variable()), &flag_value, &out_low32_value);
                placer.conditionally_assign_u32(possible_out.high32.0.map(|x| x.get_variable()), &flag_value, &out_high32_value);
            }
        }
    };
    cs.set_values(value_fn);
    
    // FIRST we perform the main binary op lookups
    let bin_out_u8 = {
        let out_u8 = LongRegisterDecomposition::new(cs);
        let id = cs.choose_from_orthogonal_variants(
            &precompile_flags, 
            &precompile_table_ids.map(TableType::to_num)
        );
        let tuples = [
            [in1_u8.low32[0], in2_u8.low32[0], out_u8.low32[0]],
            [in1_u8.low32[1], in2_u8.low32[1], out_u8.low32[1]],
            [in1_u8.low32[2], in2_u8.low32[2], out_u8.low32[2]],
            [in1_u8.low32[3], in2_u8.low32[3], out_u8.low32[3]],
            [in1_u8.high32[0], in2_u8.high32[0], out_u8.high32[0]],
            [in1_u8.high32[1], in2_u8.high32[1], out_u8.high32[1]],
            [in1_u8.high32[2], in2_u8.high32[2], out_u8.high32[2]],
            [in1_u8.high32[3], in2_u8.high32[3], out_u8.high32[3]],
        ];
        for tuple in tuples {
            let lookup_inputs = [tuple[0], tuple[1]].map(|x| LookupInput::from(x.get_variable()));
            let lookup_outputs = [tuple[2].get_variable()];
            cs.set_variables_from_lookup_constrained_explicit(lookup_inputs, lookup_outputs, id);
        }
        out_u8
    };
    // SECOND we optionally rotate (this can be merged into above lookups once we upgrade air_compiler backend)
    let rot_out_u16 = {
        let rot_const = {
            let mut rot_const = Constraint::empty();
            for (flag, constant) in precompile_rotation_flags.into_iter().zip(precompile_rotation_constants) {
                rot_const = rot_const + Term::from(flag)*Term::from(constant % 16);
            }
            rot_const
        };
        let [is_rot_lt16, is_rot_lt32, is_rot_lt48, is_rot_lt64] = {
            let mut rot_bounds: [Constraint<F>; 4] = from_fn(|_| Constraint::empty()); // TODO: does this need to be 0 ??
            for (flag, constant) in precompile_rotation_flags.into_iter().zip(precompile_rotation_constants) {
                if constant < 16 {
                    rot_bounds[0] = rot_bounds[0].clone() + Term::from(flag);
                } else if constant < 32 {
                    rot_bounds[1] = rot_bounds[1].clone() + Term::from(flag);
                } else if constant < 48 {
                    rot_bounds[2] = rot_bounds[2].clone() + Term::from(flag);
                } else if constant < 64 {
                    rot_bounds[3] = rot_bounds[3].clone() + Term::from(flag);
                } else {unreachable!()}
            }
            rot_bounds
        };
        let in_u16 = [
            Constraint::from(bin_out_u8.low32[0]) + Term::from(1<<8)*Term::from(bin_out_u8.low32[1]) + Term::from(1<<16)*rot_const.clone(),
            Constraint::from(bin_out_u8.low32[2]) + Term::from(1<<8)*Term::from(bin_out_u8.low32[3]) + Term::from(1<<16)*rot_const.clone(),
            Constraint::from(bin_out_u8.high32[0]) + Term::from(1<<8)*Term::from(bin_out_u8.high32[1]) + Term::from(1<<16)*rot_const.clone(),
            Constraint::from(bin_out_u8.high32[2]) + Term::from(1<<8)*Term::from(bin_out_u8.high32[3]) + Term::from(1<<16)*rot_const,
        ];
        // TODO: move this out_u16rot into lookup get variable...
        let out_u16rot = LongRegisterRotation::new(cs);
        let id = TableType::RotL;
        let tuples = [
            (in_u16[0].clone(), out_u16rot.chunks_u16[0][0], out_u16rot.chunks_u16[0][1]),
            (in_u16[1].clone(), out_u16rot.chunks_u16[1][0], out_u16rot.chunks_u16[1][1]),
            (in_u16[2].clone(), out_u16rot.chunks_u16[2][0], out_u16rot.chunks_u16[2][1]),
            (in_u16[3].clone(), out_u16rot.chunks_u16[3][0], out_u16rot.chunks_u16[3][1]),
        ];
        for tuple in tuples {
            let lookup_inputs = [tuple.0].map(LookupInput::from);
            let lookup_outputs = [tuple.1, tuple.2].map(|x| x.get_variable());
            cs.set_variables_from_lookup_constrained_explicit(lookup_inputs, lookup_outputs, id.to_num());
        }
        out_u16rot.complete_rotation([is_rot_lt16, is_rot_lt32, is_rot_lt48, is_rot_lt64])
    };
    // FINALLY, we enforce manual routing!
    let (in1, in2, out) = (in1_u8.complete_composition(), in2_u8.complete_composition(), rot_out_u16);
    let (in1_candidate, in2_candidate, out_candidate) = {
        let mut in1_candidate: [Constraint<F>; 4] = from_fn(|_| Constraint::empty());
        let mut in2_candidate: [Constraint<F>; 4] = from_fn(|_| Constraint::empty());
        let mut out_candidate: [Constraint<F>; 4] = from_fn(|_| Constraint::empty());
        for (flag, (in1_u64, in2_u64, out_u64)) in precompile_flags.into_iter().zip(input_output_candidates) {
            in1_candidate[0] = in1_candidate[0].clone() + Constraint::from(flag)*Term::from(in1_u64.low32.0[0]);
            in1_candidate[1] = in1_candidate[1].clone() + Constraint::from(flag)*Term::from(in1_u64.low32.0[1]);
            in1_candidate[2] = in1_candidate[2].clone() + Constraint::from(flag)*Term::from(in1_u64.high32.0[0]);
            in1_candidate[3] = in1_candidate[3].clone() + Constraint::from(flag)*Term::from(in1_u64.high32.0[1]);

            in2_candidate[0] = in2_candidate[0].clone() + Constraint::from(flag)*Term::from(in2_u64.low32.0[0]);
            in2_candidate[1] = in2_candidate[1].clone() + Constraint::from(flag)*Term::from(in2_u64.low32.0[1]);
            in2_candidate[2] = in2_candidate[2].clone() + Constraint::from(flag)*Term::from(in2_u64.high32.0[0]);
            in2_candidate[3] = in2_candidate[3].clone() + Constraint::from(flag)*Term::from(in2_u64.high32.0[1]);

            out_candidate[0] = out_candidate[0].clone() + Constraint::from(flag)*Term::from(out_u64.low32.0[0]);
            out_candidate[1] = out_candidate[1].clone() + Constraint::from(flag)*Term::from(out_u64.low32.0[1]);
            out_candidate[2] = out_candidate[2].clone() + Constraint::from(flag)*Term::from(out_u64.high32.0[0]);
            out_candidate[3] = out_candidate[3].clone() + Constraint::from(flag)*Term::from(out_u64.high32.0[1]);
        }
        (in1_candidate, in2_candidate, out_candidate)
    };
    for i in 0..4 {
        cs.add_constraint(in1[i].clone() - in1_candidate[i].clone());
        cs.add_constraint(in2[i].clone() - in2_candidate[i].clone());
        cs.add_constraint(out[i].clone() - out_candidate[i].clone());
    }
}

fn enforce_copies<F: PrimeField, CS: Circuit<F>>(cs: &mut CS, precompile_flags: [Boolean; 5], input_output_candidates: [&'static[(LongRegister<F>, LongRegister<F>)]; 5]) {
    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        for (flag, candidates) in precompile_flags.into_iter().zip(input_output_candidates) {
            let flag_value = placer.get_boolean(flag.get_variable().unwrap());
            for (in_u64, out_u64) in candidates.iter() {
                let in_low32_value = placer.get_u32_from_u16_parts(in_u64.low32.0.map(|x| x.get_variable()));
                let in_high32_value = placer.get_u32_from_u16_parts(in_u64.high32.0.map(|x| x.get_variable()));
                placer.conditionally_assign_u32(out_u64.low32.0.map(|x| x.get_variable()), &flag_value, &in_low32_value);
                placer.conditionally_assign_u32(out_u64.high32.0.map(|x| x.get_variable()), &flag_value, &in_high32_value);
            }
        }
    };
    cs.set_values(value_fn);

    for (flag, candidates) in precompile_flags.into_iter().zip(input_output_candidates) {
        for (in_u64, out_u64) in candidates {
            cs.add_constraint(Constraint::from(flag)*(Term::from(in_u64.low32.0[0]) - Term::from(out_u64.low32.0[0])));
            cs.add_constraint(Constraint::from(flag)*(Term::from(in_u64.low32.0[1]) - Term::from(out_u64.low32.0[1])));
            cs.add_constraint(Constraint::from(flag)*(Term::from(in_u64.high32.0[0]) - Term::from(out_u64.high32.0[0])));
            cs.add_constraint(Constraint::from(flag)*(Term::from(in_u64.high32.0[1]) - Term::from(out_u64.high32.0[1])));
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::cs::cs_reference::BasicAssembly;
    use crate::one_row_compiler::OneRowCompiler;
    use crate::utils::serialize_to_file;
    use field::Mersenne31Field;

    #[test]
    fn compile_keccak_special5() {
        let mut cs = BasicAssembly::<Mersenne31Field>::new();
        define_keccak_special5_delegation_circuit(&mut cs);
        let (circuit_output, _) = cs.finalize();
        let compiler = OneRowCompiler::default();
        let compiled = compiler.compile_to_evaluate_delegations(circuit_output, 20);

        serialize_to_file(&compiled, "keccak_delegation_layout.json");
    }

    #[test]
    fn keccak_delegation_get_witness_graph() {
        let ssa_forms = dump_ssa_witness_eval_form_for_delegation::<Mersenne31Field, _>(
            define_keccak_special5_delegation_circuit,
        );
        serialize_to_file(&ssa_forms, "keccak_delegation_ssa.json");
    }
}
