use super::*;
use crate::cs::circuit::*;
use crate::cs::witness_placer::WitnessComputationCore;
use crate::cs::witness_placer::WitnessComputationalInteger;
use crate::cs::witness_placer::WitnessComputationalU16;
use crate::cs::witness_placer::WitnessComputationalU32;
use crate::cs::witness_placer::WitnessMask;
use crate::cs::witness_placer::WitnessPlacer;
use crate::cs::witness_placer::WitnessTypeSet;
use crate::one_row_compiler::LookupInput;
use crate::types::Boolean;
use crate::types::Num;
use common_constants::delegation_types::keccak_special5::*;
use core::array::from_fn;

static mut DEBUG: bool = false;
#[allow(unused)]
unsafe fn update_select(select: usize) {
    DEBUG_CONTROL = {
        let precompile: u16 = DEBUG_INFO[select].0;
        let iter: u16 = DEBUG_INFO[select].1;
        let round: u16 = DEBUG_INFO[select].2;
        1 << precompile | 1 << (5 + iter) | round << 10
    };
    DEBUG_INDEXES = DEBUG_INFO[select].3;
    DEBUG_INPUT_STATE = DEBUG_INFO[select].4;
    DEBUG_OUTPUT_STATE = DEBUG_INFO[select].5;
    DEBUG_CONTROL_NEXT = {
        let precompile = DEBUG_INFO[select].6;
        let iter = DEBUG_INFO[select].7;
        let round = DEBUG_INFO[select].8;
        1 << precompile | 1 << (5 + iter) | round << 10
    };
}
static mut DEBUG_CONTROL: u16 = 0;
static mut DEBUG_CONTROL_NEXT: u16 = 0;
static mut DEBUG_INDEXES: [usize; 6] = [0; 6];
static mut DEBUG_INPUT_STATE: [u64; 30] = [0; 30];
static mut DEBUG_OUTPUT_STATE: [u64; 30] = [0; 30];
mod debug_info;
use debug_info::DEBUG_INFO;

// INFO:
// - 5 "precompiles" (ops) packed into one circuit
// - max of 5 u64 bitwise operations (+ optional rotations)
// - max of 6 u64 R/W memory accesses (+ 2 u32 register accesses)
// - repeatedly called (1 keccak = 504 precompile cycles + 15 glue code cycles)

// ABI:
// - 1 register (x11) for state pointer (aligned s.t. state[29] does not overflow low 16 bits)
// - 1 register (x10.high) for control info (precompile bitmask || i bitmask || round)
//                         this register is bumped automatically by the circuit,
//                         which saves 50% of total RV cycles during execution

// TABLES:
// - 3 tables for extraction of 6 5-bit indexes
// - one table for special xor with round constant
// - one table normal xor with rotation constant
// - one table for andn
// - one table for rotation

// CIRCUIT:
// - get state ptr + control param with 2 mem. accesses
// - extract the 6 indices to fixed positions -> get 6 u64 R/W (word1..word6) inputs + create outputs
// - bump control param back into register, for next precompile call
// - extract precompile bitmask flags, to make u64 memory routing cheap
// - extract i bitmask bits, to make rotations cheap (u16_boundary_flags become linear combination)
// - dynamic logic across precompiles is cheaply encoded using routing constraints of degree 2
// - the precompile with round constant is managed through special xor table
// - the precompiles with xor/andn feed into option rotation tables and then to output

#[derive(Copy, Clone, Debug)]
struct LongRegister<F: PrimeField> {
    low32: Register<F>,
    high32: Register<F>,
}
impl<F: PrimeField> LongRegister<F> {
    fn new(cs: &mut impl Circuit<F>) -> LongRegister<F> {
        let low32_vars = from_fn(|_| cs.add_variable());
        let high32_vars = from_fn(|_| cs.add_variable());
        LongRegister {
            low32: Register(low32_vars.map(Num::Var)),
            high32: Register(high32_vars.map(Num::Var)),
        }
    }
    pub fn get_value_unsigned<C: Circuit<F>>(self, cs: &C) -> Option<u64> {
        let low = self.low32.get_value_unsigned(cs)?;
        let high = self.high32.get_value_unsigned(cs)?;
        assert!(low <= u32::MAX);
        assert!(high <= u32::MAX);
        Some(low as u64 | (high as u64) << 32)
    }
    #[expect(unused)]
    pub fn get_value_chunks_unsigned<C: Circuit<F>>(self, cs: &C) -> [F; 4] {
        [
            self.low32.0[0].get_value(cs).unwrap(),
            self.low32.0[1].get_value(cs).unwrap(),
            self.high32.0[0].get_value(cs).unwrap(),
            self.high32.0[1].get_value(cs).unwrap(),
        ]
    }
}

struct LongRegisterDecomposition<F: PrimeField> {
    low32: [Num<F>; 4],
    high32: [Num<F>; 4],
}
impl<F: PrimeField> LongRegisterDecomposition<F> {
    fn new(cs: &mut impl Circuit<F>) -> LongRegisterDecomposition<F> {
        let low32_vars = from_fn(|_| cs.add_variable());
        let high32_vars = from_fn(|_| cs.add_variable());
        LongRegisterDecomposition {
            low32: low32_vars.map(Num::Var),
            high32: high32_vars.map(Num::Var),
        }
    }
    fn complete_composition(&self) -> [Constraint<F>; 4] {
        [
            Constraint::from(self.low32[0]) + Term::from(1 << 8) * Term::from(self.low32[1]),
            Constraint::from(self.low32[2]) + Term::from(1 << 8) * Term::from(self.low32[3]),
            Constraint::from(self.high32[0]) + Term::from(1 << 8) * Term::from(self.high32[1]),
            Constraint::from(self.high32[2]) + Term::from(1 << 8) * Term::from(self.high32[3]),
        ]
    }
}
struct LongRegisterRotation<F: PrimeField> {
    chunks_u16: [[Num<F>; 2]; 4], // output of splitting rotation across u16 boundaries
}
impl<F: PrimeField> LongRegisterRotation<F> {
    fn new(cs: &mut impl Circuit<F>) -> LongRegisterRotation<F> {
        let vars = from_fn(|_| from_fn(|_| Num::Var(cs.add_variable())));
        LongRegisterRotation { chunks_u16: vars }
    }
    fn complete_rotation(&self, u16_boundary_flags: [Constraint<F>; 4]) -> [Constraint<F>; 4] {
        debug_assert!(u16_boundary_flags.iter().all(|x| x.degree() <= 1));
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
                Constraint::from(d_right) + Term::from(c_left),
            ]
        };
        // IF is_rot_lt16 THEN rotation is  0..16, SO take the chunk that fits that exact spot
        // IF is_rot_lt32 THEN rotation is 16..32, SO take the chunk that 1 spot over
        // IF is_rot_lt48 THEN rotation is 32..48, SO take the chunk that 2 spots over
        // IF is_rot_lt64 THEN rotation is 48..64, SO take the chunk that 3 spots over
        let low32_low16 = is_rot_lt16.clone() * a.clone()
            + is_rot_lt32.clone() * d.clone()
            + is_rot_lt48.clone() * c.clone()
            + is_rot_lt64.clone() * b.clone();
        let low32_high16 = is_rot_lt16.clone() * b.clone()
            + is_rot_lt32.clone() * a.clone()
            + is_rot_lt48.clone() * d.clone()
            + is_rot_lt64.clone() * c.clone();
        let high32_low16 = is_rot_lt16.clone() * c.clone()
            + is_rot_lt32.clone() * b.clone()
            + is_rot_lt48.clone() * a.clone()
            + is_rot_lt64.clone() * d.clone();
        let high32_high16 = is_rot_lt16 * d + is_rot_lt32 * c + is_rot_lt48 * b + is_rot_lt64 * a;
        [low32_low16, low32_high16, high32_low16, high32_high16]
    }
}

pub fn all_table_types() -> Vec<TableType> {
    vec![
        TableType::ZeroEntry, // this is a possibility when delegation is disabled and all mem reads become 0
        TableType::KeccakPermutationIndices12,
        TableType::KeccakPermutationIndices34,
        TableType::KeccakPermutationIndices56,
        TableType::Xor,
        TableType::XorSpecialIota,
        TableType::AndN,
        TableType::RotL,
    ]
}

pub fn keccak_special5_delegation_circuit_create_table_driver<F: PrimeField>() -> TableDriver<F> {
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
    let execute = cs.process_delegation_request();

    // STEP1: process all memory accesses
    let (control, control_next) = {
        let x10_request = RegisterAccessRequest {
            register_index: 10,
            register_write: true,
            indirects_alignment_log2: 0, // no indirects, contains explicit control value
            indirect_accesses: vec![],
        };
        let x10_and_indirects = cs.create_register_and_indirect_memory_accesses(x10_request);
        assert!(x10_and_indirects.indirect_accesses.is_empty());
        let RegisterAccessType::Write {
            read_value: control_reg,
            write_value: control_reg_next,
        } = x10_and_indirects.register_access
        else {
            unreachable!()
        };

        if unsafe { DEBUG } {
            // set control using external stress test data
            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                let control_value =
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                        unsafe { DEBUG_CONTROL },
                    );
                placer.assign_u16(control_reg[1], &control_value);
            };
            cs.set_values(value_fn);
        }

        // set x10_next
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            let control_val = placer.get_u16(control_reg[1]);
            let zero_val =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0);
            let one_val =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(1);
            let mask_val =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0b11111);
            let precompile_val = control_val.and(&mask_val);
            let [p0_v, p1_v, p2_v, p3_v, p4_v] = {
                [
                    precompile_val.and(&one_val),
                    precompile_val.shr(1).and(&one_val),
                    precompile_val.shr(2).and(&one_val),
                    precompile_val.shr(3).and(&one_val),
                    precompile_val.shr(4),
                ]
            };
            let iter_val = control_val.shr(5).and(&mask_val);
            let [i0_v, i1_v, i2_v, i3_v, i4_v] = {
                [
                    iter_val.and(&one_val),
                    iter_val.shr(1).and(&one_val),
                    iter_val.shr(2).and(&one_val),
                    iter_val.shr(3).and(&one_val),
                    iter_val.shr(4),
                ]
            };
            let round_val = control_val.shr(10);
            let control_next_val =
                {
                    let iter_next_val = {
                        let iter_fwd_val = i4_v
                            .overflowing_add(&i0_v.shl(1))
                            .0
                            .overflowing_add(&i1_v.shl(2))
                            .0
                            .overflowing_add(&i2_v.shl(3))
                            .0
                            .overflowing_add(&i3_v.shl(4))
                            .0;
                        <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                            &p1_v.clone().into_mask().or(&p3_v.clone().into_mask()),
                            &iter_val,
                            &iter_fwd_val,
                        )
                    };
                    let precompile_next_val =
                        {
                            let precompile_fwd_val = p4_v
                                .overflowing_add(&p0_v.shl(1))
                                .0
                                .overflowing_add(&p1_v.shl(2))
                                .0
                                .overflowing_add(&p2_v.shl(3))
                                .0
                                .overflowing_add(&p3_v.shl(4))
                                .0;
                            let precompile_rev_val = p1_v
                                .overflowing_add(&p2_v.shl(1))
                                .0
                                .overflowing_add(&p3_v.shl(2))
                                .0
                                .overflowing_add(&p4_v.shl(3))
                                .0
                                .overflowing_add(&p0_v.shl(4))
                                .0;
                            <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                        &p1_v.into_mask().or(&p3_v.into_mask()).or(&i4_v.clone().into_mask()),
                        &precompile_fwd_val,
                        &<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                            &p4_v.clone().into_mask(),
                            &precompile_rev_val,
                            &precompile_val)
                        )
                        };
                    let round_next_val = {
                        let round_fwd_val = round_val.overflowing_add(&one_val).0;
                        <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                            &p4_v.into_mask().and(&i4_v.into_mask()),
                            &round_fwd_val,
                            &round_val,
                        )
                    };
                    precompile_next_val
                        .overflowing_add(&iter_next_val.shl(5))
                        .0
                        .overflowing_add(&round_next_val.shl(10))
                        .0
                };
            placer.assign_u16(control_reg_next[0], &zero_val);
            placer.assign_u16(control_reg_next[1], &control_next_val);
        };
        cs.set_values(value_fn);

        cs.add_constraint_allow_explicit_linear(Constraint::from(control_reg[0])); // we expect low 16 bits to be empty
        cs.add_constraint_allow_explicit_linear(Constraint::from(control_reg_next[0])); // we expect low 16 bits to be empty
        (control_reg[1], control_reg_next[1]) // only the high 16 bits contain control info (to accomodate for LUI)
    };
    let state_indexes = {
        // we can't assign to these variables by lookup since these variables belong to memory subtree
        // they will be assigned through placeholder by cs.create_register_and_indirect_memory_accesses
        let [s1, s2, s3, s4, s5, s6] = from_fn(|_| cs.add_variable());
        cs.enforce_lookup_tuple_for_fixed_table(
            &[control, s1, s2].map(LookupInput::from),
            TableType::KeccakPermutationIndices12,
            false,
        );
        cs.enforce_lookup_tuple_for_fixed_table(
            &[control, s3, s4].map(LookupInput::from),
            TableType::KeccakPermutationIndices34,
            false,
        );
        cs.enforce_lookup_tuple_for_fixed_table(
            &[control, s5, s6].map(LookupInput::from),
            TableType::KeccakPermutationIndices56,
            false,
        );
        [s1, s2, s3, s4, s5, s6]
    };

    // Variables above count in notion of "state element", that is itself u64 word. So we should read two u32 words
    let (state_inputs, state_outputs) = {
        let state_accesses = state_indexes
            .iter()
            .flat_map(|&var| {
                [
                    IndirectAccessOffset {
                        variable_dependent: Some((core::mem::size_of::<u64>() as u32, var)),
                        offset_constant: 0,
                        assume_no_alignment_overflow: true,
                        is_write_access: true,
                    },
                    IndirectAccessOffset {
                        variable_dependent: Some((core::mem::size_of::<u64>() as u32, var)),
                        offset_constant: core::mem::size_of::<u32>() as u32,
                        assume_no_alignment_overflow: true,
                        is_write_access: true,
                    },
                ]
            })
            .collect();
        let x11_request = RegisterAccessRequest {
            register_index: 11,
            register_write: false,
            indirects_alignment_log2: 8, // 256 bytes: 25 u64 state + 5 u64 scratch = 240 bytes
            indirect_accesses: state_accesses, // we just r/w 6 u64 words
        };
        let x11_and_indirects = cs.create_register_and_indirect_memory_accesses(x11_request);
        assert_eq!(x11_and_indirects.indirect_accesses.len(), 12);
        let mut state_inputs = [LongRegister {
            low32: Register([Num::Constant(F::ZERO); 2]),
            high32: Register([Num::Constant(F::ZERO); 2]),
        }; 6];
        let mut state_outputs = [LongRegister {
            low32: Register([Num::Constant(F::ZERO); 2]),
            high32: Register([Num::Constant(F::ZERO); 2]),
        }; 6];
        for i in 0..NUM_X10_INDIRECT_U64_WORDS {
            let IndirectAccessType::Write {
                read_value: in_low,
                write_value: out_low,
                ..
            } = x11_and_indirects.indirect_accesses[i * 2]
            else {
                unreachable!()
            };
            let IndirectAccessType::Write {
                read_value: in_high,
                write_value: out_high,
                ..
            } = x11_and_indirects.indirect_accesses[i * 2 + 1]
            else {
                unreachable!()
            };
            state_inputs[i] = LongRegister {
                low32: Register(in_low.map(Num::Var)),
                high32: Register(in_high.map(Num::Var)),
            };
            state_outputs[i] = LongRegister {
                low32: Register(out_low.map(Num::Var)),
                high32: Register(out_high.map(Num::Var)),
            };
        }

        if unsafe { DEBUG } {
            // set state_inputs based off of stress test data
            // first: set the index vars as they were overwritten by faulty simulator placeholder data
            let truevar = Boolean::Is(cs.add_variable_from_constraint_allow_explicit_linear(
                Constraint::from(execute.toggle()),
            ));
            assert!(truevar.get_value(cs).unwrap());
            cs.peek_lookup_value_unconstrained_ext(
                &[LookupInput::from(control)],
                &[state_indexes[0], state_indexes[1]],
                TableType::KeccakPermutationIndices12.to_num(),
                truevar,
            );
            cs.peek_lookup_value_unconstrained_ext(
                &[LookupInput::from(control)],
                &[state_indexes[2], state_indexes[3]],
                TableType::KeccakPermutationIndices34.to_num(),
                truevar,
            );
            cs.peek_lookup_value_unconstrained_ext(
                &[LookupInput::from(control)],
                &[state_indexes[4], state_indexes[5]],
                TableType::KeccakPermutationIndices56.to_num(),
                truevar,
            );
            // then: go ahead and process state_inputs
            let state_indexes_usize =
                state_indexes.map(|var| cs.get_value(var).unwrap().as_u64_reduced() as usize);
            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                let state_inputs_values = state_indexes_usize.map(|i| {
                    [
                        <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(
                            unsafe { DEBUG_INPUT_STATE[i] } as u32,
                        ),
                        <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(
                            (unsafe { DEBUG_INPUT_STATE[i] } >> 32) as u32,
                        ),
                    ]
                });
                for (state_input, state_input_value) in
                    state_inputs.into_iter().zip(state_inputs_values)
                {
                    placer.assign_u32_from_u16_parts(
                        state_input.low32.0.map(|x| x.get_variable()),
                        &state_input_value[0],
                    );
                    placer.assign_u32_from_u16_parts(
                        state_input.high32.0.map(|x| x.get_variable()),
                        &state_input_value[1],
                    );
                }
            };
            cs.set_values(value_fn);
        }

        (state_inputs, state_outputs)
    };

    let (precompile_bitmask, iter_bitmask, round) = {
        // TMP FIX: we're removing this in order to have even number of u16 range checks in the witness subtree
        let bitmask: [Boolean; KECCAK5_TOTAL_NUM_CONTROL_BITS] =
            Boolean::split_into_bitmask(cs, Num::Var(control));
        let round = bitmask[(PRECOMPILE_MODE_NUM_CONTROL_BITS + ITERATION_NUM_CONTROL_BITS)
            ..KECCAK5_TOTAL_NUM_CONTROL_BITS]
            .iter()
            .enumerate()
            .fold(Constraint::empty(), |acc, (i, &el)| {
                acc + Term::from(1 << i) * Term::from(el)
            });
        (
            bitmask[..PRECOMPILE_MODE_NUM_CONTROL_BITS]
                .try_into()
                .unwrap(),
            bitmask[PRECOMPILE_MODE_NUM_CONTROL_BITS
                ..(PRECOMPILE_MODE_NUM_CONTROL_BITS + ITERATION_NUM_CONTROL_BITS)]
                .try_into()
                .unwrap(),
            round,
        )
    };

    // we place bitmasks into individual Booleans for simplicity
    let [is_iota_columnxor, is_columnmix, is_theta_rho, is_chi1, is_chi2] = precompile_bitmask;
    let [is_iter0, is_iter1, is_iter2, is_iter3, is_iter4] = iter_bitmask;
    // NOT STRICTLY NECESSARY but it's free \_(o_O)_/
    cs.add_constraint(
        Constraint::from(execute)
            * (Term::from(is_iota_columnxor)
                + Term::from(is_columnmix)
                + Term::from(is_theta_rho)
                + Term::from(is_chi1)
                + Term::from(is_chi2)
                - Term::from(1)),
    );
    cs.add_constraint(
        Constraint::from(execute)
            * (Term::from(is_iter0)
                + Term::from(is_iter1)
                + Term::from(is_iter2)
                + Term::from(is_iter3)
                + Term::from(is_iter4)
                - Term::from(1)),
    );

    // now we enforce the control_next bump
    let iter_next: Constraint<F> = {
        let cur = Constraint::from(is_iter0)
            + Term::from(1 << 1) * Term::from(is_iter1)
            + Term::from(1 << 2) * Term::from(is_iter2)
            + Term::from(1 << 3) * Term::from(is_iter3)
            + Term::from(1 << 4) * Term::from(is_iter4);
        let fwd = Constraint::from(is_iter4)
            + Term::from(1 << 1) * Term::from(is_iter0)
            + Term::from(1 << 2) * Term::from(is_iter1)
            + Term::from(1 << 3) * Term::from(is_iter2)
            + Term::from(1 << 4) * Term::from(is_iter3);
        (Constraint::from(is_iota_columnxor) + Term::from(is_theta_rho) + Term::from(is_chi2)) * fwd
            + (Term::from(is_columnmix) + Term::from(is_chi1)) * cur
    };
    let precompile_next: Constraint<F> = {
        // def: (p1 + p3)fwd + (p0 + p2)maybe_fwd + (p4)fwd_or_rev
        //    = fwd + (p0 + p2) * !i4 * (cur - fwd) + p4 * !i4 * (rev - fwd)
        //    = fwd + !i4 * ((p0 + p2)(cur - fwd) + p4(rev - fwd))
        let cur = Constraint::from(is_iota_columnxor)
            + Term::from(1 << 1) * Term::from(is_columnmix)
            + Term::from(1 << 2) * Term::from(is_theta_rho)
            + Term::from(1 << 3) * Term::from(is_chi1)
            + Term::from(1 << 4) * Term::from(is_chi2);
        let fwd = Constraint::from(is_chi2)
            + Term::from(1 << 1) * Term::from(is_iota_columnxor)
            + Term::from(1 << 2) * Term::from(is_columnmix)
            + Term::from(1 << 3) * Term::from(is_theta_rho)
            + Term::from(1 << 4) * Term::from(is_chi1);
        let rev = Constraint::from(is_columnmix)
            + Term::from(1 << 1) * Term::from(is_theta_rho)
            + Term::from(1 << 2) * Term::from(is_chi1)
            + Term::from(1 << 3) * Term::from(is_chi2)
            + Term::from(1 << 4) * Term::from(is_iota_columnxor);
        let not_iter4 = Constraint::from(is_iter4.toggle());
        let special = cs.add_variable_from_constraint(
            (Constraint::from(is_iota_columnxor) + Term::from(is_theta_rho)) * (cur - fwd.clone())
                + Term::from(is_chi2) * (rev - fwd.clone()),
        );
        fwd + not_iter4 * Term::from(special)
    };
    let round_next: Constraint<F> = round.clone() + Term::from(is_chi2) * Term::from(is_iter4);
    cs.add_constraint(
        precompile_next + Term::from(1 << 5) * iter_next + Term::from(1 << 10) * round_next
            - Term::from(control_next),
    );

    // derive flags needed to identify rotations for precompile 2
    let [is_theta_rho_iter0, is_theta_rho_iter1, is_theta_rho_iter2, is_theta_rho_iter3, is_theta_rho_iter4] = [
        Boolean::and(&is_theta_rho, &is_iter0, cs),
        Boolean::and(&is_theta_rho, &is_iter1, cs),
        Boolean::and(&is_theta_rho, &is_iter2, cs),
        Boolean::and(&is_theta_rho, &is_iter3, cs),
        Boolean::and(&is_theta_rho, &is_iter4, cs),
    ];

    // need an easy way to identify positions later on during manual routing constraints...
    let [[p0_idx0, p0_idx5, p0_idx10, p0_idx15, p0_idx20, _p0_idcol], [p1_25, p1_26, p1_27, p1_28, p1_29, p1_0], [p2_idx0, p2_idx5, p2_idx10, p2_idx15, p2_idx20, p2_idcol], [p3_idx1, p3_idx2, p3_idx3, p3_idx4, _p3_25, _p3_26], [p4_idx0, p4_idx3, p4_idx4, p4_25, p4_26, _p4_27]] =
        [state_inputs; 5];
    let [[p0_idx0_new, p0_idx5_new, p0_idx10_new, p0_idx15_new, p0_idx20_new, p0_idcol_new], [p1_25_new, p1_26_new, p1_27_new, p1_28_new, p1_29_new, p1_0_new], [p2_idx0_new, p2_idx5_new, p2_idx10_new, p2_idx15_new, p2_idx20_new, p2_idcol_new], [p3_idx1_new, p3_idx2_new, p3_idx3_new, p3_idx4_new, p3_25_new, p3_26_new], [p4_idx0_new, p4_idx3_new, p4_idx4_new, p4_25_new, p4_26_new, p4_27_new]] =
        [state_outputs; 5];

    // TODO: not sure if 8bit mask is necessary (probably safer like this..)
    let p0_round_constant_control_reg = {
        // ORIGINAL
        let round_if_iter0 = cs.add_variable_from_constraint(round * Term::from(is_iter0));
        let chunks_u8: [Constraint<F>; 8] = from_fn(|i| {
            Constraint::from(round_if_iter0) + Term::from(1 << 5) * Term::from(i as u64)
        });
        let chunks_u16: [Num<F>; 4] = from_fn(|i| {
            cs.add_variable_from_constraint_allow_explicit_linear(
                chunks_u8[i * 2].clone() + Term::from(1 << 8) * chunks_u8[i * 2 + 1].clone(),
            )
        })
        .map(Num::Var);

        // NEW (but worse performance ??)
        // let round_if_iter0 = round * Term::from(is_iter0);
        // let chunks_u8: [Constraint<F>; 8] = from_fn(|i| round_if_iter0.clone() + Term::from(1<<5)*Term::from(i as u64));
        // let chunks_u16: [Num<F>; 4] = from_fn(|i| cs.add_variable_from_constraint(chunks_u8[i*2].clone() + Term::from(1<<8)*chunks_u8[i*2+1].clone())).map(Num::Var);
        LongRegister {
            low32: Register([chunks_u16[0], chunks_u16[1]]),
            high32: Register([chunks_u16[2], chunks_u16[3]]),
        }
    };
    let state_tmps: [LongRegister<F>; 3] = from_fn(|_| LongRegister::new(cs));
    let [p0_tmp1, p0_tmp2, p0_tmp3] = state_tmps;
    let [p3_tmp1, p3_tmp2, _] = state_tmps;
    let [p4_tmp1, p4_tmp2, _] = state_tmps;

    // set unconditional out+tmp u64 results
    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let rotl = |u64_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32;
                         2],
                    rot_const: u32| {
            // WATCH OUT: U3::shr needs to behave like rust u32::unbounded_shr, otherwise rust's u32>>32 does not behave well
            let rot_const_mod32 = rot_const % 32;
            let [low32_value, high32_value];
            if rot_const < 32 {
                low32_value = u64_value[0]
                    .shl(rot_const_mod32)
                    .overflowing_add(&u64_value[1].shr(32 - rot_const_mod32))
                    .0;
                high32_value = u64_value[1]
                    .shl(rot_const_mod32)
                    .overflowing_add(&u64_value[0].shr(32 - rot_const_mod32))
                    .0;
            } else {
                low32_value = u64_value[1]
                    .shl(rot_const_mod32)
                    .overflowing_add(&u64_value[0].shr(32 - rot_const_mod32))
                    .0;
                high32_value = u64_value[0]
                    .shl(rot_const_mod32)
                    .overflowing_add(&u64_value[1].shr(32 - rot_const_mod32))
                    .0;
            }
            [low32_value, high32_value]
        };
        let xor = |a_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32; 2], b_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32; 2]| {
            core::array::from_fn(|i| a_value[i].xor(&b_value[i]))
        };
        let andn = |a_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32;
                         2],
                    b_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32;
                         2]| {
            core::array::from_fn(|i| a_value[i].not().and(&b_value[i]))
        };
        let zero_u64 = [
            <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0),
            <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0),
        ];

        let state_input_values = state_inputs.map(|x| {
            [
                placer.get_u32_from_u16_parts(x.low32.0.map(|y| y.get_variable())),
                placer.get_u32_from_u16_parts(x.high32.0.map(|y| y.get_variable())),
            ]
        });
        let (state_output_values, state_tmp_values) = {
            let (p0_state_output_values, p0_tmp_values) = {
                let [idx0_value, idx5_value, idx10_value, idx15_value, idx20_value, _idcol_value] =
                    state_input_values.clone();
                let idx0_new_value = {
                    let round_constant_value = {
                        let round_if_iter0_value = {
                            let is_iter0_value =
                                placer.get_boolean(is_iter0.get_variable().unwrap());
                            let round_value = {
                                let control_value: <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16 = placer.get_u16(control);
                                control_value.shr(10)
                            };
                            let zero_value = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0);
                            <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                                &is_iter0_value,
                                &round_value,
                                &zero_value,
                            )
                        };
                        let round_constants_adjusted_values = {
                            const ROUND_CONSTANTS_ADJUSTED: [u64; 24] = [
                                0,
                                1,
                                32898,
                                9223372036854808714,
                                9223372039002292224,
                                32907,
                                2147483649,
                                9223372039002292353,
                                9223372036854808585,
                                138,
                                136,
                                2147516425,
                                2147483658,
                                2147516555,
                                9223372036854775947,
                                9223372036854808713,
                                9223372036854808579,
                                9223372036854808578,
                                9223372036854775936,
                                32778,
                                9223372039002259466,
                                9223372039002292353,
                                9223372036854808704,
                                2147483649,
                            ];
                            ROUND_CONSTANTS_ADJUSTED.map(|rc| [
                                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(rc as u32),
                                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::constant((rc>>32) as u32)
                            ])
                        };
                        let mut round_constant_value = [
                            <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(
                                0,
                            ),
                            <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(
                                0,
                            ),
                        ];
                        for (i, [rc_low32_value, rc_high32_value]) in
                            round_constants_adjusted_values.into_iter().enumerate()
                        {
                            let i_value = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<
                                F,
                            >>::U16::constant(i as u16);
                            let is_round_eqi = round_if_iter0_value.equal(&i_value);
                            round_constant_value[0].assign_masked(&is_round_eqi, &rc_low32_value);
                            round_constant_value[1].assign_masked(&is_round_eqi, &rc_high32_value);
                        }
                        round_constant_value
                    };
                    xor(&idx0_value, &round_constant_value)
                };
                let idx5_new_value = idx5_value.clone();
                let idx10_new_value = idx10_value.clone();
                let idx15_new_value = idx15_value.clone();
                let idx20_new_value = idx20_value.clone();
                let tmp1_value = xor(&idx0_new_value, &idx5_value);
                let tmp2_value = xor(&tmp1_value, &idx10_value);
                let tmp3_value = xor(&tmp2_value, &idx15_value);
                let idcol_new_value = xor(&tmp3_value, &idx20_value);
                (
                    [
                        idx0_new_value,
                        idx5_new_value,
                        idx10_new_value,
                        idx15_new_value,
                        idx20_new_value,
                        idcol_new_value,
                    ],
                    [tmp1_value, tmp2_value, tmp3_value],
                )
            };
            let (p1_state_output_values, p1_tmp_values) = {
                let [i25_value, i26_value, i27_value, i28_value, i29_value, i0_value] =
                    state_input_values.clone();
                let i25_new_value = xor(&i25_value, &rotl(&i27_value, 1));
                let i26_new_value = xor(&i26_value, &rotl(&i28_value, 1));
                let i27_new_value = xor(&i27_value, &rotl(&i29_value, 1));
                let i28_new_value = xor(&i28_value, &rotl(&i25_value, 1));
                let i29_new_value = xor(&i29_value, &rotl(&i26_value, 1));
                let i0_new_value = i0_value.clone();
                (
                    [
                        i25_new_value,
                        i26_new_value,
                        i27_new_value,
                        i28_new_value,
                        i29_new_value,
                        i0_new_value,
                    ],
                    [zero_u64.clone(), zero_u64.clone(), zero_u64.clone()],
                )
            };
            let (p2_state_output_values, p2_tmp_values) = {
                let [idx0_value, idx5_value, idx10_value, idx15_value, idx20_value, idcol_value] =
                    state_input_values.clone();
                let iter_values =
                    iter_bitmask.map(|x| placer.get_boolean(x.get_variable().unwrap()));
                let idx0_new_value = {
                    let mut idx0_new_value = xor(&idx0_value, &idcol_value);
                    for (iter_value, rot_const) in iter_values.iter().zip([0, 1, 62, 28, 27]) {
                        let possible_rotation_value = rotl(&idx0_new_value, rot_const);
                        idx0_new_value[0].assign_masked(iter_value, &possible_rotation_value[0]);
                        idx0_new_value[1].assign_masked(iter_value, &possible_rotation_value[1]);
                    }
                    idx0_new_value
                };
                let idx5_new_value = {
                    let mut idx5_new_value = xor(&idx5_value, &idcol_value);
                    for (iter_value, rot_const) in iter_values.iter().zip([36, 44, 6, 55, 20]) {
                        let possible_rotation_value = rotl(&idx5_new_value, rot_const);
                        idx5_new_value[0].assign_masked(iter_value, &possible_rotation_value[0]);
                        idx5_new_value[1].assign_masked(iter_value, &possible_rotation_value[1]);
                    }
                    idx5_new_value
                };
                let idx10_new_value = {
                    let mut idx10_new_value = xor(&idx10_value, &idcol_value);
                    for (iter_value, rot_const) in iter_values.iter().zip([3, 10, 43, 25, 39]) {
                        let possible_rotation_value = rotl(&idx10_new_value, rot_const);
                        idx10_new_value[0].assign_masked(iter_value, &possible_rotation_value[0]);
                        idx10_new_value[1].assign_masked(iter_value, &possible_rotation_value[1]);
                    }
                    idx10_new_value
                };
                let idx15_new_value = {
                    let mut idx15_new_value = xor(&idx15_value, &idcol_value);
                    for (iter_value, rot_const) in iter_values.iter().zip([41, 45, 15, 21, 8]) {
                        let possible_rotation_value = rotl(&idx15_new_value, rot_const);
                        idx15_new_value[0].assign_masked(iter_value, &possible_rotation_value[0]);
                        idx15_new_value[1].assign_masked(iter_value, &possible_rotation_value[1]);
                    }
                    idx15_new_value
                };
                let idx20_new_value = {
                    let mut idx20_new_value = xor(&idx20_value, &idcol_value);
                    for (iter_value, rot_const) in iter_values.iter().zip([18, 2, 61, 56, 14]) {
                        let possible_rotation_value = rotl(&idx20_new_value, rot_const);
                        idx20_new_value[0].assign_masked(iter_value, &possible_rotation_value[0]);
                        idx20_new_value[1].assign_masked(iter_value, &possible_rotation_value[1]);
                    }
                    idx20_new_value
                };
                let idcol_new_value = idcol_value.clone();
                (
                    [
                        idx0_new_value,
                        idx5_new_value,
                        idx10_new_value,
                        idx15_new_value,
                        idx20_new_value,
                        idcol_new_value,
                    ],
                    [zero_u64.clone(), zero_u64.clone(), zero_u64.clone()],
                )
            };
            let (p3_state_output_values, p3_tmp_values) = {
                let [idx1_value, idx2_value, idx3_value, idx4_value, _i25_value, _i26_value] =
                    state_input_values.clone();
                let tmp1_value = andn(&idx2_value, &idx3_value);
                let idx1_new_value = xor(&idx1_value, &tmp1_value);
                let tmp2_value = andn(&idx3_value, &idx4_value);
                let idx2_new_value = xor(&idx2_value, &tmp2_value);
                let idx3_new_value = idx3_value.clone();
                let idx4_new_value = idx4_value.clone();
                let i25_new_value = andn(&idx1_value, &idx2_value);
                let i26_new_value = idx1_value.clone();
                (
                    [
                        idx1_new_value,
                        idx2_new_value,
                        idx3_new_value,
                        idx4_new_value,
                        i25_new_value,
                        i26_new_value,
                    ],
                    [tmp1_value, tmp2_value, zero_u64.clone()],
                )
            };
            let (p4_state_output_values, p4_tmp_values) = {
                let [idx0_value, idx3_value, idx4_value, i25_value, i26_value, _i27_value] =
                    state_input_values;
                let idx0_new_value = xor(&idx0_value, &i25_value);
                let tmp1_value = andn(&idx4_value, &idx0_value);
                let idx3_new_value = xor(&idx3_value, &tmp1_value);
                let tmp2_value = andn(&idx0_value, &i26_value);
                let idx4_new_value = xor(&idx4_value, &tmp2_value);
                let i25_new_value = i25_value.clone();
                let i26_new_value = i26_value.clone();
                let i27_new_value = idx0_new_value.clone();
                (
                    [
                        idx0_new_value,
                        idx3_new_value,
                        idx4_new_value,
                        i25_new_value,
                        i26_new_value,
                        i27_new_value,
                    ],
                    [tmp1_value, tmp2_value, zero_u64.clone()],
                )
            };
            let flag_values =
                precompile_bitmask.map(|x| placer.get_boolean(x.get_variable().unwrap()));
            let mut state_output_values: [_; 6] = from_fn(|_| zero_u64.clone());
            let mut state_tmp_values: [_; 3] = from_fn(|_| zero_u64.clone());
            for i in 0..6 {
                state_output_values[i][0]
                    .assign_masked(&flag_values[0], &p0_state_output_values[i][0]);
                state_output_values[i][1]
                    .assign_masked(&flag_values[0], &p0_state_output_values[i][1]);
                state_output_values[i][0]
                    .assign_masked(&flag_values[1], &p1_state_output_values[i][0]);
                state_output_values[i][1]
                    .assign_masked(&flag_values[1], &p1_state_output_values[i][1]);
                state_output_values[i][0]
                    .assign_masked(&flag_values[2], &p2_state_output_values[i][0]);
                state_output_values[i][1]
                    .assign_masked(&flag_values[2], &p2_state_output_values[i][1]);
                state_output_values[i][0]
                    .assign_masked(&flag_values[3], &p3_state_output_values[i][0]);
                state_output_values[i][1]
                    .assign_masked(&flag_values[3], &p3_state_output_values[i][1]);
                state_output_values[i][0]
                    .assign_masked(&flag_values[4], &p4_state_output_values[i][0]);
                state_output_values[i][1]
                    .assign_masked(&flag_values[4], &p4_state_output_values[i][1]);
            }
            for i in 0..3 {
                state_tmp_values[i][0].assign_masked(&flag_values[0], &p0_tmp_values[i][0]);
                state_tmp_values[i][1].assign_masked(&flag_values[0], &p0_tmp_values[i][1]);
                state_tmp_values[i][0].assign_masked(&flag_values[1], &p1_tmp_values[i][0]);
                state_tmp_values[i][1].assign_masked(&flag_values[1], &p1_tmp_values[i][1]);
                state_tmp_values[i][0].assign_masked(&flag_values[2], &p2_tmp_values[i][0]);
                state_tmp_values[i][1].assign_masked(&flag_values[2], &p2_tmp_values[i][1]);
                state_tmp_values[i][0].assign_masked(&flag_values[3], &p3_tmp_values[i][0]);
                state_tmp_values[i][1].assign_masked(&flag_values[3], &p3_tmp_values[i][1]);
                state_tmp_values[i][0].assign_masked(&flag_values[4], &p4_tmp_values[i][0]);
                state_tmp_values[i][1].assign_masked(&flag_values[4], &p4_tmp_values[i][1]);
            }
            (state_output_values, state_tmp_values)
        };
        for (state_output, state_output_value) in state_outputs.into_iter().zip(state_output_values)
        {
            placer.assign_u32_from_u16_parts(
                state_output.low32.0.map(|x| x.get_variable()),
                &state_output_value[0],
            );
            placer.assign_u32_from_u16_parts(
                state_output.high32.0.map(|x| x.get_variable()),
                &state_output_value[1],
            );
        }
        for (state_tmp, state_tmp_value) in state_tmps.into_iter().zip(state_tmp_values) {
            placer.assign_u32_from_u16_parts(
                state_tmp.low32.0.map(|x| x.get_variable()),
                &state_tmp_value[0],
            );
            placer.assign_u32_from_u16_parts(
                state_tmp.high32.0.map(|x| x.get_variable()),
                &state_tmp_value[1],
            );
        }
    };
    cs.set_values(value_fn);

    // STEP2: WE PERFORM EQUIVALENT OF 5 XORS + ROTATION (a, b, c)
    // dbg!(control, precompile_bitmask, iter_bitmask, state_inputs, state_outputs, state_tmps);
    let precompile_flags = [
        is_iota_columnxor,
        is_columnmix,
        is_theta_rho,
        is_chi1,
        is_chi2,
    ];
    let precompile_rotation_flags = [
        is_iota_columnxor,
        is_columnmix,
        is_theta_rho_iter0,
        is_theta_rho_iter1,
        is_theta_rho_iter2,
        is_theta_rho_iter3,
        is_theta_rho_iter4,
        is_chi1,
        is_chi2,
    ];
    // {
    //     println!("precompile_flags: {:?}", precompile_flags.map(|b| b.get_value(cs)));
    //     println!("precompile_rotation_flags: {:?}", precompile_rotation_flags.map(|b| b.get_value(cs)));
    // }

    // 1
    if unsafe { DEBUG } {
        println!("\tbinop 1..");
    }
    enforce_binop(
        cs,
        precompile_flags,
        [
            TableType::XorSpecialIota,
            TableType::Xor,
            TableType::Xor,
            TableType::AndN,
            TableType::AndN,
        ],
        precompile_rotation_flags,
        [0, 63, 0, 1, 62, 28, 27, 0, 0],
        [
            (p0_idx0, p0_round_constant_control_reg, p0_idx0_new),
            (p1_25_new, p1_25, p1_27),
            (p2_idx0, p2_idcol, p2_idx0_new),
            (p3_idx1, p3_idx2, p3_25_new),
            (p4_idx4, p4_idx0, p4_tmp1),
        ],
    );
    // 2
    if unsafe { DEBUG } {
        println!("\tbinop 2..");
    }
    enforce_binop(
        cs,
        precompile_flags,
        [
            TableType::Xor,
            TableType::Xor,
            TableType::Xor,
            TableType::AndN,
            TableType::Xor,
        ],
        precompile_rotation_flags,
        [0, 63, 36, 44, 6, 55, 20, 0, 0],
        [
            (p0_idx0_new, p0_idx5, p0_tmp1),
            (p1_27_new, p1_27, p1_29),
            (p2_idx5, p2_idcol, p2_idx5_new),
            (p3_idx2, p3_idx3, p3_tmp1),
            (p4_idx3, p4_tmp1, p4_idx3_new),
        ],
    );
    // 3
    if unsafe { DEBUG } {
        println!("\tbinop 3..");
    }
    enforce_binop(
        cs,
        precompile_flags,
        [
            TableType::Xor,
            TableType::Xor,
            TableType::Xor,
            TableType::Xor,
            TableType::AndN,
        ],
        precompile_rotation_flags,
        [0, 63, 3, 10, 43, 25, 39, 0, 0],
        [
            (p0_tmp1, p0_idx10, p0_tmp2),
            (p1_29_new, p1_29, p1_26),
            (p2_idx10, p2_idcol, p2_idx10_new),
            (p3_idx1, p3_tmp1, p3_idx1_new),
            (p4_idx0, p4_26, p4_tmp2),
        ],
    );
    // 4
    if unsafe { DEBUG } {
        println!("\tbinop 4..");
    }
    enforce_binop(
        cs,
        precompile_flags,
        [
            TableType::Xor,
            TableType::Xor,
            TableType::Xor,
            TableType::AndN,
            TableType::Xor,
        ],
        precompile_rotation_flags,
        [0, 63, 41, 45, 15, 21, 8, 0, 0],
        [
            (p0_tmp2, p0_idx15, p0_tmp3),
            (p1_26_new, p1_26, p1_28),
            (p2_idx15, p2_idcol, p2_idx15_new),
            (p3_idx3, p3_idx4, p3_tmp2),
            (p4_idx4, p4_tmp2, p4_idx4_new),
        ],
    );
    // 5
    if unsafe { DEBUG } {
        println!("\tbinop 5..");
    }
    enforce_binop(
        cs,
        precompile_flags,
        [
            TableType::Xor,
            TableType::Xor,
            TableType::Xor,
            TableType::Xor,
            TableType::Xor,
        ],
        precompile_rotation_flags,
        [0, 63, 18, 2, 61, 56, 14, 0, 0],
        [
            (p0_tmp3, p0_idx20, p0_idcol_new),
            (p1_28_new, p1_28, p1_25),
            (p2_idx20, p2_idcol, p2_idx20_new),
            (p3_idx2, p3_tmp2, p3_idx2_new),
            (p4_idx0, p4_25, p4_idx0_new),
        ],
    );

    let s0 = Box::new([
        (p0_idx5, p0_idx5_new),
        (p0_idx10, p0_idx10_new),
        (p0_idx15, p0_idx15_new),
        (p0_idx20, p0_idx20_new),
    ]);
    let s1 = Box::new([(p1_0, p1_0_new)]);
    let s2 = Box::new([(p2_idcol, p2_idcol_new)]);
    let s3 = Box::new([
        (p3_idx3, p3_idx3_new),
        (p3_idx4, p3_idx4_new),
        (p3_idx1, p3_26_new),
    ]);
    let s4 = Box::new([
        (p4_25, p4_25_new),
        (p4_26, p4_26_new),
        (p4_idx0_new, p4_27_new),
    ]);
    // WE ALSO CANNOT FORGET TO COPY OVER UNTOUCHED VALUES BACK TO THEIR RAM ARGUMENT WRITE-SET
    enforce_copies(cs, precompile_flags, [&*s0, &*s1, &*s2, &*s3, &*s4]);

    if unsafe { DEBUG } {
        unsafe {
            let expected_control = DEBUG_CONTROL;
            let begotten_control = cs.get_value(control).unwrap().as_u64_reduced() as u16;
            let expected_state_indexes = DEBUG_INDEXES;
            let expected_state_inputs = DEBUG_INDEXES.map(|i| DEBUG_INPUT_STATE[i]);
            let begotten_state_indexes =
                state_indexes.map(|x| cs.get_value(x).unwrap().as_u64_reduced() as usize);
            let begotten_state_inputs = state_inputs.map(|x| x.get_value_unsigned(cs).unwrap());
            assert!(expected_control == begotten_control);
            assert!(expected_state_indexes == begotten_state_indexes);
            assert!(expected_state_inputs == begotten_state_inputs);

            let expected_state_outputs = DEBUG_INDEXES.map(|i| DEBUG_OUTPUT_STATE[i]);
            let begotten_state_outputs = state_outputs.map(|x| x.get_value_unsigned(cs).unwrap());
            assert!(expected_state_outputs == begotten_state_outputs, "wanted state updates {expected_state_outputs:?} but got {begotten_state_outputs:?}");

            let expected_control_next = DEBUG_CONTROL_NEXT;
            let begotten_control_next = cs.get_value(control_next).unwrap().as_u64_reduced() as u16;
            assert!(
                expected_control_next == begotten_control_next,
                "wanted control update {expected_control_next} but got {begotten_control_next}"
            );
        }
    }
}

fn enforce_binop<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    precompile_flags: [Boolean; 5],
    precompile_table_ids: [TableType; 5],
    precompile_rotation_flags: [Boolean; 9],
    precompile_rotation_constants: [u64; 9],
    input_output_candidates: [(LongRegister<F>, LongRegister<F>, LongRegister<F>); 5],
) {
    debug_assert!(precompile_rotation_constants.into_iter().all(|c| c < 64));
    let in1_u8 = LongRegisterDecomposition::new(cs);
    let in2_u8 = LongRegisterDecomposition::new(cs);

    // just set in1/in2 u8 decompositions
    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let zero_u32 = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
        let mut in1_low32_value = zero_u32.clone();
        let mut in1_high32_value = zero_u32.clone();
        let mut in2_low32_value = zero_u32.clone();
        let mut in2_high32_value = zero_u32;
        for (flag, (possible_in1, possible_in2, _)) in
            precompile_flags.into_iter().zip(input_output_candidates)
        {
            let flag_value = placer.get_boolean(flag.get_variable().unwrap());
            let possible_in1_low32_value =
                placer.get_u32_from_u16_parts(possible_in1.low32.0.map(|x| x.get_variable()));
            let possible_in1_high32_value =
                placer.get_u32_from_u16_parts(possible_in1.high32.0.map(|x| x.get_variable()));
            let possible_in2_low32_value =
                placer.get_u32_from_u16_parts(possible_in2.low32.0.map(|x| x.get_variable()));
            let possible_in2_high32_value =
                placer.get_u32_from_u16_parts(possible_in2.high32.0.map(|x| x.get_variable()));
            in1_low32_value.assign_masked(&flag_value, &possible_in1_low32_value);
            in1_high32_value.assign_masked(&flag_value, &possible_in1_high32_value);
            in2_low32_value.assign_masked(&flag_value, &possible_in2_low32_value);
            in2_high32_value.assign_masked(&flag_value, &possible_in2_high32_value);
        }
        // now can assign
        let zero_u8 = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8::constant(0);
        let in1_u8_values = {
            let mut chunks: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8; 8] =
                from_fn(|_| zero_u8.clone());
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
            let mut chunks: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U8; 8] =
                from_fn(|_| zero_u8.clone());
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
    };
    cs.set_values(value_fn);

    // FIRST we perform the main binary op lookups
    let bin_out_u8 = {
        let out_u8 = LongRegisterDecomposition::new(cs);
        let id = cs.choose_from_orthogonal_variants(
            &precompile_flags,
            &precompile_table_ids.map(TableType::to_num),
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
            cs.set_variables_from_lookup_constrained(lookup_inputs, lookup_outputs, id);
        }
        out_u8
    };
    // SECOND we optionally rotate (this can be merged into above lookups once we upgrade air_compiler backend)
    let (rot_out_u16, rot_out_u16_boundary_flags) = {
        let rot_const_mod16 = {
            let mut rot_const_mod16 = Constraint::empty();
            for (flag, constant) in precompile_rotation_flags
                .into_iter()
                .zip(precompile_rotation_constants)
            {
                rot_const_mod16 = rot_const_mod16 + Term::from(flag) * Term::from(constant % 16);
            }
            rot_const_mod16
        };
        if unsafe { DEBUG } {
            println!("\t\trot_const_mod16: {:?}", rot_const_mod16.get_value(cs));
        }
        let [is_rot_lt16, is_rot_lt32, is_rot_lt48, is_rot_lt64] = {
            let mut rot_bounds: [Constraint<F>; 4] = from_fn(|_| Constraint::empty());
            for (flag, constant) in precompile_rotation_flags
                .into_iter()
                .zip(precompile_rotation_constants)
            {
                if constant < 16 {
                    rot_bounds[0] = rot_bounds[0].clone() + Term::from(flag);
                } else if constant < 32 {
                    rot_bounds[1] = rot_bounds[1].clone() + Term::from(flag);
                } else if constant < 48 {
                    rot_bounds[2] = rot_bounds[2].clone() + Term::from(flag);
                } else if constant < 64 {
                    rot_bounds[3] = rot_bounds[3].clone() + Term::from(flag);
                } else {
                    unreachable!()
                }
            }
            rot_bounds
        };
        let in_u16 = [
            Constraint::from(bin_out_u8.low32[0])
                + Term::from(1 << 8) * Term::from(bin_out_u8.low32[1])
                + Term::from(1 << 16) * rot_const_mod16.clone(),
            Constraint::from(bin_out_u8.low32[2])
                + Term::from(1 << 8) * Term::from(bin_out_u8.low32[3])
                + Term::from(1 << 16) * rot_const_mod16.clone(),
            Constraint::from(bin_out_u8.high32[0])
                + Term::from(1 << 8) * Term::from(bin_out_u8.high32[1])
                + Term::from(1 << 16) * rot_const_mod16.clone(),
            Constraint::from(bin_out_u8.high32[2])
                + Term::from(1 << 8) * Term::from(bin_out_u8.high32[3])
                + Term::from(1 << 16) * rot_const_mod16,
        ];
        let out_u16rot = LongRegisterRotation::new(cs);
        let id = TableType::RotL;
        let tuples = [
            (
                in_u16[0].clone(),
                out_u16rot.chunks_u16[0][0],
                out_u16rot.chunks_u16[0][1],
            ),
            (
                in_u16[1].clone(),
                out_u16rot.chunks_u16[1][0],
                out_u16rot.chunks_u16[1][1],
            ),
            (
                in_u16[2].clone(),
                out_u16rot.chunks_u16[2][0],
                out_u16rot.chunks_u16[2][1],
            ),
            (
                in_u16[3].clone(),
                out_u16rot.chunks_u16[3][0],
                out_u16rot.chunks_u16[3][1],
            ),
        ];
        for tuple in tuples {
            let lookup_inputs = [tuple.0].map(LookupInput::from);
            let lookup_outputs = [tuple.1, tuple.2].map(|x| x.get_variable());
            cs.set_variables_from_lookup_constrained(lookup_inputs, lookup_outputs, id.to_num());
        }
        (
            out_u16rot,
            [is_rot_lt16, is_rot_lt32, is_rot_lt48, is_rot_lt64],
        )
    };
    // FINALLY, we enforce manual routing!
    let (in1, in2, out) = (
        in1_u8.complete_composition(),
        in2_u8.complete_composition(),
        rot_out_u16.complete_rotation(rot_out_u16_boundary_flags),
    );
    let (in1_candidate, in2_candidate, out_candidate) = {
        let mut in1_candidate: [Constraint<F>; 4] = from_fn(|_| Constraint::empty());
        let mut in2_candidate: [Constraint<F>; 4] = from_fn(|_| Constraint::empty());
        let mut out_candidate: [Constraint<F>; 4] = from_fn(|_| Constraint::empty());
        for (flag, (in1_u64, in2_u64, out_u64)) in
            precompile_flags.into_iter().zip(input_output_candidates)
        {
            in1_candidate[0] =
                in1_candidate[0].clone() + Constraint::from(flag) * Term::from(in1_u64.low32.0[0]);
            in1_candidate[1] =
                in1_candidate[1].clone() + Constraint::from(flag) * Term::from(in1_u64.low32.0[1]);
            in1_candidate[2] =
                in1_candidate[2].clone() + Constraint::from(flag) * Term::from(in1_u64.high32.0[0]);
            in1_candidate[3] =
                in1_candidate[3].clone() + Constraint::from(flag) * Term::from(in1_u64.high32.0[1]);

            in2_candidate[0] =
                in2_candidate[0].clone() + Constraint::from(flag) * Term::from(in2_u64.low32.0[0]);
            in2_candidate[1] =
                in2_candidate[1].clone() + Constraint::from(flag) * Term::from(in2_u64.low32.0[1]);
            in2_candidate[2] =
                in2_candidate[2].clone() + Constraint::from(flag) * Term::from(in2_u64.high32.0[0]);
            in2_candidate[3] =
                in2_candidate[3].clone() + Constraint::from(flag) * Term::from(in2_u64.high32.0[1]);

            out_candidate[0] =
                out_candidate[0].clone() + Constraint::from(flag) * Term::from(out_u64.low32.0[0]);
            out_candidate[1] =
                out_candidate[1].clone() + Constraint::from(flag) * Term::from(out_u64.low32.0[1]);
            out_candidate[2] =
                out_candidate[2].clone() + Constraint::from(flag) * Term::from(out_u64.high32.0[0]);
            out_candidate[3] =
                out_candidate[3].clone() + Constraint::from(flag) * Term::from(out_u64.high32.0[1]);
        }
        (in1_candidate, in2_candidate, out_candidate)
    };
    if unsafe { DEBUG } {
        println!(
            "\t\tprecompile_flags: {:?}",
            precompile_flags.map(|b| b.get_value(cs).unwrap())
        );
        println!(
            "\t\tprecompile_rotation_flags: {:?}",
            precompile_rotation_flags.map(|b| b.get_value(cs).unwrap())
        );
        println!(
            "\t\tin1_candidate: {:?}",
            in1_candidate.clone().map(|con| con.get_value(cs).unwrap())
        );
        println!(
            "\t\tin1: {:?}",
            in1.clone().map(|con| con.get_value(cs).unwrap())
        );
        println!(
            "\t\tin2_candidate: {:?}",
            in2_candidate.clone().map(|con| con.get_value(cs).unwrap())
        );
        println!(
            "\t\tin2: {:?}",
            in2.clone().map(|con| con.get_value(cs).unwrap())
        );
        println!(
            "\t\tbin_out_u8: {:?}",
            bin_out_u8
                .complete_composition()
                .map(|con| con.get_value(cs).unwrap())
        );
        println!(
            "\t\trot_out_u16: {:?}",
            rot_out_u16
                .chunks_u16
                .map(|x| x.map(|y| y.get_value(cs).unwrap()))
        );
        println!(
            "\t\tout_candidate: {:?}",
            out_candidate.clone().map(|con| con.get_value(cs).unwrap())
        );
        println!(
            "\t\tout: {:?}",
            out.clone().map(|con| con.get_value(cs).unwrap())
        );
    }
    for i in 0..4 {
        cs.add_constraint(in1[i].clone() - in1_candidate[i].clone());
        cs.add_constraint(in2[i].clone() - in2_candidate[i].clone());
        cs.add_constraint(out[i].clone() - out_candidate[i].clone());
    }
}

fn enforce_copies<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    precompile_flags: [Boolean; 5],
    input_output_candidates: [&'_ [(LongRegister<F>, LongRegister<F>)]; 5],
) {
    for (flag, candidates) in precompile_flags.into_iter().zip(input_output_candidates) {
        for (in_u64, out_u64) in candidates {
            // dbg!(in_u64, out_u64, flag);
            cs.add_constraint(
                Constraint::from(flag)
                    * (Term::from(in_u64.low32.0[0]) - Term::from(out_u64.low32.0[0])),
            );
            cs.add_constraint(
                Constraint::from(flag)
                    * (Term::from(in_u64.low32.0[1]) - Term::from(out_u64.low32.0[1])),
            );
            cs.add_constraint(
                Constraint::from(flag)
                    * (Term::from(in_u64.high32.0[0]) - Term::from(out_u64.high32.0[0])),
            );
            cs.add_constraint(
                Constraint::from(flag)
                    * (Term::from(in_u64.high32.0[1]) - Term::from(out_u64.high32.0[1])),
            );
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

    #[test]
    fn stress_test_compile_keccak_special5() {
        use crate::cs::witness_placer::cs_debug_evaluator::CSDebugWitnessEvaluator;
        fn to_u16_chunks(x: u64) -> [u16; 4] {
            [
                x as u16,
                (x >> 16) as u16,
                (x >> 32) as u16,
                (x >> 48) as u16,
            ]
        }
        unsafe {
            DEBUG = true;
        }
        for i in 0..DEBUG_INFO.len() {
            println!("trying out debug info {i}/{}..", DEBUG_INFO.len());
            unsafe {
                update_select(i);
                println!(
                    "\tgiven_inputs: {:?}",
                    DEBUG_INDEXES.map(|i| DEBUG_INPUT_STATE[i])
                );
                println!(
                    "\t.           : {:?}",
                    DEBUG_INDEXES.map(|i| to_u16_chunks(DEBUG_INPUT_STATE[i]))
                );
                println!(
                    "\texpected_outputs: {:?}",
                    DEBUG_INDEXES.map(|i| DEBUG_OUTPUT_STATE[i])
                );
                println!(
                    "\t.               : {:?}",
                    DEBUG_INDEXES.map(|i| to_u16_chunks(DEBUG_OUTPUT_STATE[i]))
                );
            }
            let mut cs = BasicAssembly::<Mersenne31Field>::new();
            cs.witness_placer = Some(CSDebugWitnessEvaluator::new()); // necessary to debug witnessgen
            define_keccak_special5_delegation_circuit(&mut cs);
            let (circuit_output, _) = cs.finalize();
            let _compiled =
                OneRowCompiler::default().compile_to_evaluate_delegations(circuit_output, 20);
        }
        unsafe {
            DEBUG = false;
        }
    }
}
