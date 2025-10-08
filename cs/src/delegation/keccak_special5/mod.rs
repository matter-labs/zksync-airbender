use super::*;
use crate::cs::circuit::*;
use crate::cs::witness_placer::WitnessComputationCore;
use crate::cs::witness_placer::WitnessComputationalField;
use crate::cs::witness_placer::WitnessComputationalInteger;
use crate::cs::witness_placer::WitnessComputationalU16;
use crate::cs::witness_placer::WitnessComputationalU32;
use crate::cs::witness_placer::WitnessComputationalU8;
use crate::cs::witness_placer::WitnessMask;
use crate::cs::witness_placer::WitnessPlacer;
use crate::cs::witness_placer::WitnessTypeSet;
use crate::definitions::*;
use crate::one_row_compiler::LookupInput;
use crate::types::Boolean;
use crate::types::Num;
// use common_constants::delegation_types::keccak_special5::*;
use core::array::from_fn;

#[allow(unused)]
unsafe fn update_select(select: usize) {
    DEBUG_CONTROL = {
        let precompile: u16 = DEBUG_INFO[select].0;
        let iter: u16 = DEBUG_INFO[select].1;
        let round: u16 = DEBUG_INFO[select].2;
        precompile | iter << 3 | round << 6
    };
    DEBUG_INDEXES = DEBUG_INFO[select].3;
    DEBUG_INPUT_STATE = DEBUG_INFO[select].4;
    DEBUG_OUTPUT_STATE = DEBUG_INFO[select].5;
    DEBUG_CONTROL_NEXT = {
        let precompile = DEBUG_INFO[select].6;
        let iter = DEBUG_INFO[select].7;
        let round = DEBUG_INFO[select].8;
        precompile | iter << 3 | round << 6
    };
}
static mut DEBUG_CONTROL: u16 = 0;
static mut DEBUG_CONTROL_NEXT: u16 = 0;
static mut DEBUG_INDEXES: [usize; 6] = [0; 6];
static mut DEBUG_INPUT_STATE: [u64; 31] = [0; 31];
static mut DEBUG_OUTPUT_STATE: [u64; 31] = [0; 31];
mod debug_info;
use debug_info::DEBUG_INFO;

// INFO:
// - 7 "precompile ops" packed into one circuit
// - max of 5 u64 bitwise operations
// - max of 6 u64 R/W memory accesses (+ 2 u32 register accesses)
// - repeatedly called (1 keccak = 649 precompile cycles + 2 normal prep cycles)

// ABI:
// - 1 register (x10) for 11-bit control info (3-bit precompile || 3-bit iter || 5-bit round)
//                        this register is bumped automatically by the circuit,
//                        which saves 50% of total RV cycles during execution
// - 1 register (x11) for state pointer (aligned s.t. state[30] does not overflow low 16 bits)

// TABLES (2^21):
// - 3 tables for extraction of state indexes (same table parametrised to 3 possible pairs) (2^12 * 3)
// - one table for 8-bit Iota's xor with round constant (2^16)
// - one table for 8-bit normal xor (2^16)
// - one table for 8-bit andn (2^16)
// - one table for 16-bit rotation with 4-bit rotation constant (2^20)

// CIRCUIT:
// - get control param (x10.low) + state pointer (x11) with 2 32-bit mem. accesses
// - extract the 6 indices to fixed variables -> get 6 u64 R/W (word1..word6) inputs + create outputs
// - extract precompile bitmask flags, to make u64 memory routing cheap
// - extract iteration bitmask flags, to make rotations cheap (rotation output composition becomes linear combination)
// - bump control param back into x10.low, for next precompile call (basically free)
// - we perform at most 5 u64 binops -> 5 * 8x8-bit lookups * 8 -> 5 * 3 * 8 variables
// - each binop can be u64 rotation -> 5 * 16+4-bit lookup * 4 -> 5 * 3 * 4 variables (50% usage, 29% of cycles)
// - dynamic selection of binop/rotation is cheaply encoded using composition constrains of degree 2
// - dynamic in/out logic across precompiles is cheaply encoded using routing constraints of degree 2

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
    fn from(vars: [Variable; 8]) -> LongRegisterDecomposition<F> {
        let low32_vars: [Variable; 4] = vars[..4].try_into().unwrap();
        let high32_vars: [Variable; 4] = vars[4..].try_into().unwrap();
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
    fn from(leftvars: [Variable; 4], rightvars: [Variable; 4]) -> LongRegisterRotation<F> {
        let vars = from_fn(|i| [leftvars[i], rightvars[i]].map(Num::Var));
        LongRegisterRotation { chunks_u16: vars }
    }
    fn complete_rotation(&self, u16_boundary_flags: [Constraint<F>; 4]) -> [Constraint<F>; 4] {
        debug_assert!(u16_boundary_flags.iter().all(|x| x.degree() <= 1));
        // orthogonal flags, they assist with rotation composition
        let [is_rot_lt16, is_rot_lt32, is_rot_lt48, is_rot_lt64] = u16_boundary_flags;

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

pub fn define_keccak_special5_delegation_circuit<
    F: PrimeField,
    CS: Circuit<F>,
    const DEBUG: bool,
>(
    cs: &mut CS,
) {
    // add tables
    materialize_tables_into_cs(cs);

    // The only convention we must eventually satisfy is that if we do NOT process delegation request,
    // THEN all memory writes in ABI must be 0s.
    // This is handled automatically by a custom stage3 constraint to mask all mem accesses,
    // then you just need to ensure that all 0 execute flags does not break/unsatisfy the circuit.
    // Therefore: we CAN safely ignore this variable, but the circuit author must design the circuit carefully.
    let execute = cs.process_delegation_request();

    // FIRST: process all memory accesses
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

        if DEBUG {
            // set control using debugging stress test data
            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                let control_value =
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(
                        unsafe { DEBUG_CONTROL },
                    );
                placer.assign_u16(control_reg[0], &control_value);
            };
            cs.set_values(value_fn);
        }

        // set x10_next
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            // fetch inputs
            let (precompile_value, iter_value, round_value) = {
                let control_value = placer.get_u16(control_reg[0]);
                let mask3 =
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0b111);
                let precompile_value = control_value.and(&mask3);
                let iter_value = control_value.shr(3).and(&mask3);
                let round_value = control_value.shr(6);
                (precompile_value, iter_value, round_value)
            };

            // helpers
            let last_loop = iter_value.equal_to_constant(4);
            let one_value =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(1);
            let zero_value =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0);
            let precompile_bools: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask;
                7] = from_fn(|i| precompile_value.equal_to_constant(i as u16));

            // get output
            let control_next_value = {
                let precompile_next_value = {
                    let precompile_options = {
                        let advance = precompile_value.overflowing_add(&one_value).0;
                        let advance_after_loops =
                            <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                                &last_loop,
                                &advance,
                                &precompile_value,
                            );
                        let retreat_or_reset = {
                            let retreat = precompile_value.overflowing_sub(&one_value).0;
                            <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                                &last_loop,
                                &zero_value,
                                &retreat,
                            )
                        };
                        [
                            advance_after_loops.clone(),
                            advance.clone(),
                            advance.clone(),
                            advance_after_loops.clone(),
                            advance_after_loops,
                            advance,
                            retreat_or_reset,
                        ]
                    };
                    precompile_bools.iter().zip(precompile_options).fold(
                        zero_value.clone(),
                        |acc, (flag, option)| {
                            <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                                &flag, &option, &acc,
                            )
                        },
                    )
                };
                let iter_next_value = {
                    let iter_options = {
                        let advance_or_reset = {
                            let advance = iter_value.overflowing_add(&one_value).0;
                            <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                                &last_loop,
                                &zero_value,
                                &advance,
                            )
                        };
                        [
                            advance_or_reset.clone(),
                            iter_value.clone(),
                            iter_value.clone(),
                            advance_or_reset.clone(),
                            advance_or_reset.clone(),
                            iter_value.clone(),
                            advance_or_reset,
                        ]
                    };
                    precompile_bools.iter().zip(iter_options).fold(
                        zero_value.clone(),
                        |acc, (flag, option)| {
                            <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                                &flag, &option, &acc,
                            )
                        },
                    )
                };
                let round_next_value = {
                    let last_precompile_last_loop =
                        precompile_value.equal_to_constant(6).and(&last_loop);
                    let advance = round_value.overflowing_add(&one_value).0;
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                        &last_precompile_last_loop,
                        &advance,
                        &round_value,
                    )
                };
                precompile_next_value
                    .or(&iter_next_value.shl(3))
                    .or(&round_next_value.shl(6))
            };
            placer.assign_u16(control_reg_next[0], &control_next_value);
            placer.assign_u16(control_reg_next[1], &zero_value);
        };
        cs.set_values(value_fn);

        cs.add_constraint_allow_explicit_linear(Constraint::from(control_reg[1])); // we expect high 16 bits to be empty
        cs.add_constraint_allow_explicit_linear(Constraint::from(control_reg_next[1])); // we expect high 16 bits to be empty
        (control_reg[0], control_reg_next[0]) // only the low 11 bits contain control info
    };

    let state_indexes = {
        // we can't assign to these variables by lookup since these variables belong to memory subtree
        // so, they will be assigned through placeholder by cs.create_register_and_indirect_memory_accesses
        let [s1, s2, s3, s4, s5, s6] = from_fn(|_| cs.add_variable());
        {
            // control is properly range checked later by bitmasks, so don't worry :)
            let control_with_exe =
                Constraint::from(control) + Term::from(1 << 11) * Term::from(execute);
            let [s1, s2, s3, s4, s5, s6] = [s1, s2, s3, s4, s5, s6].map(Constraint::from);
            cs.enforce_lookup_tuple_for_fixed_table(
                &[control_with_exe.clone(), s1, s2].map(LookupInput::from),
                TableType::KeccakPermutationIndices12,
                false,
            );
            cs.enforce_lookup_tuple_for_fixed_table(
                &[control_with_exe.clone(), s3, s4].map(LookupInput::from),
                TableType::KeccakPermutationIndices34,
                false,
            );
            cs.enforce_lookup_tuple_for_fixed_table(
                &[control_with_exe, s5, s6].map(LookupInput::from),
                TableType::KeccakPermutationIndices56,
                false,
            );
        }
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
            indirects_alignment_log2: 8, // 256 bytes: 25 u64 state + 6 u64 scratch = 248 bytes
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

        if DEBUG {
            // set state_inputs based off of stress test data
            // first: re-set the index vars as they were overwritten by faulty simulator placeholder data
            assert!(!execute.get_value(cs).unwrap());
            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                let truebool =
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(true);
                placer.assign_mask(execute.get_variable().unwrap(), &truebool);
            };
            cs.set_values(value_fn);
            let control_with_exe =
                Constraint::from(control) + Term::from(1 << 11) * Term::from(execute);
            cs.peek_lookup_value_unconstrained_ext(
                &[LookupInput::from(control_with_exe.clone())],
                &[state_indexes[0], state_indexes[1]],
                TableType::KeccakPermutationIndices12.to_num(),
                execute,
            );
            cs.peek_lookup_value_unconstrained_ext(
                &[LookupInput::from(control_with_exe.clone())],
                &[state_indexes[2], state_indexes[3]],
                TableType::KeccakPermutationIndices34.to_num(),
                execute,
            );
            cs.peek_lookup_value_unconstrained_ext(
                &[LookupInput::from(control_with_exe)],
                &[state_indexes[4], state_indexes[5]],
                TableType::KeccakPermutationIndices56.to_num(),
                execute,
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

    // UNPACK THE CONTROL INTO FLAGS THAT WE NEED
    // TODO: ADD CONSTANTS
    let (precompile_bitmask, iter_bitmask, precompile, iter, round) = {
        // new control is precompile (3) || iter (3) || round (5), all are packed!!
        // we only unpack
        let precompile_bitmask: [Boolean; 7] = from_fn(|_| cs.add_boolean_variable());
        let precompile = {
            // WARNING: p0 remains unconstrained!
            precompile_bitmask
                .into_iter()
                .enumerate()
                .fold(Constraint::from(0), |acc, (i, bit)| {
                    acc + Term::from(i as u64) * Term::from(bit)
                })
        };
        let iter_bitmask: [Boolean; 5] = from_fn(|_| cs.add_boolean_variable());
        let iter = {
            // WARNING: i0 remains unconstrained!
            iter_bitmask
                .into_iter()
                .enumerate()
                .fold(Constraint::from(0), |acc, (i, bit)| {
                    acc + Term::from(i as u64) * Term::from(bit)
                })
        };
        let round_bits: [Boolean; 5] = from_fn(|_| cs.add_boolean_variable());
        let round = {
            round_bits
                .into_iter()
                .enumerate()
                .fold(Constraint::from(0), |acc, (i, bit)| {
                    acc + Term::from(1 << i) * Term::from(bit)
                })
        };

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            // fetch inputs
            let (precompile_value, iter_value, round_value) = {
                let mask3 =
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0b111);
                let control_value = placer.get_u16(control);
                let precompile_value = control_value.and(&mask3);
                let iter_value = control_value.shr(3).and(&mask3);
                let round_value = control_value.shr(6);
                (precompile_value, iter_value, round_value)
            };
            // decompose to bits/bitmasks
            let zero_bool =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
            let one_value =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(1);
            let mut precompile_bitmask_bools: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask; 7] = from_fn(|_| zero_bool.clone());
            let mut iter_bitmask_bools: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask; 5] = from_fn(|_| zero_bool.clone());
            let mut round_bools: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask;
                5] = from_fn(|_| zero_bool.clone());
            for i in 0..7 {
                precompile_bitmask_bools[i] = precompile_value.equal_to_constant(i as u16);
            }
            for i in 0..5 {
                iter_bitmask_bools[i] = iter_value.equal_to_constant(i as u16);
            }
            for i in 0..5 {
                round_bools[i] = round_value.shr(i as u32).and(&one_value).is_one();
            }
            // beware that keccak padding (inactive) mode does not follow correct bitmask rules
            let execute_bool = placer.get_boolean(execute.get_variable().unwrap());
            precompile_bitmask_bools[0] = precompile_bitmask_bools[0].and(&execute_bool);
            iter_bitmask_bools[0] = iter_bitmask_bools[0].and(&execute_bool);
            // assign bits/bitmasks
            for i in 0..7 {
                placer.assign_mask(
                    precompile_bitmask[i].get_variable().unwrap(),
                    &precompile_bitmask_bools[i],
                );
            }
            for i in 0..5 {
                placer.assign_mask(
                    iter_bitmask[i].get_variable().unwrap(),
                    &iter_bitmask_bools[i],
                );
            }
            for i in 0..5 {
                placer.assign_mask(round_bits[i].get_variable().unwrap(), &round_bools[i]);
            }
        };
        cs.set_values(value_fn);

        // compose, to give meaning to (almost) all the bits
        cs.add_constraint_allow_explicit_linear(
            precompile.clone()
                + Term::from(1 << 3) * iter.clone()
                + Term::from(1 << 6) * round.clone()
                - Term::from(control),
        );

        // as p0 and i0 are unconstrained, we give them meaning
        {
            let precompile_bitmask_sum = precompile_bitmask
                .iter()
                .fold(Constraint::from(0), |acc, &flag| acc + Term::from(flag));
            let iter_bitmask_sum = iter_bitmask
                .iter()
                .fold(Constraint::from(0), |acc, &flag| acc + Term::from(flag));
            cs.add_constraint(
                Constraint::from(execute) * (precompile_bitmask_sum.clone() - Term::from(1)),
            );
            cs.add_constraint(
                Constraint::from(execute) * (iter_bitmask_sum.clone() - Term::from(1)),
            );
            cs.add_constraint(Constraint::from(execute.toggle()) * precompile_bitmask_sum);
            cs.add_constraint(Constraint::from(execute.toggle()) * iter_bitmask_sum);
        }

        (precompile_bitmask, iter_bitmask, precompile, iter, round)
    };

    // we place bitmasks into individual Booleans for simplicity
    let [is_iota_columnxor, is_columnmix1, is_columnmix2, is_theta, is_rho, is_chi1, is_chi2] =
        precompile_bitmask;
    let [is_iter0, is_iter1, is_iter2, is_iter3, is_iter4] = iter_bitmask;

    // now we enforce the control_next bump
    {
        let precompile_next = precompile
            + (Term::from(is_columnmix1) + Term::from(is_columnmix2) + Term::from(is_chi1)) // precompiles that always advance
            + (Term::from(is_iota_columnxor) + Term::from(is_theta) + Term::from(is_rho)) * Term::from(is_iter4) // only advance after 5 loops
            - Term::from(is_chi2) * (Constraint::from(1) + Term::from(5)*Term::from(is_iter4)); // retreat always, and after 5 loops reset
        let iter_next = iter
            + (Term::from(is_iota_columnxor)
                + Term::from(is_theta)
                + Term::from(is_rho)
                + Term::from(is_chi2))
                * (Constraint::from(1) - Term::from(5) * Term::from(is_iter4)); // precompiles that advance always, and after 5 loops reset
        let round_next = round.clone() + Term::from(is_chi2) * Term::from(is_iter4); // only last precompile + last loop advances round
        cs.add_constraint(
            precompile_next + Term::from(1 << 3) * iter_next + Term::from(1 << 6) * round_next
                - Term::from(control_next),
        );
    }

    // derive flags needed to identify rotations for precompile 2
    let [is_rho_iter0, is_rho_iter1, is_rho_iter2, is_rho_iter3, is_rho_iter4] = [
        Boolean::and(&is_rho, &is_iter0, cs),
        Boolean::and(&is_rho, &is_iter1, cs),
        Boolean::and(&is_rho, &is_iter2, cs),
        Boolean::and(&is_rho, &is_iter3, cs),
        Boolean::and(&is_rho, &is_iter4, cs),
    ];

    // need an easy way to identify positions later on during manual routing constraints...
    // this is also a good sanity check to ensure we use all values appropriately!
    let [[p0_idx0, p0_idx5, p0_idx10, p0_idx15, p0_idx20, _p0_idcol], [p1_25, p1_26, p1_27, p1_28, p1_29, _p1_30], [p2_25, p2_26, p2_27, p2_28, p2_29, p2_30], [p3_idx0, p3_idx5, p3_idx10, p3_idx15, p3_idx20, p3_idcol], [p4_idx0, p4_idx5, p4_idx10, p4_idx15, p4_idx20, p4_25], [p5_idx1, p5_idx2, p5_idx3, p5_idx4, _p5_25, _p5_26], [p6_idx0, p6_idx3, p6_idx4, p6_25, p6_26, p6_27]] =
        [state_inputs; 7];
    let [[p0_idx0_new, p0_idx5_new, p0_idx10_new, p0_idx15_new, p0_idx20_new, p0_idcol_new], [p1_25_new, p1_26_new, p1_27_new, p1_28_new, p1_29_new, p1_30_new], [p2_25_new, p2_26_new, p2_27_new, p2_28_new, p2_29_new, p2_30_new], [p3_idx0_new, p3_idx5_new, p3_idx10_new, p3_idx15_new, p3_idx20_new, p3_idcol_new], [p4_idx0_new, p4_idx5_new, p4_idx10_new, p4_idx15_new, p4_idx20_new, p4_25_new], [p5_idx1_new, p5_idx2_new, p5_idx3_new, p5_idx4_new, p5_25_new, p5_26_new], [p6_idx0_new, p6_idx3_new, p6_idx4_new, p6_25_new, p6_26_new, p6_27_new]] =
        [state_outputs; 7];

    // for iota, we let the special xor table find the proper 64-bit value based on the round
    let p0_round_constant_control_reg = {
        let round_if_iter0 = cs.add_variable_from_constraint(round * Term::from(is_iter0)); // (might not be necessary but let's do it for safety)
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
        // let round_if_iter0 = round * Term::from(is_iter0); // (might not be necessary but let's do it for safety)
        // let chunks_u8: [Constraint<F>; 8] = from_fn(|i| round_if_iter0.clone() + Term::from(1<<5)*Term::from(i as u64));
        // let chunks_u16: [Num<F>; 4] = from_fn(|i| cs.add_variable_from_constraint(chunks_u8[i*2].clone() + Term::from(1<<8)*chunks_u8[i*2+1].clone())).map(Num::Var);
        LongRegister {
            low32: Register([chunks_u16[0], chunks_u16[1]]),
            high32: Register([chunks_u16[2], chunks_u16[3]]),
        }
    };

    // most precompile modes require extra space for intermediate results...
    let tmps: [LongRegister<F>; 3] = from_fn(|_| LongRegister::new(cs));
    let [[p0_tmp1, p0_tmp2, p0_tmp3], [p1_tmp1, p1_tmp2, _], [p2_tmp1, p2_tmp2, _], [p5_tmp1, p5_tmp2, _], [p6_tmp1, p6_tmp2, _]] =
        [tmps; _];

    // because witness gen is so painful for keccak, we batch scratch space for binops here too
    let binops_scratch_space: [([Variable; 8], [Variable; 8], [Variable; 8]); 5] = from_fn(|_| {
        (
            from_fn(|_| cs.add_variable()),
            from_fn(|_| cs.add_variable()),
            from_fn(|_| cs.add_variable()),
        )
    });
    let [binop1_scratch_space, binop2_scratch_space, binop3_scratch_space, binop4_scratch_space, binop5_scratch_space] =
        { binops_scratch_space };

    // set unconditional out+tmp u64 results
    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let tou16 = |u64_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32;
                          2]| {
            let [low32, high32] = u64_value;
            [
                low32.truncate(),
                low32.shr(16).truncate(),
                high32.truncate(),
                high32.shr(16).truncate(),
            ]
        };
        let tou8 = |u64_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32;
                         2]| {
            let [ll, lh, hl, hh] = tou16(u64_value);
            [
                ll.truncate(),
                ll.shr(8).truncate(),
                lh.truncate(),
                lh.shr(8).truncate(),
                hl.truncate(),
                hl.shr(8).truncate(),
                hh.truncate(),
                hh.shr(8).truncate(),
            ]
        };
        let rotl = |u64_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32;
                         2],
                    rot_const: u32| {
            // NB: U32::shr expected to behave like rust u32::unbounded_shr, otherwise rust's u32>>32 does not behave well
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
            let u16input = tou16(&u64_value);
            let zero =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(F::ZERO);
            let a: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field; 8] = {
                let rotconst_mod16 =
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(
                        rot_const % 16,
                    );
                let input_with_rotconst = u16input.clone()
                .map(|x| x.widen().or(&rotconst_mod16.shl(16)))
                .map(<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer);
                from_fn(|i| {
                    if i < 4 {
                        input_with_rotconst[i].clone()
                    } else {
                        zero.clone()
                    }
                })
            };
            let b: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field; 8] = {
                let left = u16input.clone()
                    .map(|x| x.shr(16 - rot_const % 16).widen())
                    .map(<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer);
                from_fn(|i| if i < 4 { left[i].clone() } else { zero.clone() })
            };
            let c: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field; 8] = {
                let right = u16input.clone().map(|x| x.shl(rot_const % 16).widen()).map(
                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer,
                );
                from_fn(|i| {
                    if i < 4 {
                        right[i].clone()
                    } else {
                        zero.clone()
                    }
                })
            };
            ([low32_value, high32_value], (a, b, c))
        };
        let xor = |a_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32; 2], b_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32; 2]| {
            let out = core::array::from_fn(|i| a_value[i].xor(&b_value[i]));
            let a = tou8(&a_value)
                .map(|x| x.widen().widen())
                .map(<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer);
            let b = tou8(&b_value)
                .map(|x| x.widen().widen())
                .map(<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer);
            let c = tou8(&out)
                .map(|x| x.widen().widen())
                .map(<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer);
            (out, (a, b, c))
        };
        let andn = |a_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32;
                         2],
                    b_value: &[<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32;
                         2]| {
            let out = core::array::from_fn(|i| a_value[i].not().and(&b_value[i]));
            let a = tou8(&a_value)
                .map(|x| x.widen().widen())
                .map(<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer);
            let b = tou8(&b_value)
                .map(|x| x.widen().widen())
                .map(<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer);
            let c = tou8(&out)
                .map(|x| x.widen().widen())
                .map(<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer);
            (out, (a, b, c))
        };

        let zero_u64 = [
            <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0),
            <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0),
        ];
        let zero_binop = {
            let zero_field =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::constant(F::ZERO);
            (
                from_fn(|_| zero_field.clone()),
                from_fn(|_| zero_field.clone()),
                from_fn(|_| zero_field.clone()),
            )
        };
        let state_input_values = state_inputs.map(|x| {
            [
                placer.get_u32_from_u16_parts(x.low32.0.map(|y| y.get_variable())),
                placer.get_u32_from_u16_parts(x.high32.0.map(|y| y.get_variable())),
            ]
        });
        let (state_output_values, tmp_values, binops_scratch_space_values) = {
            let (p0_state_output_values, p0_tmp_values, p0_binop_values) = {
                let [idx0_value, idx5_value, idx10_value, idx15_value, idx20_value, _idcol_value] =
                    state_input_values.clone();

                let (idx0_new_value, binop1) = {
                    let round_constant_value = {
                        let round_if_iter0_value = {
                            let is_iter0_value =
                                placer.get_boolean(is_iter0.get_variable().unwrap());
                            let round_value = {
                                let control_value: <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16 = placer.get_u16(control);
                                control_value.shr(6)
                            };
                            let zero_value = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0);
                            <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                                &is_iter0_value,
                                &round_value,
                                &zero_value,
                            )
                        };
                        let round_constants_adjusted_values = {
                            const ROUND_CONSTANTS_ADJUSTED: [u64; 25] = [
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
                                9223372039002292232,
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
                            let is_round_eqi = round_if_iter0_value.equal_to_constant(i as u16);
                            round_constant_value[0].assign_masked(&is_round_eqi, &rc_low32_value);
                            round_constant_value[1].assign_masked(&is_round_eqi, &rc_high32_value);
                        }
                        round_constant_value
                    };
                    let (out, (a, _b_faulty, c)) = xor(&idx0_value, &round_constant_value);
                    let binop = {
                        let rc_control_value = [
                            placer.get_u32_from_u16_parts(
                                p0_round_constant_control_reg
                                    .low32
                                    .0
                                    .map(|x| x.get_variable()),
                            ),
                            placer.get_u32_from_u16_parts(
                                p0_round_constant_control_reg
                                    .high32
                                    .0
                                    .map(|x| x.get_variable()),
                            ),
                        ];
                        let b = tou8(&rc_control_value)
                            .map(|x| x.widen().widen())
                            .map(<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::from_integer);
                        (a, b, c)
                    };
                    (out, binop)
                };
                let idx5_new_value = idx5_value.clone();
                let idx10_new_value = idx10_value.clone();
                let idx15_new_value = idx15_value.clone();
                let idx20_new_value = idx20_value.clone();
                let (tmp1_value, binop2) = xor(&idx0_new_value, &idx5_value);
                let (tmp2_value, binop3) = xor(&tmp1_value, &idx10_value);
                let (tmp3_value, binop4) = xor(&tmp2_value, &idx15_value);
                let (idcol_new_value, binop5) = xor(&tmp3_value, &idx20_value);
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
                    [binop1, binop2, binop3, binop4, binop5],
                )
            };
            let (p1_state_output_values, p1_tmp_values, p1_binop_values) = {
                let [i25_value, i26_value, i27_value, i28_value, i29_value, _i30_value] =
                    state_input_values.clone();

                let (i30_new_value, binop1) = rotl(&i25_value, 1);
                let (tmp1_value, binop2) = rotl(&i27_value, 1);
                let (i25_new_value, binop3) = xor(&i25_value, &tmp1_value);
                let (tmp2_value, binop4) = rotl(&i29_value, 1);
                let (i27_new_value, binop5) = xor(&i27_value, &tmp2_value);
                let i26_new_value = i26_value;
                let i28_new_value = i28_value;
                let i29_new_value = i29_value;
                (
                    [
                        i25_new_value,
                        i26_new_value,
                        i27_new_value,
                        i28_new_value,
                        i29_new_value,
                        i30_new_value,
                    ],
                    [tmp1_value, tmp2_value, zero_u64.clone()],
                    [binop1, binop2, binop3, binop4, binop5],
                )
            };
            let (p2_state_output_values, p2_tmp_values, p2_binop_values) = {
                let [i25_value, i26_value, i27_value, i28_value, i29_value, i30_value] =
                    state_input_values.clone();

                let (tmp1_value, binop1) = rotl(&i26_value, 1);
                let (i29_new_value, binop2) = xor(&i29_value, &tmp1_value);
                let (tmp2_value, binop3) = rotl(&i28_value, 1);
                let (i26_new_value, binop4) = xor(&i26_value, &tmp2_value);
                let (i28_new_value, binop5) = xor(&i28_value, &i30_value);
                let i25_new_value = i25_value;
                let i27_new_value = i27_value;
                let i30_new_value = i30_value;
                (
                    [
                        i25_new_value,
                        i26_new_value,
                        i27_new_value,
                        i28_new_value,
                        i29_new_value,
                        i30_new_value,
                    ],
                    [tmp1_value, tmp2_value, zero_u64.clone()],
                    [binop1, binop2, binop3, binop4, binop5],
                )
            };
            let (p3_state_output_values, p3_tmp_values, p3_binop_values) = {
                let [idx0_value, idx5_value, idx10_value, idx15_value, idx20_value, idcol_value] =
                    state_input_values.clone();

                let (idx0_new_value, binop1) = xor(&idx0_value, &idcol_value);
                let (idx5_new_value, binop2) = xor(&idx5_value, &idcol_value);
                let (idx10_new_value, binop3) = xor(&idx10_value, &idcol_value);
                let (idx15_new_value, binop4) = xor(&idx15_value, &idcol_value);
                let (idx20_new_value, binop5) = xor(&idx20_value, &idcol_value);
                let idcol_new_value = idcol_value;
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
                    [binop1, binop2, binop3, binop4, binop5],
                )
            };
            let (p4_state_output_values, p4_tmp_values, p4_binop_values) = {
                let [idx0_value, idx5_value, idx10_value, idx15_value, idx20_value, i25_value] =
                    state_input_values.clone();

                let iter_values =
                    iter_bitmask.map(|x| placer.get_boolean(x.get_variable().unwrap()));
                let fn_folder = |idx_value: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32;
                                     2]| {
                    move |(acc_value, acc_binop): (
                        [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32; 2],
                        (
                            [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field; _],
                            [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field; _],
                            [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field; _],
                        ),
                    ),
                          (iter_value, rot_const): (
                        &<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask,
                        u32,
                    )| {
                        let (possible_rotation_value, possible_binop) = rotl(&idx_value, rot_const);
                        (
                            from_fn(|i| {
                                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::select(&iter_value, &possible_rotation_value[i], &acc_value[i])
                            }),
                            (
                                from_fn(|i| {
                                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::select(&iter_value, &possible_binop.0[i], &acc_binop.0[i])
                                }),
                                from_fn(|i| {
                                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::select(&iter_value, &possible_binop.1[i], &acc_binop.1[i])
                                }),
                                from_fn(|i| {
                                    <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::select(&iter_value, &possible_binop.2[i], &acc_binop.2[i])
                                }),
                            ),
                        )
                    }
                };
                let (idx0_new_value, binop1) = {
                    iter_values.iter().zip([0, 1, 62, 28, 27]).fold(
                        (zero_u64.clone(), zero_binop.clone()),
                        fn_folder(idx0_value),
                    )
                };
                let (idx5_new_value, binop2) = {
                    iter_values.iter().zip([36, 44, 6, 55, 20]).fold(
                        (zero_u64.clone(), zero_binop.clone()),
                        fn_folder(idx5_value),
                    )
                };
                let (idx10_new_value, binop3) = {
                    iter_values.iter().zip([3, 10, 43, 25, 39]).fold(
                        (zero_u64.clone(), zero_binop.clone()),
                        fn_folder(idx10_value),
                    )
                };
                let (idx15_new_value, binop4) = {
                    iter_values.iter().zip([41, 45, 15, 21, 8]).fold(
                        (zero_u64.clone(), zero_binop.clone()),
                        fn_folder(idx15_value),
                    )
                };
                let (idx20_new_value, binop5) = {
                    iter_values.iter().zip([18, 2, 61, 56, 14]).fold(
                        (zero_u64.clone(), zero_binop.clone()),
                        fn_folder(idx20_value),
                    )
                };
                let i25_new_value = i25_value;
                (
                    [
                        idx0_new_value,
                        idx5_new_value,
                        idx10_new_value,
                        idx15_new_value,
                        idx20_new_value,
                        i25_new_value,
                    ],
                    [zero_u64.clone(), zero_u64.clone(), zero_u64.clone()],
                    [binop1, binop2, binop3, binop4, binop5],
                )
            };
            let (p5_state_output_values, p5_tmp_values, p5_binop_values) = {
                let [idx1_value, idx2_value, idx3_value, idx4_value, _i25_value, _i26_value] =
                    state_input_values.clone();

                let i26_new_value = idx1_value.clone();
                let (i25_new_value, binop1) = andn(&idx1_value, &idx2_value);
                let (tmp1_value, binop2) = andn(&idx2_value, &idx3_value);
                let (idx1_new_value, binop3) = xor(&idx1_value, &tmp1_value);
                let (tmp2_value, binop4) = andn(&idx3_value, &idx4_value);
                let (idx2_new_value, binop5) = xor(&idx2_value, &tmp2_value);
                let idx3_new_value = idx3_value;
                let idx4_new_value = idx4_value;
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
                    [binop1, binop2, binop3, binop4, binop5],
                )
            };
            let (p6_state_output_values, p6_tmp_values, p6_binop_values) = {
                let [idx0_value, idx3_value, idx4_value, i25_value, i26_value, i27_value] =
                    state_input_values;

                let (tmp1_value, binop1) = andn(&idx4_value, &idx0_value);
                let (idx3_new_value, binop2) = xor(&idx3_value, &tmp1_value);
                let (tmp2_value, binop3) = andn(&idx0_value, &i26_value);
                let (idx4_new_value, binop4) = xor(&idx4_value, &tmp2_value);
                let (idx0_new_value, binop5) = xor(&idx0_value, &i25_value);
                let i25_new_value = i25_value;
                let i26_new_value = i26_value;
                let i27_new_value = i27_value;
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
                    [binop1, binop2, binop3, binop4, binop5],
                )
            };

            let precompile_flag_values =
                precompile_bitmask.map(|x| placer.get_boolean(x.get_variable().unwrap()));
            let state_output_values: [_; 6] = from_fn(|i| {
                precompile_flag_values
                .iter()
                .zip([p0_state_output_values[i].clone(), p1_state_output_values[i].clone(), p2_state_output_values[i].clone(), p3_state_output_values[i].clone(), p4_state_output_values[i].clone(), p5_state_output_values[i].clone(), p6_state_output_values[i].clone()])
                .fold(zero_u64.clone(), |[acc_low32, acc_high32], (flag, [possible_low32, possible_high32])| {
                    [
                        <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::select(&flag, &possible_low32, &acc_low32),
                        <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::select(&flag, &possible_high32, &acc_high32),
                    ]
                })
            });
            let tmp_values: [_; 3] = from_fn(|i| {
                precompile_flag_values
                .iter()
                .zip([p0_tmp_values[i].clone(), p1_tmp_values[i].clone(), p2_tmp_values[i].clone(), p3_tmp_values[i].clone(), p4_tmp_values[i].clone(), p5_tmp_values[i].clone(), p6_tmp_values[i].clone()])
                .fold(zero_u64.clone(), |[acc_low32, acc_high32], (flag, [possible_low32, possible_high32])| {
                    [
                        <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::select(&flag, &possible_low32, &acc_low32),
                        <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U32::select(&flag, &possible_high32, &acc_high32),
                    ]
                })
            });
            let binop_values: [_; 5] = from_fn(|i| {
                precompile_flag_values
                .iter()
                .zip([p0_binop_values[i].clone(), p1_binop_values[i].clone(), p2_binop_values[i].clone(), p3_binop_values[i].clone(), p4_binop_values[i].clone(), p5_binop_values[i].clone(), p6_binop_values[i].clone()])
                .fold(zero_binop.clone(), |acc, (flag, possible_binop)| {
                    (
                        from_fn(|i| <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::select(&flag, &possible_binop.0[i], &acc.0[i])),
                        from_fn(|i| <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::select(&flag, &possible_binop.1[i], &acc.1[i])),
                        from_fn(|i| <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Field::select(&flag, &possible_binop.2[i], &acc.2[i]))
                    )
                })
            });
            (state_output_values, tmp_values, binop_values)
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
        for (tmp, tmp_value) in tmps.into_iter().zip(tmp_values) {
            placer.assign_u32_from_u16_parts(tmp.low32.0.map(|x| x.get_variable()), &tmp_value[0]);
            placer.assign_u32_from_u16_parts(tmp.high32.0.map(|x| x.get_variable()), &tmp_value[1]);
        }
        for ((a, b, c), (a_value, b_value, c_value)) in binops_scratch_space
            .into_iter()
            .zip(binops_scratch_space_values)
        {
            for i in 0..8 {
                placer.assign_field(a[i], &a_value[i]);
                placer.assign_field(b[i], &b_value[i]);
                placer.assign_field(c[i], &c_value[i]);
            }
        }
    };
    cs.set_values(value_fn);

    // STEP2: WE PERFORM EQUIVALENT OF 5 u64 BINARY OPERATIONS (over u8 chunks mostly, or u16 during rotation)
    // 1
    if DEBUG {
        println!("\tbinop 1..");
    }
    enforce_binop::<_, _, _, DEBUG>(
        cs,
        precompile_bitmask,
        [
            TableType::XorSpecialIota,
            TableType::RotL,
            TableType::RotL,
            TableType::Xor,
            TableType::RotL,
            TableType::AndN,
            TableType::AndN,
        ],
        [
            is_columnmix1,
            is_columnmix2,
            is_rho_iter0,
            is_rho_iter1,
            is_rho_iter2,
            is_rho_iter3,
            is_rho_iter4,
        ],
        [1, 1, 0, 1, 62, 28, 27],
        [
            (p0_idx0, p0_round_constant_control_reg.into(), p0_idx0_new),
            (p1_25, None, p1_30_new),
            (p2_26, None, p2_tmp1),
            (p3_idx0, p3_idcol.into(), p3_idx0_new),
            (p4_idx0, None, p4_idx0_new),
            (p5_idx1, p5_idx2.into(), p5_25_new),
            (p6_idx4, p6_idx0.into(), p6_tmp1),
        ],
        binop1_scratch_space,
    );
    // 2
    if DEBUG {
        println!("\tbinop 2..");
    }
    enforce_binop::<_, _, _, DEBUG>(
        cs,
        precompile_bitmask,
        [
            TableType::Xor,
            TableType::RotL,
            TableType::Xor,
            TableType::Xor,
            TableType::RotL,
            TableType::AndN,
            TableType::Xor,
        ],
        [
            is_columnmix1,
            is_rho_iter0,
            is_rho_iter1,
            is_rho_iter2,
            is_rho_iter3,
            is_rho_iter4,
        ],
        [1, 36, 44, 6, 55, 20],
        [
            (p0_idx0_new, p0_idx5.into(), p0_tmp1),
            (p1_27, None, p1_tmp1),
            (p2_29, p2_tmp1.into(), p2_29_new),
            (p3_idx5, p3_idcol.into(), p3_idx5_new),
            (p4_idx5, None, p4_idx5_new),
            (p5_idx2, p5_idx3.into(), p5_tmp1),
            (p6_idx3, p6_tmp1.into(), p6_idx3_new),
        ],
        binop2_scratch_space,
    );
    // 3
    if DEBUG {
        println!("\tbinop 3..");
    }
    enforce_binop::<_, _, _, DEBUG>(
        cs,
        precompile_bitmask,
        [
            TableType::Xor,
            TableType::Xor,
            TableType::RotL,
            TableType::Xor,
            TableType::RotL,
            TableType::Xor,
            TableType::AndN,
        ],
        [
            is_columnmix2,
            is_rho_iter0,
            is_rho_iter1,
            is_rho_iter2,
            is_rho_iter3,
            is_rho_iter4,
        ],
        [1, 3, 10, 43, 25, 39],
        [
            (p0_tmp1, p0_idx10.into(), p0_tmp2),
            (p1_25, p1_tmp1.into(), p1_25_new),
            (p2_28, None, p2_tmp2),
            (p3_idx10, p3_idcol.into(), p3_idx10_new),
            (p4_idx10, None, p4_idx10_new),
            (p5_idx1, p5_tmp1.into(), p5_idx1_new),
            (p6_idx0, p6_26.into(), p6_tmp2),
        ],
        binop3_scratch_space,
    );
    // 4
    if DEBUG {
        println!("\tbinop 4..");
    }
    enforce_binop::<_, _, _, DEBUG>(
        cs,
        precompile_bitmask,
        [
            TableType::Xor,
            TableType::RotL,
            TableType::Xor,
            TableType::Xor,
            TableType::RotL,
            TableType::AndN,
            TableType::Xor,
        ],
        [
            is_columnmix1,
            is_rho_iter0,
            is_rho_iter1,
            is_rho_iter2,
            is_rho_iter3,
            is_rho_iter4,
        ],
        [1, 41, 45, 15, 21, 8],
        [
            (p0_tmp2, p0_idx15.into(), p0_tmp3),
            (p1_29, None, p1_tmp2),
            (p2_26, p2_tmp2.into(), p2_26_new),
            (p3_idx15, p3_idcol.into(), p3_idx15_new),
            (p4_idx15, None, p4_idx15_new),
            (p5_idx3, p5_idx4.into(), p5_tmp2),
            (p6_idx4, p6_tmp2.into(), p6_idx4_new),
        ],
        binop4_scratch_space,
    );
    // 5
    if DEBUG {
        println!("\tbinop 5..");
    }
    enforce_binop::<_, _, _, DEBUG>(
        cs,
        precompile_bitmask,
        [
            TableType::Xor,
            TableType::Xor,
            TableType::Xor,
            TableType::Xor,
            TableType::RotL,
            TableType::Xor,
            TableType::Xor,
        ],
        [
            is_rho_iter0,
            is_rho_iter1,
            is_rho_iter2,
            is_rho_iter3,
            is_rho_iter4,
        ],
        [18, 2, 61, 56, 14],
        [
            (p0_tmp3, p0_idx20.into(), p0_idcol_new),
            (p1_27, p1_tmp2.into(), p1_27_new),
            (p2_28, p2_30.into(), p2_28_new),
            (p3_idx20, p3_idcol.into(), p3_idx20_new),
            (p4_idx20, None, p4_idx20_new),
            (p5_idx2, p5_tmp2.into(), p5_idx2_new),
            (p6_idx0, p6_25.into(), p6_idx0_new),
        ],
        binop5_scratch_space,
    );

    // WE ALSO CANNOT FORGET TO COPY OVER UNTOUCHED VALUES BACK TO THEIR RAM ARGUMENT WRITE-SET
    let p0_copies = Box::new([
        (p0_idx5, p0_idx5_new),
        (p0_idx10, p0_idx10_new),
        (p0_idx15, p0_idx15_new),
        (p0_idx20, p0_idx20_new),
    ]);
    let p1_copies = Box::new([(p1_26, p1_26_new), (p1_28, p1_28_new), (p1_29, p1_29_new)]);
    let p2_copies = Box::new([(p2_25, p2_25_new), (p2_27, p2_27_new), (p2_30, p2_30_new)]);
    let p3_copies = Box::new([(p3_idcol, p3_idcol_new)]);
    let p4_copies = Box::new([(p4_25, p4_25_new)]);
    let p5_copies = Box::new([
        (p5_idx1, p5_26_new),
        (p5_idx3, p5_idx3_new),
        (p5_idx4, p5_idx4_new),
    ]);
    let p6_copies = Box::new([(p6_25, p6_25_new), (p6_26, p6_26_new), (p6_27, p6_27_new)]);
    enforce_copies(
        cs,
        precompile_bitmask,
        [
            &*p0_copies,
            &*p1_copies,
            &*p2_copies,
            &*p3_copies,
            &*p4_copies,
            &*p5_copies,
            &*p6_copies,
        ],
    );

    if DEBUG {
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

fn enforce_binop<F: PrimeField, CS: Circuit<F>, const N: usize, const DEBUG: bool>(
    cs: &mut CS,
    precompile_flags: [Boolean; 7],
    precompile_table_ids: [TableType; 7],
    precompile_rotation_flags: [Boolean; N],
    precompile_rotation_constants: [u64; N],
    input_output_candidates: [(LongRegister<F>, Option<LongRegister<F>>, LongRegister<F>); 7],
    lookup_scratch_space: ([Variable; 8], [Variable; 8], [Variable; 8]),
) {
    {
        // input validation
        // precompile_rotation_constants must be valid u64 rotations
        // precompile_rotation_flags must be just an expansion of RotL precompile_flags
        // precompile_table_ids with RotL can't have the second input candidate
        assert!(precompile_rotation_constants.into_iter().all(|c| c < 64));
        let is_rot = precompile_flags.iter().zip(&precompile_table_ids).fold(
            Constraint::from(0),
            |acc, (&flag, &table)| {
                acc + Term::from(if table == TableType::RotL { 1 } else { 0 }) * Term::from(flag)
            },
        );
        let is_rot_ = precompile_rotation_flags
            .iter()
            .fold(Constraint::from(0), |acc, &flag| acc + Term::from(flag));
        cs.add_constraint_allow_explicit_linear_prevent_optimizations(is_rot - is_rot_);
        assert!(
            N >= input_output_candidates
                .iter()
                .filter(|(_in1, in2, _out)| in2.is_none())
                .count()
        );
        assert!(precompile_table_ids
            .iter()
            .zip(&input_output_candidates)
            .all(|(&table, &(_, in2, _))| in2.is_some() ^ (table == TableType::RotL)));
    }

    // NOTE: normally we would create all local variables and assign them here,
    //       but due to witness gen difficulties it's been moved to the external mega value_fn
    let (a, b, c) = lookup_scratch_space;

    // FIRST enforce all 8 binop lookups
    {
        let table_id = cs
            .choose_from_orthogonal_variants(
                &precompile_flags,
                &precompile_table_ids.map(TableType::to_num),
            )
            .get_variable();
        let tuples: [[Variable; 3]; 8] = from_fn(|i| [a[i], b[i], c[i]]);
        for tuple in tuples {
            cs.enforce_lookup_tuple_for_variable_table(&tuple.map(LookupInput::from), table_id);
        }
    }

    // SECOND we prepare some deg.1 rotation information
    let rot_const_mod16 = {
        let mut rot_const_mod16 = Constraint::from(0);
        for (flag, constant) in precompile_rotation_flags
            .into_iter()
            .zip(precompile_rotation_constants)
        {
            rot_const_mod16 += Term::from(flag) * Term::from(constant % 16);
        }
        rot_const_mod16
    };
    let rot_out_u16_boundary_flags = {
        let mut rot_bounds: [Constraint<F>; 4] = from_fn(|_| Constraint::from(0));
        for (flag, constant) in precompile_rotation_flags
            .into_iter()
            .zip(precompile_rotation_constants)
        {
            if constant < 16 {
                rot_bounds[0] += Term::from(flag);
            } else if constant < 32 {
                rot_bounds[1] += Term::from(flag);
            } else if constant < 48 {
                rot_bounds[2] += Term::from(flag);
            } else if constant < 64 {
                rot_bounds[3] += Term::from(flag);
            } else {
                unreachable!()
            }
        }
        rot_bounds
    };
    let is_rot = rot_out_u16_boundary_flags[0].clone()
        + rot_out_u16_boundary_flags[1].clone()
        + rot_out_u16_boundary_flags[2].clone()
        + rot_out_u16_boundary_flags[3].clone();

    // FINALLY, we enforce manual routing!
    let (in1, in2, out): ([Constraint<F>; 4], [Constraint<F>; 4], [Constraint<F>; 4]) = {
        // we need to extract some partial results first
        // when we deal with a column: it's either u8 input chunks or (u16 input || u4 rotconst) chunks
        // when we deal with b column: it's either u8 input chunks or u16 (left half rot) output chunks
        // when we deal with c column: it's either u8 output chunks or u16 (right half rot) output chunks
        let a_u8composition = LongRegisterDecomposition::from(a).complete_composition();
        let b_u8composition = LongRegisterDecomposition::from(b).complete_composition();
        let c_u8composition = LongRegisterDecomposition::from(c).complete_composition();
        let a_u16minusrotconst = {
            // only 4 lookup inputs are needed for rotation
            let a_u16: [Variable; 4] = a[..4].try_into().unwrap();
            a_u16.map(|var| Constraint::from(var) - Term::from(1 << 16) * rot_const_mod16.clone())
        };
        let bc_u16rotfinish_ifrot = {
            // only 4 lookup outputs are needed for rotation
            let b_u16left: [Variable; 4] = b[..4].try_into().unwrap();
            let c_u16right: [Variable; 4] = c[..4].try_into().unwrap();

            // keep in mind that .complete_rotation(rot_out_u16_boundary_flags) automatically masks to is_rot
            LongRegisterRotation::from(b_u16left, c_u16right)
                .complete_rotation(rot_out_u16_boundary_flags)
        };
        let not_rot = Constraint::from(Constraint::from(1) - is_rot.clone());

        // now we just choose the appropriate input/output based on which operation we perform
        (
            from_fn(|i| {
                not_rot.clone() * a_u8composition[i].clone()
                    + is_rot.clone() * a_u16minusrotconst[i].clone()
            }),
            from_fn(|i| not_rot.clone() * b_u8composition[i].clone()),
            from_fn(|i| {
                not_rot.clone() * c_u8composition[i].clone() + bc_u16rotfinish_ifrot[i].clone()
            }), // bc_.. is already masked
        )
    };
    let (in1_candidate, in2_candidate, out_candidate) = {
        let mut in1_candidate: [Constraint<F>; 4] = from_fn(|_| Constraint::from(0));
        let mut in2_candidate: [Constraint<F>; 4] = from_fn(|_| Constraint::from(0));
        let mut out_candidate: [Constraint<F>; 4] = from_fn(|_| Constraint::from(0));
        for (flag, (in1_u64, in2_u64, out_u64)) in
            precompile_flags.into_iter().zip(input_output_candidates)
        {
            in1_candidate[0] += Constraint::from(flag) * Term::from(in1_u64.low32.0[0]);
            in1_candidate[1] += Constraint::from(flag) * Term::from(in1_u64.low32.0[1]);
            in1_candidate[2] += Constraint::from(flag) * Term::from(in1_u64.high32.0[0]);
            in1_candidate[3] += Constraint::from(flag) * Term::from(in1_u64.high32.0[1]);

            if let Some(in2_u64) = in2_u64 {
                in2_candidate[0] += Constraint::from(flag) * Term::from(in2_u64.low32.0[0]);
                in2_candidate[1] += Constraint::from(flag) * Term::from(in2_u64.low32.0[1]);
                in2_candidate[2] += Constraint::from(flag) * Term::from(in2_u64.high32.0[0]);
                in2_candidate[3] += Constraint::from(flag) * Term::from(in2_u64.high32.0[1]);
            }

            out_candidate[0] += Constraint::from(flag) * Term::from(out_u64.low32.0[0]);
            out_candidate[1] += Constraint::from(flag) * Term::from(out_u64.low32.0[1]);
            out_candidate[2] += Constraint::from(flag) * Term::from(out_u64.high32.0[0]);
            out_candidate[3] += Constraint::from(flag) * Term::from(out_u64.high32.0[1]);
        }
        (in1_candidate, in2_candidate, out_candidate)
    };

    if DEBUG {
        println!(
            "\t\tprecompile_flags: {:?}",
            precompile_flags.map(|b| b.get_value(cs).unwrap())
        );
        println!(
            "\t\tprecompile_rotation_flags: {:?}",
            precompile_rotation_flags.map(|b| b.get_value(cs).unwrap())
        );
        println!("\t\trot_const_mod16: {:?}", rot_const_mod16.get_value(cs));
        println!("\t\tis_rot: {:?}", is_rot.get_value(cs).unwrap());
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
            LongRegisterDecomposition::from(c)
                .complete_composition()
                .map(|con| con.get_value(cs).unwrap())
        );
        println!(
            "\t\trot_out_u16: {:?}",
            LongRegisterRotation::from(b[..4].try_into().unwrap(), c[..4].try_into().unwrap())
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
    precompile_flags: [Boolean; 7],
    input_output_candidates: [&'_ [(LongRegister<F>, LongRegister<F>)]; 7],
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
        define_keccak_special5_delegation_circuit::<_, _, false>(&mut cs);
        let (circuit_output, _) = cs.finalize();
        let compiler = OneRowCompiler::default();
        let compiled = compiler.compile_to_evaluate_delegations(circuit_output, 20);
        serialize_to_file(&compiled, "keccak_delegation_layout.json");
    }

    #[test]
    fn keccak_delegation_get_witness_graph() {
        let ssa_forms = dump_ssa_witness_eval_form_for_delegation::<Mersenne31Field, _>(
            define_keccak_special5_delegation_circuit::<_, _, false>,
        );
        serialize_to_file(&ssa_forms, "keccak_delegation_ssa.json");
    }

    #[test]
    #[ignore = "slow comprehensive test"]
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
                println!(
                    "\texpected control update (bitform): {:011b} -> {:011b}",
                    DEBUG_CONTROL as u16, DEBUG_CONTROL_NEXT as u16
                );
            }
            let mut cs = BasicAssembly::<Mersenne31Field>::new();
            cs.witness_placer = Some(CSDebugWitnessEvaluator::new()); // necessary to debug witnessgen
            define_keccak_special5_delegation_circuit::<_, _, true>(&mut cs);
            let (circuit_output, _) = cs.finalize();
            let _compiled =
                OneRowCompiler::default().compile_to_evaluate_delegations(circuit_output, 20);
        }
    }
}
