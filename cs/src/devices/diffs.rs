use crate::constraint::Constraint;
use crate::constraint::Term;
use crate::cs::circuit::*;
use crate::cs::utils::*;
use crate::definitions::*;
use crate::types::*;
use field::PrimeField;

pub const PC_INC_STEP: u64 = 4;
pub const NUM_OF_MEMORY_ACCESSES_PER_CYCLE: usize = 3;

#[derive(Clone, Copy, Debug)]
pub enum RegisterLikeDiff<F: PrimeField> {
    Register(Register<F>),
    Bytes([Num<F>; REGISTER_BYTE_SIZE]),
}

impl<F: PrimeField> RegisterLikeDiff<F> {
    pub fn get_value<C: Circuit<F>>(&self, cs: &C) -> Option<u32> {
        match self {
            Self::Register(reg) => reg.get_value_unsigned(cs),
            Self::Bytes(els) => {
                let mut result: u32 = 0;
                for (i, el) in els.iter().enumerate() {
                    if let Some(value) = el.get_value(cs) {
                        let value = value.as_u64_reduced();
                        assert!(value < (1 << 8));
                        result += (value as u32) << (i * 4)
                    } else {
                        return None;
                    }
                }

                Some(result)
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum NextPcValue<F: PrimeField> {
    Default,
    Custom(Register<F>),
}

#[derive(Clone, Debug)]
pub struct CommonDiffs<F: PrimeField> {
    pub exec_flag: Boolean,
    pub trapped: Option<Boolean>,
    pub trap_reason: Option<Num<F>>,
    pub rd_value: Vec<([Constraint<F>; 2], Boolean)>,
    pub new_pc_value: NextPcValue<F>,
}

impl<F: PrimeField> CommonDiffs<F> {
    #[track_caller]
    pub fn select_final_rd_value<CS: Circuit<F>>(cs: &mut CS, sources: &[Self]) -> Register<F> {
        let result = std::array::from_fn(|word_idx| {
            let mut flags = vec![];
            let mut variants = vec![];
            for el in sources.iter() {
                for (rd_candidate, flag) in el.rd_value.iter() {
                    let limb_constraint = rd_candidate[word_idx].clone();
                    assert!(limb_constraint.degree() <= 1);
                    flags.push(*flag);
                    variants.push(limb_constraint);
                }
            }

            let result = cs.choose_from_orthogonal_variants_for_linear_terms(&flags, &variants);

            result
        });

        let new_reg_val = Register(result);

        new_reg_val
    }

    #[track_caller]
    pub fn select_final_pc_value<CS: Circuit<F>>(
        cs: &mut CS,
        sources: &[Self],
        default_next_pc: Register<F>,
    ) -> Register<F> {
        let mut default_case_exec_flags = vec![];
        let mut non_default_cases = vec![];

        for el in sources {
            match el.new_pc_value {
                NextPcValue::Default => {
                    default_case_exec_flags.push(el.exec_flag);
                }
                NextPcValue::Custom(diff) => {
                    non_default_cases.push((el.exec_flag, diff));
                }
            }
        }

        // just merge them

        let mut witness_sets_for_words = vec![];

        for (flag, diff) in non_default_cases.iter() {
            let Boolean::Is(flag) = flag else {
                unreachable!()
            };
            let words = diff.0.map(|el| el.get_variable());
            witness_sets_for_words.push((*flag, words));
        }

        let result_vars: [Variable; REGISTER_SIZE] = [cs.add_variable(), cs.add_variable()];
        let default_pc_vars = default_next_pc.0.map(|el| el.get_variable());
        let default_case_exec_flags_vars: Vec<_> = default_case_exec_flags
            .iter()
            .map(|&el| {
                let Boolean::Is(el) = el else { unreachable!() };

                el
            })
            .collect();
        // assign witness
        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            use crate::cs::witness_placer::*;

            // first default case

            let mut result = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0);
            let default_pc = placer.get_u32_from_u16_parts(default_pc_vars);
            let mut should_assign = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
            for flag in default_case_exec_flags_vars.iter() {
                should_assign = should_assign.or(&placer.get_boolean(*flag));
            }
            result.assign_masked(&should_assign, &default_pc);

            // then by-word cases
            for (flag, words) in witness_sets_for_words.iter() {
                let flag = placer.get_boolean(*flag);
                let value = placer.get_u32_from_u16_parts(*words);
                result.assign_masked(&flag, &value);
            }

            placer.assign_u32_from_u16_parts(result_vars, &result);
        };
        cs.set_values(value_fn);

        for word_idx in [0, 1] {
            let mut orthogonality_flag = false;

            let mut constraint = Constraint::empty();
            for flag in default_case_exec_flags.iter() {
                let word = default_next_pc.0[word_idx];
                constraint = mask_by_boolean_into_accumulator_constraint(flag, &word, constraint);
            }

            for (flag, diff) in non_default_cases.iter() {
                let word = diff.0[word_idx];
                constraint = mask_by_boolean_into_accumulator_constraint(flag, &word, constraint);
                if flag.get_value(cs).unwrap_or(false) {
                    if orthogonality_flag {
                        panic!("Not orthogonal application");
                    } else {
                        orthogonality_flag = true;
                    }
                }
            }

            let selection_result = result_vars[word_idx]; // No range check required
            constraint -= Term::from(selection_result);

            cs.add_constraint(constraint);
        }

        let result = result_vars.map(|el| Num::Var(el));

        Register(result)
    }
}
