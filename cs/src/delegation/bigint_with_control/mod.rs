use std::collections::BTreeMap;

use super::*;
use crate::cs::circuit::*;
use crate::cs::utils::collapse_max_quadratic_constraint_into;
use crate::cs::witness_placer::WitnessTypeSet;
use crate::cs::witness_placer::*;
use crate::definitions::REGISTER_SIZE;
use crate::one_row_compiler::LookupInput;
use crate::one_row_compiler::Variable;
use crate::types::Boolean;
use crate::types::Num;

const NUM_CONTROL_BITS: usize = 8;

pub const ADD_OP_BIT_IDX: usize = 0;
pub const SUB_OP_BIT_IDX: usize = 1;
pub const SUB_AND_NEGATE_OP_BIT_IDX: usize = 2;
pub const MUL_LOW_OP_BIT_IDX: usize = 3;
pub const MUL_HIGH_OP_BIT_IDX: usize = 4;
pub const EQ_OP_BIT_IDX: usize = 5;
pub const CARRY_BIT_IDX: usize = 6;
pub const MEMCOPY_BIT_IDX: usize = 7;

pub fn all_table_types() -> Vec<TableType> {
    vec![
        TableType::U16SplitAsBytes,
        TableType::RangeCheck9x9,
        TableType::RangeCheck10x10,
        TableType::RangeCheck11,
        TableType::RangeCheck12,
        TableType::RangeCheck13,
    ]
}

pub fn u256_ops_extended_control_delegation_circuit_create_table_driver<F: PrimeField>(
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

pub fn define_u256_ops_extended_control_delegation_circuit<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
) -> (Vec<[Variable; 2]>, [Variable; REGISTER_SIZE]) {
    // add tables
    materialize_tables_into_cs(cs);

    // the only convention we must eventually satisfy is that if we do NOT process delegation request,
    // then all memory writes in ABI must be 0s

    let execute = cs.process_delegation_request();

    let x10_request = RegisterAccessRequest {
        register_index: 10,
        register_write: false,
        indirects_alignment_log2: 5, // 32 bytes
        indirect_accesses: vec![true; 8],
    };

    let x11_request = RegisterAccessRequest {
        register_index: 11,
        register_write: false,
        indirects_alignment_log2: 5, // 32 bytes
        indirect_accesses: vec![false; 8],
    };

    let x12_request = RegisterAccessRequest {
        register_index: 12,
        register_write: true,
        indirects_alignment_log2: 0, // no indirects
        indirect_accesses: vec![],
    };

    let x10_and_indirects = cs.create_register_and_indirect_memory_accesses(x10_request);
    let x11_and_indirects = cs.create_register_and_indirect_memory_accesses(x11_request);
    let x12_and_indirects = cs.create_register_and_indirect_memory_accesses(x12_request);

    assert_eq!(x10_and_indirects.indirect_accesses.len(), 8);
    assert_eq!(x11_and_indirects.indirect_accesses.len(), 8);
    assert!(x12_and_indirects.indirect_accesses.is_empty());

    let mut a_words = vec![];
    let mut output_placeholder_state = vec![];
    for i in 0..8 {
        let IndirectAccessType::Write {
            read_value,
            write_value,
        } = x10_and_indirects.indirect_accesses[i]
        else {
            panic!()
        };

        a_words.push(read_value);
        output_placeholder_state.push(write_value);
    }

    let mut b_words = vec![];
    for i in 0..8 {
        let IndirectAccessType::Read { read_value } = x11_and_indirects.indirect_accesses[i] else {
            panic!()
        };

        b_words.push(read_value);
    }

    let control_mask = {
        let RegisterAccessType::Write { read_value, .. } = x12_and_indirects.register_access else {
            panic!()
        };

        read_value
    };

    assert_eq!(a_words.len(), 8);
    assert_eq!(b_words.len(), 8);

    {
        for (i, input) in a_words.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("`a` U256 element word {} = 0x{:08x}", i, value);
            }
        }

        for (i, input) in b_words.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("`b` U256 element word {} = 0x{:08x}", i, value);
            }
        }

        let register = Register::<F>(control_mask.map(|el| Num::Var(el)));
        if let Some(value) = register.get_value_unsigned(&*cs) {
            println!("Control bitmask = 0b{:b}", value);
        }
    }

    // we can immediately boolean decompose control register into bitmask and ignore high

    let control_bitmask =
        Boolean::split_into_bitmask::<F, CS, NUM_CONTROL_BITS>(cs, Num::Var(control_mask[0]));

    {
        for (i, el) in control_bitmask.iter().enumerate() {
            if let Some(value) = el.get_value(&*cs) {
                println!("Control bitmask element {} = {}", i, value);
            }
        }
    }

    // We will check for a proper bitmask, for all terms EXCEPT carry, as it can be encountered
    // in combination with add/sub

    let mut constraint = Constraint::<F>::empty();
    for (idx, bit) in control_bitmask.iter().enumerate() {
        if idx != CARRY_BIT_IDX {
            constraint = constraint + bit.get_terms();
        }
    }
    let constraint_minus_one = constraint.clone() - Term::from(1u64);
    constraint = constraint * constraint_minus_one;
    cs.add_constraint(constraint);

    let perform_add = control_bitmask[ADD_OP_BIT_IDX];
    let perform_sub = control_bitmask[SUB_OP_BIT_IDX];
    let perform_sub_negate = control_bitmask[SUB_AND_NEGATE_OP_BIT_IDX];
    let perform_mul_low = control_bitmask[MUL_LOW_OP_BIT_IDX];
    let perform_mul_high = control_bitmask[MUL_HIGH_OP_BIT_IDX];
    let perform_eq = control_bitmask[EQ_OP_BIT_IDX];
    let carry_or_borrow = control_bitmask[CARRY_BIT_IDX];
    let perform_memcopy = control_bitmask[MEMCOPY_BIT_IDX];

    {
        if let Some(value) = perform_add.get_value(&*cs) {
            if value {
                println!("Perform ADD");
            }
        }
        if let Some(value) = perform_sub.get_value(&*cs) {
            if value {
                println!("Perform SUB");
            }
        }
        if let Some(value) = perform_sub_negate.get_value(&*cs) {
            if value {
                println!("Perform SUB_NEGATE");
            }
        }
        if let Some(value) = perform_mul_low.get_value(&*cs) {
            if value {
                println!("Perform MUL_LOW");
            }
        }
        if let Some(value) = perform_mul_high.get_value(&*cs) {
            if value {
                println!("Perform MUL_HIGH");
            }
        }
        if let Some(value) = perform_eq.get_value(&*cs) {
            if value {
                println!("Perform EQ");
            }
        }
        if let Some(value) = perform_memcopy.get_value(&*cs) {
            if value {
                println!("Perform MEMCOPY");
            }
        }
    }

    let perform_eq_boolean = perform_eq;

    let perform_add = perform_add.get_variable().unwrap();
    let perform_sub = perform_sub.get_variable().unwrap();
    let perform_sub_negate = perform_sub_negate.get_variable().unwrap();
    let perform_mul_low = perform_mul_low.get_variable().unwrap();
    let perform_mul_high = perform_mul_high.get_variable().unwrap();
    let perform_eq = perform_eq.get_variable().unwrap();
    let carry_or_borrow = carry_or_borrow.get_variable().unwrap();
    let perform_memcopy = perform_memcopy.get_variable().unwrap();

    // We have two choices for the strategy:
    // - separately implement addition/subtraction and multiplication. It's easy and dealing with carry bit is simple
    // - try to perform some convoluted FMA

    // For now we stick with the first option

    // first operations that only require addition/subtraction. For that we need for the relation of the form
    // `A` + `B` = `C` + 2^256 * overflow to designate a/b/c
    // if we add: `A` = a, `B` = b + carry, `C` = result
    // if we sub: 2^256 * of + a - b = result, so result + b = a + 2^256 * of, `C` = a, `B` = b + carry, `A` = result
    // if we sub-negate (opposite order): 2^256 * of + b - a = result, so result + a = b + 2^256 * of, `C` = b + carry, `B` = result, `A` = a
    // if we perform equality check - we do just a subtraction and look at the carry and perform zero-comparisons
    // if we execute memcopy, then `A` = 0, `B` = b + carry, `C` = result

    // We will also reuse zero-comparisons for overflowing multiplication check later on

    let a_limbs: [Variable; 16] = a_words
        .iter()
        .flatten()
        .copied()
        .collect::<Vec<Variable>>()
        .try_into()
        .unwrap();
    let b_limbs: [Variable; 16] = b_words
        .iter()
        .flatten()
        .copied()
        .collect::<Vec<Variable>>()
        .try_into()
        .unwrap();

    // NOTE: no range checks here, we will merge it with multiplication low
    let additive_ops_result: [Variable; 16] = std::array::from_fn(|_| cs.add_variable());

    let intermediate_carry_booleans: [Boolean; 16] =
        std::array::from_fn(|_| cs.add_boolean_variable());
    let intermediate_carry_variables =
        intermediate_carry_booleans.map(|el| el.get_variable().unwrap());

    let result_of_boolean = intermediate_carry_booleans[15];
    let result_of_variable = result_of_boolean.get_variable().unwrap();
    // perform witness generation. We will at once generate value for the final result and intermediate variables
    // for constraints below

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let a_limbs = a_limbs.map(|el| placer.get_u16(el));
        let b_limbs = b_limbs.map(|el| placer.get_u16(el));

        let perform_add = placer.get_boolean(perform_add);
        let perform_sub = placer.get_boolean(perform_sub);
        let perform_sub_negate = placer.get_boolean(perform_sub_negate);
        let perform_eq = placer.get_boolean(perform_eq);
        let perform_memcopy = placer.get_boolean(perform_memcopy);

        let carry_or_borrow = placer.get_boolean(carry_or_borrow);

        let zero = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0);
        let constant_false = <CS::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);

        let mut base_el: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16; 16] =
            std::array::from_fn(|_| zero.clone());
        let mut to_add: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16; 16] =
            std::array::from_fn(|_| zero.clone());
        let mut to_sub: [<<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16; 16] =
            std::array::from_fn(|_| zero.clone());

        let mut carry_or_borrow_selected = constant_false.clone();
        {
            let use_carry_or_borrow = perform_add
                .or(&perform_sub)
                .or(&perform_sub_negate)
                .or(&perform_memcopy);
            carry_or_borrow_selected.assign_masked(&use_carry_or_borrow, &carry_or_borrow);
        }

        for i in 0..16 {
            let assign_a = perform_add.or(&perform_sub).or(&perform_eq);
            base_el[i].assign_masked(&assign_a, &a_limbs[i]);
            base_el[i].assign_masked(&perform_sub_negate, &b_limbs[i]);
            // and if we do memcopy, then it's 0
        }

        for i in 0..16 {
            let assign_b = perform_add.or(&perform_memcopy);
            to_add[i].assign_masked(&assign_b, &b_limbs[i]);
        }

        for i in 0..16 {
            to_sub[i].assign_masked(&perform_sub_negate, &a_limbs[i]);

            let assign_b = perform_sub.or(&perform_eq);
            to_sub[i].assign_masked(&assign_b, &b_limbs[i]);
        }

        let mut carry_to_propagate = carry_or_borrow_selected.clone();

        // well, just unrolled long addition and subtraction
        let addition_result_limbs: [_; 16] = std::array::from_fn(|i| {
            let (t, of) = base_el[i].overflowing_add_with_carry(&to_add[i], &carry_to_propagate);
            carry_to_propagate = of.clone();

            (t, of)
        });

        let mut borrow_to_propagate = carry_or_borrow_selected.clone();
        let subtraction_result_limbs: [_; 16] = std::array::from_fn(|i| {
            let (t, of) = base_el[i].overflowing_sub_with_borrow(&to_sub[i], &borrow_to_propagate);
            borrow_to_propagate = of.clone();

            (t, of)
        });

        let assign_addition_result = perform_add.or(&perform_memcopy);
        let assign_subtraction_result = perform_sub.or(&perform_sub_negate).or(&perform_eq);

        // NOTE: we can not use fully conditional form here, instead we take baseline 0 and select on top

        for i in 0..16 {
            // Trivial values are 0
            let mut value =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0);
            let mut intermediate_carry_value =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask::constant(false);
            // add
            value = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                &assign_addition_result,
                &addition_result_limbs[i].0,
                &value,
            );
            intermediate_carry_value =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                    &assign_addition_result,
                    &addition_result_limbs[i].1,
                    &intermediate_carry_value,
                );
            // sub
            value = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                &assign_subtraction_result,
                &subtraction_result_limbs[i].0,
                &value,
            );
            intermediate_carry_value =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                    &assign_subtraction_result,
                    &subtraction_result_limbs[i].1,
                    &intermediate_carry_value,
                );
            // rest
            value = <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                &assign_subtraction_result,
                &subtraction_result_limbs[i].0,
                &value,
            );
            intermediate_carry_value =
                <<CS as Circuit<F>>::WitnessPlacer as WitnessTypeSet<F>>::Mask::select(
                    &assign_subtraction_result,
                    &subtraction_result_limbs[i].1,
                    &intermediate_carry_value,
                );

            placer.assign_u16(additive_ops_result[i], &value);
            placer.assign_mask(intermediate_carry_variables[i], &intermediate_carry_value);
        }
    };

    cs.set_values(value_fn);

    {
        for (i, input) in additive_ops_result.array_chunks::<2>().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("Prepared result U256 element word {} = 0x{:08x}", i, value);
            }
        }

        if let Some(value) = result_of_boolean.get_value(&*cs) {
            println!("Of = {}", value);
        }
    }

    // We do not need to make any explicit selections and instead can keep A/B/C as quadratic constraints
    // to enforce linear addition constraint

    // constraint values shuffle

    let mut previous_of = None;
    // now enforce long addition - we should allocate intermediate carries and then use pre-existing one for the result
    for limb_idx in 0..16 {
        let of_for_limb = intermediate_carry_variables[limb_idx];
        // now select and add from constraint

        let mut constraint = Constraint::<F>::empty();
        // selection of virtual A limb
        constraint = constraint + Term::from(perform_add) * Term::from(a_limbs[limb_idx]);
        constraint =
            constraint + Term::from(perform_sub) * Term::from(additive_ops_result[limb_idx]);
        constraint = constraint + Term::from(perform_sub_negate) * Term::from(a_limbs[limb_idx]);
        constraint =
            constraint + Term::from(perform_eq) * Term::from(additive_ops_result[limb_idx]);
        // and nothing for memcopy

        // selection of virtual B limb
        constraint = constraint + Term::from(perform_add) * Term::from(b_limbs[limb_idx]);
        constraint = constraint + Term::from(perform_sub) * Term::from(b_limbs[limb_idx]);
        constraint =
            constraint + Term::from(perform_sub_negate) * Term::from(additive_ops_result[limb_idx]);
        constraint = constraint + Term::from(perform_eq) * Term::from(b_limbs[limb_idx]);
        // memcopy is present here
        constraint = constraint + Term::from(perform_memcopy) * Term::from(b_limbs[limb_idx]);

        // selection of virtual C limb
        constraint =
            constraint - Term::from(perform_add) * Term::from(additive_ops_result[limb_idx]);
        constraint = constraint - Term::from(perform_sub) * Term::from(a_limbs[limb_idx]);
        constraint = constraint - Term::from(perform_sub_negate) * Term::from(b_limbs[limb_idx]);
        constraint = constraint - Term::from(perform_eq) * Term::from(a_limbs[limb_idx]);
        // memcopy is present here
        constraint =
            constraint - Term::from(perform_memcopy) * Term::from(additive_ops_result[limb_idx]);

        // and propagate carries
        constraint -= Term::from((F::from_u64_unchecked(1 << 16), of_for_limb));
        if limb_idx == 0 {
            // we only "use" carry or borrow in case of add/sub/sub_neg, but it is still degree 2

            // we always add it along with "b" term
            constraint = constraint + Term::from(perform_add) * Term::from(carry_or_borrow);
            constraint = constraint + Term::from(perform_sub) * Term::from(carry_or_borrow);
            constraint = constraint - Term::from(perform_sub_negate) * Term::from(carry_or_borrow);
            // memcopy is present here
            constraint = constraint + Term::from(perform_memcopy) * Term::from(carry_or_borrow);
        } else {
            let previous_carry = previous_of.take().unwrap();
            constraint += Term::from(previous_carry);
        }

        cs.add_constraint(constraint);

        previous_of = Some(of_for_limb);
    }

    // addition is done, and we need to keep the zero-check in mind to finish equality operation later on

    // for multiplication we will want to allocate 8-bit chunks anyway. Unfortunately there is no simple consistent way to work
    // with e.g 24-bit intermediate product results. So we make a decomposition and continue from there

    let mut a_bytes = Vec::with_capacity(32);
    for el in a_limbs.iter() {
        let [l, h] = cs.get_variables_from_lookup_constrained::<1, 2>(
            &[LookupInput::from(*el)],
            TableType::U16SplitAsBytes,
        );
        a_bytes.extend([l, h]);
    }

    let mut b_bytes = Vec::with_capacity(32);
    for el in b_limbs.iter() {
        let [l, h] = cs.get_variables_from_lookup_constrained::<1, 2>(
            &[LookupInput::from(*el)],
            TableType::U16SplitAsBytes,
        );
        b_bytes.extend([l, h]);
    }

    // {
    //     for (i, el) in a_bytes.iter().enumerate() {
    //         if let Some(value) = cs.get_value(*el) {
    //             println!("`a` element byte {} = 0x{:02x}", i, value.as_u64_reduced() as u8);
    //         }
    //     }

    //     for (i, el) in b_bytes.iter().enumerate() {
    //         if let Some(value) = cs.get_value(*el) {
    //             println!("`b` element byte {} = 0x{:02x}", i, value.as_u64_reduced() as u8);
    //         }
    //     }
    // }

    let add_sub_operation_result = additive_ops_result;
    let eq_operation_result = a_limbs;
    let eq_operation_words_for_zero_check = additive_ops_result;

    // We will put all byte-products into 16-bit destination word, and dynamically keep track of the range and issue the corresponding range checks for intermediate overflows

    // Note that we need to make explicit 16-bit result words, so we will make intermediate product as variable,
    // then split an explicit lowest 16 bits, range check upper bits linear term, and carry such linear term further

    // We will encounter intermediate products from 25 to 29 bits,
    // so we will need rangecheck tables from 9 to 13 bits

    let mut range_checks_buffer: BTreeMap<u32, Vec<Constraint<F>>> = BTreeMap::new();

    // we will make full product below, but we will merge range checks for result of add/sub/etc and of product_low

    let product_low: [Variable; 16] = std::array::from_fn(|_| cs.add_variable()); // no range check, we will merge it below
    let product_high: [Variable; 16] =
        std::array::from_fn(|_| cs.add_variable_with_range_check(16).get_variable());

    let full_product: [Variable; 32] = product_low
        .into_iter()
        .chain(product_high.into_iter())
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

    let mut carry_constraint = Constraint::<F>::empty();
    let mut carry_range = 0u64;
    for (i, product_word) in full_product.iter().enumerate() {
        let mut product_constraint = carry_constraint.clone();
        let mut product_range = carry_range;
        for a_byte_idx in 0..32 {
            for b_byte_idx in 0..32 {
                if a_byte_idx + b_byte_idx == 2 * i {
                    product_constraint = product_constraint
                        + Term::from(a_bytes[a_byte_idx]) * Term::from(b_bytes[b_byte_idx]);
                    product_range += 255u64 * 255u64;
                } else if a_byte_idx + b_byte_idx == 2 * i + 1 {
                    product_constraint = product_constraint
                        + Term::from((F::from_u64_unchecked(1 << 8), a_bytes[a_byte_idx]))
                            * Term::from(b_bytes[b_byte_idx]);
                    product_range += (255u64 * 255u64) << 8;
                }
            }
        }
        assert!(product_range < F::CHARACTERISTICS);
        assert!(product_range.next_power_of_two() <= F::CHARACTERISTICS);

        if i == full_product.len() - 1 {
            assert!(product_range < 1 << 16);
            // no further overflow is possible, and we should collapse directly
            collapse_max_quadratic_constraint_into(cs, product_constraint.clone(), *product_word);
            product_constraint -= Term::from(*product_word);
            cs.add_constraint(product_constraint);
        } else {
            let product_intermediate = cs.add_variable_from_constraint(product_constraint);
            // now split it - we only need to assign a witness to already range-checked product word,
            // and perform extra range check for carry constraint

            let product_word = *product_word;

            let value_fn = move |placer: &mut CS::WitnessPlacer| {
                let full_value_low = placer
                    .get_field(product_intermediate)
                    .as_integer()
                    .truncate();
                placer.assign_u16(product_word, &full_value_low);
            };
            cs.set_values(value_fn);

            carry_range = product_range >> 16;
            carry_constraint = Constraint::empty();
            carry_constraint += Term::from(product_intermediate);
            carry_constraint -= Term::from(product_word);
            carry_constraint.scale(F::from_u64_unchecked(1 << 16).inverse().unwrap());

            // {
            //     if let Some(value) = cs.get_value(product_intermediate) {
            //         println!("Intermediate product {} value = 0x{:016x}", i, value.as_u64_reduced());
            //     }

            //     if let Some(value) = cs.get_value(*product_word) {
            //         println!("Result product word {} value = 0x{:016x}", i, value.as_u64_reduced());
            //     }
            // }

            let carry_bits = carry_range.next_power_of_two().trailing_zeros();
            range_checks_buffer
                .entry(carry_bits)
                .or_default()
                .push(carry_constraint.clone());
        }
    }

    {
        for (i, input) in product_low.array_chunks::<2>().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("Product low U256 element word {} = 0x{:08x}", i, value);
            }
        }

        for (i, input) in product_high.array_chunks::<2>().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("Product high U256 element word {} = 0x{:08x}", i, value);
            }
        }
    }

    // merge range checks between additive results and multiplicative result low
    {
        for (a, b) in additive_ops_result.into_iter().zip(product_low.into_iter()) {
            let mut constraint = Constraint::empty();
            constraint = constraint + Term::from(perform_add) * Term::from(a);
            constraint = constraint + Term::from(perform_sub) * Term::from(a);
            constraint = constraint + Term::from(perform_sub_negate) * Term::from(a);
            constraint = constraint + Term::from(perform_eq) * Term::from(a);

            constraint = constraint + Term::from(perform_mul_low) * Term::from(b);
            constraint = constraint + Term::from(perform_mul_high) * Term::from(b);

            let t = cs.add_variable_with_range_check(16).get_variable();
            collapse_max_quadratic_constraint_into(cs, constraint.clone(), t);
            constraint -= Term::from(t);
            cs.add_constraint(constraint);
        }
    }

    // for width 9 and 10 we can use two checks at once,
    // for higher widths - only one check at once

    for (width, checks) in range_checks_buffer.into_iter() {
        assert!(width >= 9, "width {} is unexpected", width);
        assert!(width <= 13, "width {} is unexpected", width);

        if width <= 10 {
            let table_type = match width {
                9 => TableType::RangeCheck9x9,
                10 => TableType::RangeCheck10x10,
                _ => unreachable!(),
            };
            let mut it = checks.array_chunks::<2>();
            for [a, b] in &mut it {
                let a = LookupInput::from(a.clone());
                let b = LookupInput::from(b.clone());
                cs.enforce_lookup_tuple_for_fixed_table(
                    &[a, b, LookupInput::empty()],
                    table_type,
                    false,
                );
            }
            let remainder = it.remainder();
            if remainder.len() > 0 {
                let a = &remainder[0];
                let a = LookupInput::from(a.clone());
                cs.enforce_lookup_tuple_for_fixed_table(
                    &[a, LookupInput::empty(), LookupInput::empty()],
                    table_type,
                    false,
                );
            }
        } else {
            let table_type = match width {
                11 => TableType::RangeCheck11,
                12 => TableType::RangeCheck12,
                13 => TableType::RangeCheck13,
                _ => unreachable!(),
            };
            for a in checks.iter() {
                let a = LookupInput::from(a.clone());
                cs.enforce_lookup_tuple_for_fixed_table(
                    &[a, LookupInput::empty(), LookupInput::empty()],
                    table_type,
                    false,
                );
            }
        }
    }

    // now multiplication is fully constrained, so we can select the outputs, and write them directly into memory

    let all_flags = [
        perform_add,
        perform_sub,
        perform_sub_negate,
        perform_eq,
        perform_mul_low,
        perform_mul_high,
        perform_memcopy,
    ];
    let all_results = [
        add_sub_operation_result,
        add_sub_operation_result,
        add_sub_operation_result,
        eq_operation_result,
        product_low,
        product_high,
        add_sub_operation_result,
    ];

    let output_vars = output_placeholder_state.iter().flatten();

    for (idx, output_var) in output_vars.enumerate() {
        let mut constraint = Constraint::<F>::empty();
        for (flag, result) in all_flags.iter().zip(all_results.iter()) {
            let limb = result[idx];
            constraint = constraint + (Term::from(*flag) * Term::from(limb));
        }
        collapse_max_quadratic_constraint_into(cs, constraint.clone(), *output_var);
        constraint -= Term::from(*output_var);
        cs.add_constraint(constraint);
    }

    // and now we can resolve updated flag

    // Select values over which we will perform zero-check
    // - for equality operation it's taken from additive ops
    // - for mul-low operation those are high words
    let zero_check_inputs: [Variable; 16] = std::array::from_fn(|_| cs.add_variable());
    for (idx, (comparison_output, product_high)) in eq_operation_words_for_zero_check
        .into_iter()
        .zip(product_high.into_iter())
        .enumerate()
    {
        let output_var = zero_check_inputs[idx];
        let mut constraint = Constraint::<F>::empty();
        constraint = constraint + (Term::from(perform_eq) * Term::from(comparison_output));
        constraint = constraint + (Term::from(perform_mul_low) * Term::from(product_high));
        collapse_max_quadratic_constraint_into(cs, constraint.clone(), output_var);
        constraint -= Term::from(output_var);
        cs.add_constraint(constraint);
    }
    let zero_flags = zero_check_inputs.map(|el| cs.is_zero(Num::Var(el)));
    let all_zeroes = Boolean::multi_and(&zero_flags, cs);
    let values_are_equal_for_perform_eq =
        Boolean::and(&all_zeroes, &result_of_boolean.toggle(), cs);
    let perform_eq_bit = Boolean::and(&perform_eq_boolean, &values_are_equal_for_perform_eq, cs);
    // NOTE: we need to mask equality check as it'll be 1 in the padding
    let perform_eq_result = Boolean::and(&perform_eq_bit, &execute, cs);

    // now we need to resolve a condition
    // - for all add/sub ops our return register is just an overflow
    // - for equality - it's zero check && overflow is zero
    // - for mul-low - it's zero check negated

    let RegisterAccessType::Write {
        write_value: x12_write_vars,
        ..
    } = x12_and_indirects.register_access
    else {
        panic!()
    };

    let mut constraint = Constraint::<F>::empty();
    constraint = constraint + (Term::from(perform_add) * Term::from(result_of_variable));
    constraint = constraint + (Term::from(perform_sub) * Term::from(result_of_variable));
    constraint = constraint + (Term::from(perform_sub_negate) * Term::from(result_of_variable));
    constraint = constraint
        + (Term::from(perform_eq) * Term::from(perform_eq_result.get_variable().unwrap()));
    constraint = constraint
        + (Term::from(perform_mul_low)
            * (Term::from(1u64) - Term::from(all_zeroes.get_variable().unwrap())));
    // memcopy is same as addition
    constraint = constraint + (Term::from(perform_memcopy) * Term::from(result_of_variable));
    collapse_max_quadratic_constraint_into(cs, constraint.clone(), x12_write_vars[0]);
    constraint -= Term::from(x12_write_vars[0]);
    cs.add_constraint(constraint);

    // set value for high bits and constraint it
    let x12_write_vars_high = x12_write_vars[1];
    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        use crate::cs::witness_placer::WitnessComputationalInteger;

        let zero = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0);
        placer.assign_u16(x12_write_vars_high, &zero);
    };
    cs.set_values(value_fn);

    let constraint = Constraint::<F>::empty() + Term::from(x12_write_vars[1]);
    cs.add_constraint_allow_explicit_linear_prevent_optimizations(constraint);

    {
        for (i, input) in output_placeholder_state.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("Output element {} = 0x{:08x}", i, value);
            }
        }

        let x12_output = Register::<F>(x12_write_vars.map(|el| Num::Var(el)));
        if let Some(value) = x12_output.get_value_unsigned(&*cs) {
            println!("x12 output = 0x{:08x}", value);
        }
    }

    (output_placeholder_state, x12_write_vars)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::cs::cs_reference::BasicAssembly;
    use crate::one_row_compiler::OneRowCompiler;
    use crate::utils::serialize_to_file;
    use field::Mersenne31Field;

    #[test]
    fn compile_u256_ops_extended_control() {
        let mut cs: BasicAssembly<Mersenne31Field> = BasicAssembly::<Mersenne31Field>::new();
        define_u256_ops_extended_control_delegation_circuit(&mut cs);
        let (circuit_output, _) = cs.finalize();
        let compiler = OneRowCompiler::default();
        let compiled = compiler.compile_to_evaluate_delegations(circuit_output, 20);

        serialize_to_file(&compiled, "bigint_delegation_layout.json");
    }

    #[test]
    fn bigint_delegation_get_witness_graph() {
        let ssa_forms = dump_ssa_witness_eval_form_for_delegation::<Mersenne31Field, _>(
            define_u256_ops_extended_control_delegation_circuit,
        );
        serialize_to_file(&ssa_forms, "bigint_delegation_ssa.json");
    }
}
