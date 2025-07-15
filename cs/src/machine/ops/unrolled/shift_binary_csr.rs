use crate::cs::witness_placer::*;

use super::*;

// NOTE: this circuit should specify non-dummy CSR table in proving/setup. while compilation in tests
// takes case of properly computing offsets by using dummy talbe

pub fn shift_binop_csrrw_tables() -> Vec<TableType> {
    vec![
        TableType::ZeroEntry, // we need it, as we use conditional lookup enforcements
        TableType::TruncateShiftAmount,
        TableType::SllWith16BitInputLow,
        TableType::SllWith16BitInputHigh,
        TableType::SrlWith16BitInputLow,
        TableType::SrlWith16BitInputHigh,
        TableType::Sra16BitInputSignFill,
        TableType::Xor,
        TableType::And,
        TableType::Or,
        TableType::RangeCheck16WithZeroPads,
    ]
}

pub fn shift_binop_csrrw_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    for el in shift_binop_csrrw_tables() {
        cs.materialize_table(el);
    }
}

pub fn shift_binop_csrrw_table_driver_fn<F: PrimeField>(table_driver: &mut TableDriver<F>) {
    for el in shift_binop_csrrw_tables() {
        table_driver.materialize_table(el);
    }
}

fn apply_shift_binop_csrrw<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    inputs: OpcodeFamilyCircuitState<F>,
) {
    // we will not use optimization context and utilize scratch space ourselves
    let decoder = <ShiftBinaryCsrrwDecoder as OpcodeFamilyDecoder>::BitmaskCircuitParser::parse(
        cs,
        inputs.decoder_data.circuit_family_extra_mask,
    );

    // read inputs
    let (rs1_reg, rs1_mem_query) =
        get_rs1_as_shuffle_ram(cs, Num::Var(inputs.decoder_data.rs1_index), true);
    cs.add_shuffle_ram_query(rs1_mem_query);
    let (rs2_reg, rs2_mem_query) =
        get_rs2_as_shuffle_ram(cs, Num::Var(inputs.decoder_data.rs2_index), true);
    cs.add_shuffle_ram_query(rs2_mem_query);
    let imm_as_reg = Register::<F>(inputs.decoder_data.imm.map(|el| Num::Var(el)));

    let use_imm = decoder.use_imm();
    let rs2_value = Register::choose(cs, &use_imm, &imm_as_reg, &rs2_reg);

    let [rs1_low, rs1_high] = rs1_reg.0.map(|el| el.get_variable());
    let [rs2_low, rs2_high] = rs2_value.0.map(|el| el.get_variable());

    // we can reuse some variables as scratch space

    // for binary ops - we need to decompose inputs into bytes, so we will need 4 more variables,
    // and then we need 4 more variables for outputs of lookup

    // for shifts - we need to crop shift amount to 5 bits (for simplicity we will treat it as 2 output vars), also get top bit of input word (same - we will use 2 output var),
    // and then 4 more variables as outputs of lookups

    // for csrrw - we are also fine with 8

    let [s0, s1, s2, s3, s4, s5, s6, s7] = std::array::from_fn(|_| cs.add_variable());

    // shifts are simple - truncate shift amount, then lookup
    let (lookup_tuples_sll, sll_outs): (Vec<([LookupInput<F>; 3], Num<F>)>, _) = {
        let is_sll = decoder.perform_sll();
        let shift_amount = s0;
        let _unused = s1;
        cs.peek_lookup_value_unconstrained_ext::<1, 2>(
            &[LookupInput::Variable(rs2_low)],
            &[shift_amount, _unused],
            TableType::TruncateShiftAmount.to_num(),
            is_sll,
        );

        let t0 = (
            [
                LookupInput::Variable(rs2_low),
                LookupInput::Variable(shift_amount),
                LookupInput::Variable(_unused),
            ],
            TableType::TruncateShiftAmount.to_num(),
        );

        let low_from_low = s2;
        let high_from_low = s3;
        let low_from_high = s4;
        let high_from_high = s5;

        let input_expr_low = (Term::from(1 << 16) * Term::from(shift_amount)) + Term::from(rs1_low);
        let input_expr_high =
            (Term::from(1 << 16) * Term::from(shift_amount)) + Term::from(rs1_high);

        cs.peek_lookup_value_unconstrained_ext::<1, 2>(
            &[LookupInput::from(input_expr_low.clone())],
            &[low_from_low, high_from_low],
            TableType::SllWith16BitInputLow.to_num(),
            is_sll,
        );

        let t1 = (
            [
                LookupInput::from(input_expr_low),
                LookupInput::Variable(low_from_low),
                LookupInput::Variable(high_from_low),
            ],
            TableType::SllWith16BitInputLow.to_num(),
        );

        cs.peek_lookup_value_unconstrained_ext::<1, 2>(
            &[LookupInput::from(input_expr_high.clone())],
            &[low_from_high, high_from_high],
            TableType::SllWith16BitInputHigh.to_num(),
            is_sll,
        );

        let t2 = (
            [
                LookupInput::from(input_expr_high),
                LookupInput::Variable(low_from_high),
                LookupInput::Variable(high_from_high),
            ],
            TableType::SllWith16BitInputHigh.to_num(),
        );

        (
            vec![t0, t1, t2],
            [
                [low_from_low, low_from_high],
                [high_from_low, high_from_high],
            ],
        )
    };

    // SRL is the same
    let (lookup_tuples_srl, srl_outs): (Vec<([LookupInput<F>; 3], Num<F>)>, _) = {
        let is_srl = decoder.perform_srl();
        let shift_amount = s0;
        let _unused = s1;
        cs.peek_lookup_value_unconstrained_ext::<1, 2>(
            &[LookupInput::Variable(rs2_low)],
            &[shift_amount, _unused],
            TableType::TruncateShiftAmount.to_num(),
            is_srl,
        );

        let t0 = (
            [
                LookupInput::Variable(rs2_low),
                LookupInput::Variable(shift_amount),
                LookupInput::Variable(_unused),
            ],
            TableType::TruncateShiftAmount.to_num(),
        );

        let low_from_low = s2;
        let high_from_low = s3;
        let low_from_high = s4;
        let high_from_high = s5;

        let input_expr_low = (Term::from(1 << 16) * Term::from(shift_amount)) + Term::from(rs1_low);
        let input_expr_high =
            (Term::from(1 << 16) * Term::from(shift_amount)) + Term::from(rs1_high);

        cs.peek_lookup_value_unconstrained_ext::<1, 2>(
            &[LookupInput::from(input_expr_low.clone())],
            &[low_from_low, high_from_low],
            TableType::SrlWith16BitInputLow.to_num(),
            is_srl,
        );

        let t1 = (
            [
                LookupInput::from(input_expr_low),
                LookupInput::Variable(low_from_low),
                LookupInput::Variable(high_from_low),
            ],
            TableType::SrlWith16BitInputLow.to_num(),
        );

        cs.peek_lookup_value_unconstrained_ext::<1, 2>(
            &[LookupInput::from(input_expr_high.clone())],
            &[low_from_high, high_from_high],
            TableType::SrlWith16BitInputHigh.to_num(),
            is_srl,
        );

        let t2 = (
            [
                LookupInput::from(input_expr_high),
                LookupInput::Variable(low_from_high),
                LookupInput::Variable(high_from_high),
            ],
            TableType::SrlWith16BitInputHigh.to_num(),
        );

        (
            vec![t0, t1, t2],
            [
                [low_from_low, low_from_high],
                [high_from_low, high_from_high],
            ],
        )
    };

    // SRA is different as we always need to know top bit
    let (lookup_tuples_sra, sra_outs): (Vec<([LookupInput<F>; 3], Num<F>)>, _) = {
        let is_sra = decoder.perform_sra();
        let shift_amount = s0;
        let _unused = s1;
        cs.peek_lookup_value_unconstrained_ext::<1, 2>(
            &[LookupInput::Variable(rs2_low)],
            &[shift_amount, _unused],
            TableType::TruncateShiftAmount.to_num(),
            is_sra,
        );

        let t0 = (
            [
                LookupInput::Variable(rs2_low),
                LookupInput::Variable(shift_amount),
                LookupInput::Variable(_unused),
            ],
            TableType::TruncateShiftAmount.to_num(),
        );

        // model it as SRL and filling top bits

        let input_expr_low = (Term::from(1 << 16) * Term::from(shift_amount)) + Term::from(rs1_low);
        let input_expr_high =
            (Term::from(1 << 16) * Term::from(shift_amount)) + Term::from(rs1_high);

        let low_word_fill = s2;
        let high_word_fill = s3;
        cs.peek_lookup_value_unconstrained_ext::<1, 2>(
            &[LookupInput::from(input_expr_high.clone())],
            &[low_word_fill, high_word_fill],
            TableType::Sra16BitInputSignFill.to_num(),
            is_sra,
        );

        let t1 = (
            [
                LookupInput::from(input_expr_high.clone()),
                LookupInput::Variable(low_word_fill),
                LookupInput::Variable(high_word_fill),
            ],
            TableType::U16GetSignAndHighByte.to_num(),
        );

        let low_from_low = s4;
        let high_from_low = s5;
        let low_from_high = s6;
        let high_from_high = s7;

        cs.peek_lookup_value_unconstrained_ext::<1, 2>(
            &[LookupInput::from(input_expr_low.clone())],
            &[low_from_low, high_from_low],
            TableType::SrlWith16BitInputLow.to_num(),
            is_sra,
        );

        let t2 = (
            [
                LookupInput::from(input_expr_low),
                LookupInput::Variable(low_from_low),
                LookupInput::Variable(high_from_low),
            ],
            TableType::SrlWith16BitInputLow.to_num(),
        );

        cs.peek_lookup_value_unconstrained_ext::<1, 2>(
            &[LookupInput::from(input_expr_high.clone())],
            &[low_from_high, high_from_high],
            TableType::SrlWith16BitInputHigh.to_num(),
            is_sra,
        );

        let t3 = (
            [
                LookupInput::from(input_expr_high),
                LookupInput::Variable(low_from_high),
                LookupInput::Variable(high_from_high),
            ],
            TableType::SrlWith16BitInputHigh.to_num(),
        );

        (
            vec![t0, t1, t2, t3],
            [
                [low_from_low, low_from_high, low_word_fill],
                [high_from_low, high_from_high, high_word_fill],
            ],
        )
    };

    // binary ops are more complex
    let (lookup_tuples_binops, binops_outs): (Vec<([LookupInput<F>; 3], Num<F>)>, _) = {
        let is_binary = decoder.perform_binary_op();

        let rs1_byte_0 = s0;
        let rs1_byte_2 = s1;
        let rs2_byte_0 = s2;
        let rs2_byte_2 = s3;

        let exec_flag = is_binary.get_variable().unwrap();
        let inner_evaluator = move |placer: &mut CS::WitnessPlacer| {
            let rs1_low = placer.get_u16(rs1_low);
            let rs1_high = placer.get_u16(rs1_high);

            let rs2_low = placer.get_u16(rs2_low);
            let rs2_high = placer.get_u16(rs2_high);

            let condition = placer.get_boolean(exec_flag);

            let rs1_byte_0_val: <CS::WitnessPlacer as WitnessTypeSet<F>>::U8 = rs1_low.truncate();
            placer.conditionally_assign_u8(rs1_byte_0, &condition, &rs1_byte_0_val);

            let rs1_byte_2_val: <CS::WitnessPlacer as WitnessTypeSet<F>>::U8 = rs1_high.truncate();
            placer.conditionally_assign_u8(rs1_byte_2, &condition, &rs1_byte_2_val);

            let rs2_byte_0_val: <CS::WitnessPlacer as WitnessTypeSet<F>>::U8 = rs2_low.truncate();
            placer.conditionally_assign_u8(rs2_byte_0, &condition, &rs2_byte_0_val);

            let rs2_byte_2_val: <CS::WitnessPlacer as WitnessTypeSet<F>>::U8 = rs2_high.truncate();
            placer.conditionally_assign_u8(rs2_byte_2, &condition, &rs2_byte_2_val);
        };

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            use crate::cs::witness_placer::*;
            let mask = placer.get_boolean(exec_flag);
            witness_early_branch_if_possible(mask.clone(), placer, &inner_evaluator);
        };
        cs.set_values(value_fn);

        // and now perform lookup
        let out_byte_0 = s4;
        let out_byte_1 = s5;
        let out_byte_2 = s6;
        let out_byte_3 = s7;

        cs.peek_lookup_value_unconstrained_ext(
            &[
                LookupInput::Variable(rs1_byte_0),
                LookupInput::Variable(rs2_byte_0),
            ],
            &[out_byte_0],
            Num::Var(inputs.decoder_data.funct3),
            is_binary,
        );

        let t0 = (
            [
                LookupInput::Variable(rs1_byte_0),
                LookupInput::Variable(rs2_byte_0),
                LookupInput::Variable(out_byte_0),
            ],
            Num::Var(inputs.decoder_data.funct3),
        );

        // (word - u8) / 2^8 == u8 -> word == u8 + 2^8 u8
        let mut rs1_byte_1 = Term::from(rs1_low) - Term::from(rs1_byte_0);
        rs1_byte_1.scale(F::from_u64_unchecked(1 << 8).inverse().unwrap());

        // (word - u8) / 2^8 == u8 -> word == u8 + 2^8 u8
        let mut rs2_byte_1 = Term::from(rs2_low) - Term::from(rs2_byte_0);
        rs2_byte_1.scale(F::from_u64_unchecked(1 << 8).inverse().unwrap());

        cs.peek_lookup_value_unconstrained_ext(
            &[
                LookupInput::from(rs1_byte_1.clone()),
                LookupInput::from(rs2_byte_1.clone()),
            ],
            &[out_byte_1],
            Num::Var(inputs.decoder_data.funct3),
            is_binary,
        );

        let t1 = (
            [
                LookupInput::from(rs1_byte_1),
                LookupInput::from(rs2_byte_1),
                LookupInput::Variable(out_byte_1),
            ],
            Num::Var(inputs.decoder_data.funct3),
        );

        cs.peek_lookup_value_unconstrained_ext(
            &[
                LookupInput::Variable(rs1_byte_2),
                LookupInput::Variable(rs2_byte_2),
            ],
            &[out_byte_2],
            Num::Var(inputs.decoder_data.funct3),
            is_binary,
        );

        let t2 = (
            [
                LookupInput::Variable(rs1_byte_2),
                LookupInput::Variable(rs2_byte_2),
                LookupInput::Variable(out_byte_2),
            ],
            Num::Var(inputs.decoder_data.funct3),
        );

        // (word - u8) / 2^8 == u8 -> word == u8 + 2^8 u8
        let mut rs1_byte_3 = Term::from(rs1_high) - Term::from(rs1_byte_2);
        rs1_byte_3.scale(F::from_u64_unchecked(1 << 8).inverse().unwrap());

        // (word - u8) / 2^8 == u8 -> word == u8 + 2^8 u8
        let mut rs2_byte_3 = Term::from(rs2_high) - Term::from(rs2_byte_2);
        rs2_byte_3.scale(F::from_u64_unchecked(1 << 8).inverse().unwrap());

        cs.peek_lookup_value_unconstrained_ext(
            &[
                LookupInput::from(rs1_byte_3.clone()),
                LookupInput::from(rs2_byte_3.clone()),
            ],
            &[out_byte_3],
            Num::Var(inputs.decoder_data.funct3),
            is_binary,
        );

        let t3 = (
            [
                LookupInput::from(rs1_byte_3),
                LookupInput::from(rs2_byte_3),
                LookupInput::Variable(out_byte_3),
            ],
            Num::Var(inputs.decoder_data.funct3),
        );

        (
            vec![t0, t1, t2, t3],
            [out_byte_0, out_byte_1, out_byte_2, out_byte_3],
        )
    };

    let (lookup_tuples_csrrw, csrrw_outs): (Vec<([LookupInput<F>; 3], Num<F>)>, _) = {
        // we need 2 more variables that are "exclusive", as those can not be polluted by other opcode
        let execute_delegation = cs.add_variable(); // we do not need boolean check
        let delegation_type = cs.add_variable(); // we also do not need to perform range checks

        let is_csrrw = decoder.perform_csrrw();

        // first let's consult about CSR index. NOTE: our decoder puts it non-signextended into IMM,
        // so we just use lower part of IMM

        // first we want to conditionally assign witness for non-determinism read

        let is_supported_table_output = s0;
        let perform_delegation_table_output = s1;

        let csr_index = inputs.decoder_data.imm[0];

        cs.peek_lookup_value_unconstrained_ext(
            &[LookupInput::Variable(csr_index)],
            &[is_supported_table_output, perform_delegation_table_output],
            TableType::SpecialCSRProperties.to_num(),
            is_csrrw,
        );
        // panic if CSR is not supported (even though we could make a table this way, for convenience table just spans 12 bits)
        cs.add_constraint(
            (Term::from(1) - Term::from(is_supported_table_output)) * is_csrrw.get_terms(),
        );

        let t0 = (
            [
                LookupInput::Variable(csr_index),
                LookupInput::Variable(is_supported_table_output),
                LookupInput::Variable(perform_delegation_table_output),
            ],
            TableType::SpecialCSRProperties.to_num(),
        );

        // choose some temporaries to assign placeholder witness
        let non_determinism_placeholder_low = s2;
        let non_determinism_placeholder_high = s3;

        // we also need to constraint those right away
        let t1 = (
            [
                LookupInput::Variable(non_determinism_placeholder_low),
                LookupInput::from(Constraint::empty()),
                LookupInput::from(Constraint::empty()),
            ],
            TableType::RangeCheck16WithZeroPads.to_num(),
        );

        let t2 = (
            [
                LookupInput::Variable(non_determinism_placeholder_high),
                LookupInput::from(Constraint::empty()),
                LookupInput::from(Constraint::empty()),
            ],
            TableType::RangeCheck16WithZeroPads.to_num(),
        );

        // we will assign all the witness at once
        let exec_flag = is_csrrw.get_variable().unwrap();
        let inner_evaluator = move |placer: &mut CS::WitnessPlacer| {
            let is_csrrw = placer.get_boolean(exec_flag);
            let csr_index_from_decoder = placer.get_u16(csr_index);
            let non_determinism_value = placer.get_oracle_u32(Placeholder::ExternalOracle);

            // Assign to placeholder values

            // it may be assigned by other opcodes as non-boolean, so we get lowest bits instead
            // if we even encounter branchless witness eval, that checks for booleanity
            let is_delegation = placer
                .get_field(perform_delegation_table_output)
                .as_integer()
                .get_bit(0);

            // if it's CSRRW, then non-determinism is negation of delegation,
            // and if it's a delegation then non-determinism value is 0
            let non_determinism_selected_value =
                <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::select(
                    &is_delegation,
                    &<CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(0),
                    &non_determinism_value,
                );
            placer.conditionally_assign_u32(
                [
                    non_determinism_placeholder_low,
                    non_determinism_placeholder_high,
                ],
                &is_csrrw,
                &non_determinism_selected_value,
            );

            // if it's CSRRW, then delegation execution is properly masked (to save constraint degree below)
            let is_delegaiton_masked = is_csrrw.and(&is_delegation);
            placer.assign_mask(execute_delegation, &is_delegaiton_masked);

            // if we indeed perform a delegation, then we assign a CSR index
            let selected_csr_index = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::select(
                &is_delegaiton_masked,
                &csr_index_from_decoder,
                &<CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0),
            );
            placer.assign_u16(delegation_type, &selected_csr_index);
        };

        let value_fn = move |placer: &mut CS::WitnessPlacer| {
            use crate::cs::witness_placer::*;
            let mask = placer.get_boolean(exec_flag);
            witness_early_branch_if_possible(mask.clone(), placer, &inner_evaluator);
        };
        cs.set_values(value_fn);

        // add constraints

        // If it's CSRRW, then delegation execution is properly masked.
        // This variable also has a property that it's 1 IFF it's CSRRW execution at the first place
        cs.add_constraint(
            Term::from(perform_delegation_table_output) * is_csrrw.get_terms()
                - Term::from(execute_delegation),
        );
        // If it's indeed a delegation, then CSR index is properly propagated
        cs.add_constraint(
            Term::from(execute_delegation) * (Term::from(csr_index) - Term::from(delegation_type)),
        );

        // we will transpose a constraint to mask non-determinism value for simplicity,
        // and reuse the fact that `execute_delegation` is not shared

        // what we want, is that if `execute_delegation` == 1, then non-determinism value is always 0
        // (and we checked that it's valid CSR already)
        cs.add_constraint(
            Term::from(non_determinism_placeholder_low) * Term::from(execute_delegation),
        );
        cs.add_constraint(
            Term::from(non_determinism_placeholder_high) * Term::from(execute_delegation),
        );

        // That constraint is enough - if it's csrrw and we execute delegation - then it's 0,
        // if it's CSRRW and it's not a delegation - we will use oracle value directly, because it's the only case

        let delegation_request = DelegatedComputationRequest {
            execute: execute_delegation,
            delegation_type,
            memory_offset_high: Variable::placeholder_variable(),
        };
        cs.add_delegation_request(delegation_request);

        (
            vec![t0, t1, t2],
            [
                non_determinism_placeholder_low,
                non_determinism_placeholder_high,
            ],
        )
    };

    let is_sll = decoder.perform_sll();
    let is_srl = decoder.perform_srl();
    let is_sra = decoder.perform_sra();
    let is_binary = decoder.perform_binary_op();
    let is_csrrw = decoder.perform_csrrw();

    // now manually perform what optimization context does to enforce lookup
    {
        let inputs = [
            (is_sll, lookup_tuples_sll),
            (is_srl, lookup_tuples_srl),
            (is_sra, lookup_tuples_sra),
            (is_binary, lookup_tuples_binops),
            (is_csrrw, lookup_tuples_csrrw),
        ];
        let bound = inputs.iter().map(|el| el.1.len()).max().unwrap();
        for i in 0..bound {
            let mut flags = vec![];
            let mut input_array = vec![];
            let mut table_ids = vec![];

            for (flag, input) in inputs.iter() {
                if let Some((inputs, table_type)) = input.get(i) {
                    flags.push(*flag);
                    input_array.push(inputs.clone());
                    table_ids.push(*table_type);
                }
            }

            assert!(flags.len() > 0);

            // NOTE: here we must select such that in case if particular opcode doesn't use a table all available
            // lookups, then it would degrade to 0/0/0 case. So we select from orthogonal values, and in the worst
            // case we will indeed get 0s everywhere

            let vars: [Num<F>; COMMON_TABLE_WIDTH] = std::array::from_fn(|i| {
                let variants: Vec<Constraint<F>> = input_array
                    .iter()
                    .map(|els| match &els[i] {
                        LookupInput::Variable(var) => Constraint::<F>::from(*var),
                        LookupInput::Expression {
                            linear_terms,
                            constant_coeff,
                        } => {
                            let mut constraint = Constraint::<F>::from_field(*constant_coeff);
                            for (coeff, variable) in linear_terms.iter() {
                                constraint = constraint + Term::from((*coeff, *variable));
                            }

                            constraint
                        }
                    })
                    .collect();

                cs.choose_from_orthogonal_variants_for_linear_terms(&flags, &variants)
            });
            let table_id = cs.choose_from_orthogonal_variants(&flags, &table_ids);

            let inputs: [LookupInput<F>; COMMON_TABLE_WIDTH] =
                vars.map(|x| LookupInput::from(x.get_variable()));

            // we can add formal witness evaluation function here for cases when witness
            // evaluator can count everything on the fly

            let table_id_var = table_id.get_variable();
            cs.enforce_lookup_tuple_for_variable_table(&inputs, table_id_var);
        }
    }

    // select and write to RD

    let rd_low = Term::from(is_sll) * (Term::from(sll_outs[0][0]) + Term::from(sll_outs[0][1])) + // SLL
    Term::from(is_srl) * (Term::from(srl_outs[0][0]) + Term::from(srl_outs[0][1])) + // SRL
    Term::from(is_sra) * (Term::from(sra_outs[0][0]) + Term::from(sra_outs[0][1]) + Term::from(sra_outs[0][2])) + // SRA
    Term::from(is_csrrw) * Term::from(csrrw_outs[0]) + // CSRRW non-determinism
    Term::from(is_binary) * (Term::from(1 << 8) * Term::from(binops_outs[1]) + Term::from(binops_outs[0])); // BINARY
    let rd_low = cs.add_variable_from_constraint(rd_low);

    let rd_high = Term::from(is_sll) * (Term::from(sll_outs[1][0]) + Term::from(sll_outs[1][1])) + // SLL
    Term::from(is_srl) * (Term::from(srl_outs[1][0]) + Term::from(srl_outs[1][1])) + // SRL
    Term::from(is_sra) * (Term::from(sra_outs[1][0]) + Term::from(sra_outs[1][1]) + Term::from(sra_outs[1][2])) + // SRA
    Term::from(is_csrrw) * Term::from(csrrw_outs[1]) + // CSRRW non-determinism
    Term::from(is_binary) * (Term::from(1 << 8) * Term::from(binops_outs[3]) + Term::from(binops_outs[2])); // BINARY
    let rd_high = cs.add_variable_from_constraint(rd_high);

    let rd_reg = Register([Num::Var(rd_low), Num::Var(rd_high)]);
    let is_rd_x0 = Boolean::Is(inputs.decoder_data.rd_is_zero);
    let rd_mem_query = set_rd_with_mask_as_shuffle_ram(
        cs,
        Num::Var(inputs.decoder_data.rd_index),
        rd_reg,
        is_rd_x0,
        true,
    );
    cs.add_shuffle_ram_query(rd_mem_query);

    // and we can increment PC without range checks

    // write to PC
    bump_pc_no_range_checks_explicit(
        cs,
        Register(inputs.cycle_start_state.pc.map(|x| Num::Var(x))),
        Register(inputs.cycle_end_state.pc.map(|x| Num::Var(x))),
    );
}

pub fn shift_binop_csrrw_circuit_with_preprocessed_bytecode<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
) {
    let input = cs.allocate_execution_circuit_state::<true>();
    apply_shift_binop_csrrw(cs, input);
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::utils::serialize_to_file;

    #[test]
    fn compile_shift_binop_csrrw_circuit() {
        use crate::machine::machine_configurations::create_csr_table_for_delegation;
        use ::field::Mersenne31Field;

        let csr_table = create_csr_table_for_delegation::<Mersenne31Field>(
            true,
            &[],
            TableType::SpecialCSRProperties.to_table_id(),
        );

        let compiled = compile_unrolled_circuit_state_transition::<Mersenne31Field>(
            &|cs| {
                shift_binop_csrrw_table_addition_fn(cs);
                cs.add_table_with_content(
                    TableType::SpecialCSRProperties,
                    LookupWrapper::Dimensional3(csr_table.clone()),
                );
            },
            &|cs| shift_binop_csrrw_circuit_with_preprocessed_bytecode(cs),
            1 << 20,
            24,
        );

        serialize_to_file(&compiled, "shift_binop_csrrw_preprocessed_layout.json");
    }

    #[test]
    fn compile_shift_binop_csrrw_witness_graph() {
        use crate::machine::machine_configurations::create_csr_table_for_delegation;
        use ::field::Mersenne31Field;

        let csr_table = create_csr_table_for_delegation::<Mersenne31Field>(
            true,
            &[],
            TableType::SpecialCSRProperties.to_table_id(),
        );

        let ssa_forms = dump_ssa_witness_eval_form_for_unrolled_circuit::<Mersenne31Field>(
            &|cs| {
                shift_binop_csrrw_table_addition_fn(cs);
                cs.add_table_with_content(
                    TableType::SpecialCSRProperties,
                    LookupWrapper::Dimensional3(csr_table.clone()),
                );
            },
            &|cs| shift_binop_csrrw_circuit_with_preprocessed_bytecode(cs),
        );
        serialize_to_file(&ssa_forms, "shift_binop_csrrw_preprocessed_ssa.json");
    }
}
