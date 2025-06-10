use super::*;

pub fn apply_csr_with_delegation<
    F: PrimeField,
    CS: Circuit<F>,
    ST: BaseMachineState<F>,
    RS: RegisterValueSource<F>,
    DE: DecoderOutputSource<F, RS>,
    BS: IndexableBooleanSet,
    const SUPPORT_CSRRC: bool,
    const SUPPORT_CSRRS: bool,
    const SUPPORT_CSR_IMMEDIATES: bool,
    const ASSUME_TRUSTED_CODE: bool,
    const OUTPUT_EXACT_EXCEPTIONS: bool,
>(
    cs: &mut CS,
    _machine_state: &ST,
    inputs: &DE,
    boolean_set: &BS,
    opt_ctx: &mut OptimizationContext<F, CS>,
) -> CommonDiffs<F> {
    if SUPPORT_CSR_IMMEDIATES {
        todo!()
    }

    opt_ctx.reset_indexers();
    let exec_flag = boolean_set.get_major_flag(CSR_COMMON_OP_KEY);

    let src1 = inputs.get_rs1_or_equivalent().get_register();

    if ASSUME_TRUSTED_CODE {
        // access non-determinism CSR, or perform delegation
        let external_oracle =
            Register::new_unchecked_from_placeholder::<CS>(cs, Placeholder::ExternalOracle);
        external_oracle.0.iter().for_each(|x| {
            cs.require_invariant(x.get_variable(), Invariant::RangeChecked { width: 16 })
        });

        if SUPPORT_CSRRC == false && SUPPORT_CSRRS == false {
            let csr_index = inputs.funct12();
            let [is_supported_csr, is_for_delegation] = opt_ctx
                .append_lookup_relation_from_linear_terms::<1, 2>(
                    cs,
                    &[csr_index.clone()],
                    TableType::SpecialCSRProperties.to_num(),
                    exec_flag,
                );
            // panic if CSR is not supported - this way we can avoid comparing to the UNIMP before decoding
            cs.add_constraint(
                (Term::from(1) - Term::from(is_supported_csr)) * exec_flag.get_terms(),
            );

            // we assume trusted code, so we do not need to enforce that CSR is supported
            let should_delegate = cs.add_variable_from_constraint(
                Term::from(is_for_delegation) * Term::from(exec_flag),
            );

            // in our ABI we use highest 16 bits of src1 as the offset
            let offset = src1.0[1];

            // and to have easier consistency with memory witness delegation we also want to mask everything down to 0s
            let offset_masked =
                cs.add_variable_from_constraint(Term::from(should_delegate) * Term::from(offset));
            let csr_index_masked =
                cs.add_variable_from_constraint(Term::from(should_delegate) * csr_index);

            let delegation_request = DelegatedComputationRequest {
                execute: should_delegate,
                degegation_type: csr_index_masked,
                memory_offset_high: offset_masked,
            };
            cs.add_delegation_request(delegation_request);

            // if we do DO delegate, then we require that oracle is 0 - and prover can still satisfy it
            // even though `is_delegate` is not strictly boolean
            cs.add_constraint(Term::from(is_for_delegation) * Term::from(external_oracle.0[0]));
            cs.add_constraint(Term::from(is_for_delegation) * Term::from(external_oracle.0[1]));

            let returned_value = [
                Constraint::<F>::from(external_oracle.0[0]),
                Constraint::<F>::from(external_oracle.0[1]),
            ];

            if exec_flag.get_value(cs).unwrap_or(false) {
                println!("CSR");
                dbg!(src1.get_value_unsigned(cs));
                if cs.get_value(should_delegate).unwrap() == F::ONE {
                    println!(
                        "Perform delegation to CSR {} with offset {}",
                        cs.get_value(csr_index_masked).unwrap(),
                        cs.get_value(offset_masked).unwrap(),
                    );
                }
            }

            CommonDiffs {
                exec_flag,
                trapped: None,
                trap_reason: None,
                rd_value: vec![(returned_value, exec_flag)],
                new_pc_value: NextPcValue::Default,
            }
        } else {
            todo!()
        }
    } else {
        todo!()
    }
}
