use super::*;

pub fn apply_non_determinism_csr_only_assuming_no_unimp<
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
        // we assume that only CSR index that exists is the csr one, so we just perform CSSRW/CSSRS/CSRSC
        let external_oracle =
            Register::new_unchecked_from_placeholder::<CS>(cs, Placeholder::ExternalOracle);
        external_oracle.0.iter().for_each(|x| {
            cs.require_invariant(x.get_variable(), Invariant::RangeChecked { width: 16 })
        });

        if SUPPORT_CSRRC == false && SUPPORT_CSRRS == false {
            if exec_flag.get_value(cs).unwrap_or(false) {
                println!("CSR");
                dbg!(src1.get_value_unsigned(cs));
            }

            let returned_value = [
                Constraint::<F>::from(external_oracle.0[0].get_variable()),
                Constraint::<F>::from(external_oracle.0[1].get_variable()),
            ];

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
