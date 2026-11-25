pub mod l1_wrap {
    use prover::cs::gkr_compiler::GKRCircuitArtifact;
    use prover::field::Proth120;
    use prover::worker::Worker;
    use unified_reduced_machine_proth120_2_21::l1_wrap::l1_wrap_setup_from_artifact;
    use unified_reduced_machine_proth120_2_21::L1WrapSetup;

    use prover::gkr::prover_config::example_configs::l1_wrap::ETHPROOFS_TRACE_LEN_LOG2 as TRACE_LEN_LOG2;

    const LAYOUT_JSON: &str = include_str!("../generated/layout.json");

    fn circuit_artifact() -> GKRCircuitArtifact<Proth120> {
        serde_json::from_str(LAYOUT_JSON).expect("embedded 2^22 Proth120 unified layout")
    }

    pub fn l1_wrap_setup(binary: &[u32], text: &[u32], worker: &Worker) -> L1WrapSetup {
        let circuit = circuit_artifact();
        assert_eq!(circuit.trace_len, 1 << TRACE_LEN_LOG2);
        l1_wrap_setup_from_artifact(circuit, binary, text, worker)
    }
}

#[cfg(test)]
mod test {
    use prover::cs::gkr_circuits::unified_reduced_machine::{
        build_unified_artifact_core,
        unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr_core,
        unified_register_all_tables,
    };
    use prover::cs::gkr_compiler::{dump_ssa_witness_eval_form, GKRCircuitArtifact};
    use prover::field::baby_bear::base::BabyBearField;
    use prover::field::Proth120;
    use prover::gkr::prover_config::example_configs::l1_wrap::ETHPROOFS_TRACE_LEN_LOG2;
    use test_utils::skip_if_ci;
    use unified_reduced_machine_proth120_2_21::l1_wrap::ROM;

    fn compile(trace_len_log2: usize) -> GKRCircuitArtifact<Proth120> {
        build_unified_artifact_core::<Proth120, BabyBearField>(true, trace_len_log2, 1, ROM)
    }

    #[test]
    fn generate() {
        skip_if_ci!();

        let layout = compile(ETHPROOFS_TRACE_LEN_LOG2);
        let dst = std::fs::File::create("generated/layout.json").unwrap();
        serde_json::to_writer_pretty(dst, &layout).unwrap();
    }

    #[test]
    fn witness_eval_fn_matches_sibling() {
        let ssa = dump_ssa_witness_eval_form::<Proth120>(
            &|cs| unified_register_all_tables(cs, ROM),
            &|cs| {
                unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr_core::<
                    Proth120,
                    BabyBearField,
                    _,
                >(cs, ROM)
            },
        );
        let layout = compile(ETHPROOFS_TRACE_LEN_LOG2);
        let generated = witness_eval_generator::derive_from_ssa::derive_from_gkr_ssa(
            &ssa, &layout, false, "Proth120",
        )
        .to_string();
        let sibling = include_str!(
            "../../unified_reduced_machine_proth120_2_21/generated/witness_generation_fn.rs"
        );
        assert!(
            generated == sibling,
            "2^22 L1 wrap witness generation differs from the shared witness function"
        );
    }
}
