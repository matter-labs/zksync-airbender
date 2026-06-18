use cs::cs::circuit_trait::Circuit;
use cs::gkr_compiler::*;
use cs::tables::TableDriver;
use cs::witness_placer::graph_description::RawExpression;
use field::baby_bear::base::BabyBearField;
use field::PrimeField;

pub trait DelegationCircuit<F: PrimeField> {
    const DELEGATION_TYPE_ID: u16;
    const DOMAIN_SIZE_LOG2: u32;

    fn table_driver_fn(table_driver: &mut TableDriver<F>);
    fn table_addition_fn<CS: Circuit<F>>(cs: &mut CS);
    fn circuit_fn<CS: Circuit<F>>(cs: &mut CS);

    fn get_circuit(use_caches: bool) -> GKRCircuitArtifact<F> {
        if use_caches {
            compile_delegation_circuit_into_gkr::<F>(
                &|cs| Self::table_addition_fn(cs),
                &|cs| {
                    let _ = Self::circuit_fn(cs);
                },
                Self::DOMAIN_SIZE_LOG2 as usize,
            )
        } else {
            compile_delegation_circuit_into_gkr_without_caches::<F>(
                &|cs| Self::table_addition_fn(cs),
                &|cs| {
                    let _ = Self::circuit_fn(cs);
                },
                Self::DOMAIN_SIZE_LOG2 as usize,
            )
        }
    }

    fn get_ssa_form() -> Vec<Vec<RawExpression<F>>> {
        dump_ssa_witness_eval_form::<F>(&|cs| Self::table_addition_fn(cs), &|cs| {
            let _ = Self::circuit_fn(cs);
        })
    }

    fn get_table_driver() -> TableDriver<F> {
        let mut table_driver = TableDriver::<F>::new();
        Self::table_driver_fn(&mut table_driver);

        table_driver
    }
}

pub trait RiscVCycleCircuit<F: PrimeField, const USE_BYTECODE: bool> {
    const CIRCUIT_FAMILY: u8;
    const DOMAIN_SIZE_LOG2: u32;

    fn table_driver_fn(table_driver: &mut TableDriver<F>, bytecode: &[u32]);
    fn table_addition_fn<CS: Circuit<F>>(cs: &mut CS, bytecode: &[u32]);
    fn circuit_fn<CS: Circuit<F>>(cs: &mut CS, bytecode: &[u32]);
}

pub fn risc_v_non_mem_get_circuit<F: PrimeField, C: RiscVCycleCircuit<F, false>>(
    use_caches: bool,
) -> GKRCircuitArtifact<F> {
    if use_caches {
        compile_unrolled_circuit_state_transition_into_gkr::<F>(
            &|cs| C::table_addition_fn(cs, &[]),
            &|cs| C::circuit_fn(cs, &[]),
            common_constants::ROM_WORD_SIZE,
            C::DOMAIN_SIZE_LOG2 as usize,
        )
    } else {
        compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches::<F>(
            &|cs| C::table_addition_fn(cs, &[]),
            &|cs| C::circuit_fn(cs, &[]),
            common_constants::ROM_WORD_SIZE,
            C::DOMAIN_SIZE_LOG2 as usize,
        )
    }
}

pub fn risc_v_non_mem_get_ssa_form<F: PrimeField, C: RiscVCycleCircuit<F, false>>(
) -> Vec<Vec<RawExpression<F>>> {
    dump_ssa_witness_eval_form::<F>(&|cs| C::table_addition_fn(cs, &[]), &|cs| {
        let _ = C::circuit_fn(cs, &[]);
    })
}

pub fn risc_v_non_mem_get_table_driver<F: PrimeField, C: RiscVCycleCircuit<F, false>>(
) -> TableDriver<F> {
    let mut table_driver = TableDriver::<F>::new();
    C::table_driver_fn(&mut table_driver, &[]);

    table_driver
}

pub fn risc_v_with_mem_get_circuit<F: PrimeField, C: RiscVCycleCircuit<F, true>>(
    use_caches: bool,
    bytecode: &[u32],
) -> GKRCircuitArtifact<F> {
    assert!(bytecode.is_empty() || bytecode.len() == common_constants::ROM_WORD_SIZE);
    if use_caches {
        compile_unrolled_circuit_state_transition_into_gkr::<F>(
            &|cs| C::table_addition_fn(cs, bytecode),
            &|cs| C::circuit_fn(cs, bytecode),
            common_constants::ROM_WORD_SIZE,
            C::DOMAIN_SIZE_LOG2 as usize,
        )
    } else {
        compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches::<F>(
            &|cs| C::table_addition_fn(cs, &[]),
            &|cs| C::circuit_fn(cs, &[]),
            common_constants::ROM_WORD_SIZE,
            C::DOMAIN_SIZE_LOG2 as usize,
        )
    }
}

pub fn risc_v_with_mem_get_ssa_form<F: PrimeField, C: RiscVCycleCircuit<F, true>>(
    bytecode: &[u32],
) -> Vec<Vec<RawExpression<F>>> {
    assert!(bytecode.is_empty() || bytecode.len() == common_constants::ROM_WORD_SIZE);
    dump_ssa_witness_eval_form::<F>(&|cs| C::table_addition_fn(cs, bytecode), &|cs| {
        let _ = C::circuit_fn(cs, bytecode);
    })
}

pub fn risc_v_with_mem_get_table_driver<F: PrimeField, C: RiscVCycleCircuit<F, true>>(
    bytecode: &[u32],
) -> TableDriver<F> {
    assert!(bytecode.is_empty() || bytecode.len() == common_constants::ROM_WORD_SIZE);
    let mut table_driver = TableDriver::<F>::new();
    C::table_driver_fn(&mut table_driver, bytecode);

    table_driver
}

pub fn generate_default_delegation_artifacts<C: DelegationCircuit<BabyBearField>>(
    use_caches: bool,
) {
    fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
        let mut dst = std::fs::File::create(filename).unwrap();
        serde_json::to_writer_pretty(&mut dst, el).unwrap();
    }

    use std::io::Write;

    let compiled_circuit: cs::gkr_compiler::GKRCircuitArtifact<BabyBearField> =
        C::get_circuit(use_caches);
    serialize_to_file(&compiled_circuit, "generated/layout.json");
    let ssa = C::get_ssa_form();

    let full_stream = witness_eval_generator::derive_from_ssa::derive_from_gkr_ssa(
        &ssa,
        &compiled_circuit,
        false,
        "BabyBearField",
    );
    std::fs::File::create("generated/witness_generation_fn.rs")
        .unwrap()
        .write_all(&full_stream.to_string().as_bytes())
        .unwrap();
}

pub fn generate_default_risc_v_non_mem_cycles_artifacts<
    C: RiscVCycleCircuit<BabyBearField, false>,
>(
    use_caches: bool,
) {
    fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
        let mut dst = std::fs::File::create(filename).unwrap();
        serde_json::to_writer_pretty(&mut dst, el).unwrap();
    }

    use std::io::Write;

    let compiled_circuit: cs::gkr_compiler::GKRCircuitArtifact<BabyBearField> =
        risc_v_non_mem_get_circuit::<BabyBearField, C>(use_caches);
    serialize_to_file(&compiled_circuit, "generated/layout.json");
    let ssa = risc_v_non_mem_get_ssa_form::<BabyBearField, C>();

    let full_stream = witness_eval_generator::derive_from_ssa::derive_from_gkr_ssa(
        &ssa,
        &compiled_circuit,
        false,
        "BabyBearField",
    );
    std::fs::File::create("generated/witness_generation_fn.rs")
        .unwrap()
        .write_all(&full_stream.to_string().as_bytes())
        .unwrap();
}

pub fn generate_default_risc_v_with_mem_cycles_artifacts<
    C: RiscVCycleCircuit<BabyBearField, true>,
>(
    use_caches: bool,
) {
    fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
        let mut dst = std::fs::File::create(filename).unwrap();
        serde_json::to_writer_pretty(&mut dst, el).unwrap();
    }

    use std::io::Write;

    let compiled_circuit: cs::gkr_compiler::GKRCircuitArtifact<BabyBearField> =
        risc_v_with_mem_get_circuit::<BabyBearField, C>(use_caches, &[]);
    serialize_to_file(&compiled_circuit, "generated/layout.json");
    let ssa = risc_v_with_mem_get_ssa_form::<BabyBearField, C>(&[]);

    let full_stream = witness_eval_generator::derive_from_ssa::derive_from_gkr_ssa(
        &ssa,
        &compiled_circuit,
        false,
        "BabyBearField",
    );
    std::fs::File::create("generated/witness_generation_fn.rs")
        .unwrap()
        .write_all(&full_stream.to_string().as_bytes())
        .unwrap();
}
