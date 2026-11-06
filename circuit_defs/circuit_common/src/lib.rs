use cs::cs::circuit_trait::Circuit;
use cs::gkr_compiler::*;
use cs::tables::TableDriver;
use cs::witness_placer::graph_description::RawExpression;
use field::baby_bear::base::BabyBearField;
use field::PrimeField;

pub use prover::definitions::SecurityLevel;
pub use prover::gkr::prover_config::ProverConfig;

/// The standard prover config of a circuit with a `2^trace_len_log2` trace at
/// `level` — what every production circuit returns from its `prover_config`
/// unless it needs a special schedule or a packed base commitment.
pub fn default_prover_config(trace_len_log2: u32, level: SecurityLevel) -> ProverConfig {
    prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(
        trace_len_log2 as usize,
        level,
    )
}

/// log2 of the trace length of the configs returned by `prover_config`,
/// asserting it is the same at every security level (the trace length is a
/// property of the circuit, the security level only changes the schedules).
fn trace_len_log2_of(prover_config: impl Fn(SecurityLevel) -> ProverConfig) -> u32 {
    let first = prover_config(SecurityLevel::ALL[0]).trace_len_log2;
    for &level in SecurityLevel::ALL.iter().skip(1) {
        assert_eq!(
            prover_config(level).trace_len_log2,
            first,
            "the trace length must not depend on the security level"
        );
    }
    first as u32
}

/// The configs of a circuit at EVERY security level, indexed by `SecurityLevel
/// as usize` (see [`prover_config_at`]): what a setup carries so that every
/// commitment / proof made from it uses the circuit's own geometry.
pub fn prover_configs_for_all_levels(
    prover_config: impl Fn(SecurityLevel) -> ProverConfig,
) -> Vec<ProverConfig> {
    SecurityLevel::ALL
        .iter()
        .enumerate()
        .map(|(idx, &level)| {
            assert_eq!(level as usize, idx);
            let config = prover_config(level);
            assert_eq!(config.security_level, level);
            config
        })
        .collect()
}

/// The config for `level` out of [`prover_configs_for_all_levels`].
pub fn prover_config_at(configs: &[ProverConfig], level: SecurityLevel) -> &ProverConfig {
    let config = &configs[level as usize];
    assert_eq!(config.security_level, level);
    config
}

pub trait DelegationCircuit<F: PrimeField> {
    const DELEGATION_TYPE_ID: u16;

    /// The prover config this circuit is proved with (and its verifier is
    /// generated for) at `level`: trace length, sumcheck schedules, WHIR
    /// schedule, base-commitment packing. The single source of the circuit's
    /// proving geometry — the artifact generators serialize it next to the
    /// layout (`generated/prover_config_<level>.json`) and the verifier
    /// generator reads it back from there.
    fn prover_config(level: SecurityLevel) -> ProverConfig;

    /// log2 of the trace length (`prover_config(..).trace_len_log2`, the same
    /// at every security level).
    fn trace_len_log2() -> u32 {
        trace_len_log2_of(Self::prover_config)
    }

    fn table_driver_fn(table_driver: &mut TableDriver<F>);
    fn table_addition_fn<CS: Circuit<F>>(cs: &mut CS);
    fn circuit_fn<CS: Circuit<F>>(cs: &mut CS);

    fn get_circuit(use_caches: bool) -> GKRCircuitArtifact<F> {
        if use_caches {
            compile_delegation_circuit_into_gkr::<F>(
                &|cs| Self::table_addition_fn(cs),
                &|cs| {
                    Self::circuit_fn(cs);
                },
                Self::trace_len_log2() as usize,
            )
        } else {
            compile_delegation_circuit_into_gkr_without_caches::<F>(
                &|cs| Self::table_addition_fn(cs),
                &|cs| {
                    Self::circuit_fn(cs);
                },
                Self::trace_len_log2() as usize,
            )
        }
    }

    fn get_ssa_form() -> Vec<Vec<RawExpression<F>>> {
        dump_ssa_witness_eval_form::<F>(&|cs| Self::table_addition_fn(cs), &|cs| {
            Self::circuit_fn(cs);
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
    const NUM_INIT_AND_TEARDOWN_PAIRS: usize;

    /// See [`DelegationCircuit::prover_config`].
    fn prover_config(level: SecurityLevel) -> ProverConfig;

    /// log2 of the trace length (`prover_config(..).trace_len_log2`, the same
    /// at every security level).
    fn trace_len_log2() -> u32 {
        trace_len_log2_of(Self::prover_config)
    }

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
            C::trace_len_log2() as usize,
            0,
        )
    } else {
        compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches::<F>(
            &|cs| C::table_addition_fn(cs, &[]),
            &|cs| C::circuit_fn(cs, &[]),
            common_constants::ROM_WORD_SIZE,
            C::trace_len_log2() as usize,
            0,
        )
    }
}

pub fn risc_v_non_mem_get_ssa_form<F: PrimeField, C: RiscVCycleCircuit<F, false>>(
) -> Vec<Vec<RawExpression<F>>> {
    dump_ssa_witness_eval_form::<F>(&|cs| C::table_addition_fn(cs, &[]), &|cs| {
        C::circuit_fn(cs, &[]);
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
            C::trace_len_log2() as usize,
            C::NUM_INIT_AND_TEARDOWN_PAIRS,
        )
    } else {
        compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches::<F>(
            &|cs| C::table_addition_fn(cs, &[]),
            &|cs| C::circuit_fn(cs, &[]),
            common_constants::ROM_WORD_SIZE,
            C::trace_len_log2() as usize,
            C::NUM_INIT_AND_TEARDOWN_PAIRS,
        )
    }
}

pub fn risc_v_with_mem_get_ssa_form<F: PrimeField, C: RiscVCycleCircuit<F, true>>(
    bytecode: &[u32],
) -> Vec<Vec<RawExpression<F>>> {
    assert!(bytecode.is_empty() || bytecode.len() == common_constants::ROM_WORD_SIZE);
    dump_ssa_witness_eval_form::<F>(&|cs| C::table_addition_fn(cs, bytecode), &|cs| {
        C::circuit_fn(cs, bytecode);
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
    let compiled_circuit: cs::gkr_compiler::GKRCircuitArtifact<BabyBearField> =
        C::get_circuit(use_caches);
    let ssa = C::get_ssa_form();

    save_artifacts(compiled_circuit, ssa, C::prover_config);
}

pub fn generate_default_risc_v_non_mem_cycles_artifacts<
    C: RiscVCycleCircuit<BabyBearField, false>,
>(
    use_caches: bool,
) {
    let compiled_circuit: cs::gkr_compiler::GKRCircuitArtifact<BabyBearField> =
        risc_v_non_mem_get_circuit::<BabyBearField, C>(use_caches);
    let ssa = risc_v_non_mem_get_ssa_form::<BabyBearField, C>();

    save_artifacts(compiled_circuit, ssa, C::prover_config);
}

pub fn generate_default_risc_v_with_mem_cycles_artifacts<
    C: RiscVCycleCircuit<BabyBearField, true>,
>(
    use_caches: bool,
) {
    let compiled_circuit: cs::gkr_compiler::GKRCircuitArtifact<BabyBearField> =
        risc_v_with_mem_get_circuit::<BabyBearField, C>(use_caches, &[]);
    let ssa = risc_v_with_mem_get_ssa_form::<BabyBearField, C>(&[]);

    save_artifacts(compiled_circuit, ssa, C::prover_config);
}

/// File (relative to the circuit crate root) the circuit's prover config for
/// `level` is serialized to by the artifact generators, next to
/// `generated/layout.json`.
pub fn prover_config_file_name(level: SecurityLevel) -> String {
    format!("generated/prover_config_{}.json", level.dir_suffix())
}

/// Serialize the circuit's prover config for every security level next to the
/// layout ([`prover_config_file_name`]), after checking it against the compiled
/// circuit (trace length) and the WHIR message size (`validate_for_whir_message_size`).
pub fn save_prover_configs(
    compiled_circuit: &cs::gkr_compiler::GKRCircuitArtifact<BabyBearField>,
    prover_config: impl Fn(SecurityLevel) -> ProverConfig,
) {
    for &level in SecurityLevel::ALL {
        let config = prover_config(level);
        assert_eq!(
            1usize << config.trace_len_log2,
            compiled_circuit.trace_len,
            "the prover config's trace length must match the compiled circuit's"
        );
        config.validate_for_whir_message_size(config.whir_message_size_log2());
        let mut dst = std::fs::File::create(prover_config_file_name(level)).unwrap();
        serde_json::to_writer_pretty(&mut dst, &config).unwrap();
    }
}

pub fn save_artifacts(
    compiled_circuit: cs::gkr_compiler::GKRCircuitArtifact<BabyBearField>,
    ssa: Vec<Vec<RawExpression<BabyBearField>>>,
    prover_config: impl Fn(SecurityLevel) -> ProverConfig,
) {
    fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
        let mut dst = std::fs::File::create(filename).unwrap();
        serde_json::to_writer_pretty(&mut dst, el).unwrap();
    }

    use std::io::Write;
    serialize_to_file(&compiled_circuit, "generated/layout.json");
    save_prover_configs(&compiled_circuit, prover_config);

    let full_stream = witness_eval_generator::derive_from_ssa::derive_from_gkr_ssa(
        &ssa,
        &compiled_circuit,
        false,
        "BabyBearField",
    );
    std::fs::File::create("generated/witness_generation_fn.rs")
        .unwrap()
        .write_all(full_stream.to_string().as_bytes())
        .unwrap();
}
