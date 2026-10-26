use cs::cs::circuit_trait::Circuit;
use cs::gkr_compiler::*;
use cs::tables::TableDriver;
use cs::witness_placer::graph_description::RawExpression;
use field::baby_bear::base::BabyBearField;
use field::PrimeField;

pub use prover::definitions::SecurityLevel;
pub use prover::gkr::prover_config::{
    BaseColumns, BasePacking, ProverConfig, SoundnessMode, WhirInput,
};

/// What a circuit definition decides about its proving geometry: its trace
/// length and how its base columns are committed ([`BasePacking`]). The
/// committed column widths — the committed-polynomial count the WHIR batching
/// challenge combines — are NOT declared: the compiled circuit artifact
/// ([`GKRCircuitArtifact`], [`BaseColumns::of`]) is their single source, so a
/// config whose schedule depends on them is built from the artifact
/// ([`Self::prover_config`]); the default-mode config, which does not, can
/// also be built from the geometry alone ([`Self::default_mode_prover_config`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CircuitGeometry {
    pub trace_len_log2: u32,
    pub base_packing: BasePacking,
}

impl CircuitGeometry {
    /// The prover config under `mode` at `level` for the compiled circuit:
    /// the standard GKR side for the trace length and the WHIR schedule
    /// computed for what enters WHIR after the packing ([`WhirInput`], with
    /// the committed-polynomial count read off `compiled_circuit`); panics
    /// when the trace lengths disagree or no schedule exists for that shape
    /// under `mode`.
    pub fn prover_config<F: PrimeField>(
        &self,
        compiled_circuit: &GKRCircuitArtifact<F>,
        level: SecurityLevel,
        mode: SoundnessMode,
    ) -> ProverConfig {
        self.assert_trace_len(compiled_circuit);
        prover::gkr::prover_config::example_configs::prover_config(
            mode,
            level,
            self.trace_len_log2 as usize,
            self.base_packing,
            Some(&BaseColumns::of(compiled_circuit)),
        )
    }

    /// The config in the default [`SoundnessMode`] from the geometry alone
    /// (no compiled circuit at hand, e.g. a prover job keyed by circuit type):
    /// the default mode's schedule does not depend on the committed column
    /// count. Equal to [`Self::prover_config`] in that mode.
    pub fn default_mode_prover_config(&self, level: SecurityLevel) -> ProverConfig {
        prover::gkr::prover_config::example_configs::prover_config(
            SoundnessMode::DEFAULT,
            level,
            self.trace_len_log2 as usize,
            self.base_packing,
            None,
        )
    }

    /// What enters WHIR for the compiled circuit: the committed polynomial
    /// size and count after the packing (separate memory and witness
    /// commitments).
    pub fn whir_input<F: PrimeField>(&self, compiled_circuit: &GKRCircuitArtifact<F>) -> WhirInput {
        self.assert_trace_len(compiled_circuit);
        WhirInput::new(
            self.trace_len_log2 as usize,
            self.base_packing,
            &BaseColumns::of(compiled_circuit),
            prover::gkr::prover_config::CommitmentMode::SeparateMemoryAndWitness,
        )
    }

    /// The notes on the non-obvious parameters of the config under `mode`
    /// (`None` for a mode without such notes), see
    /// `example_configs::whir_schedule_notes`.
    pub fn prover_config_notes<F: PrimeField>(
        &self,
        compiled_circuit: &GKRCircuitArtifact<F>,
        level: SecurityLevel,
        mode: SoundnessMode,
    ) -> Option<String> {
        prover::gkr::prover_config::example_configs::whir_schedule_notes(
            mode,
            level,
            &self.whir_input(compiled_circuit),
        )
    }

    fn assert_trace_len<F: PrimeField>(&self, compiled_circuit: &GKRCircuitArtifact<F>) {
        assert_eq!(
            1usize << self.trace_len_log2,
            compiled_circuit.trace_len,
            "the declared trace length must match the compiled circuit's"
        );
    }
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

    /// log2 of the circuit's LOGICAL trace length for the purposes of GKR
    /// (the rows of the circuit trace); the polynomials WHIR commits may be
    /// larger when the base commitment packs columns (`BASE_PACKING`).
    const TRACE_LEN_LOG2: u32;
    /// How the base columns are committed (physical / virtual packing).
    const BASE_PACKING: BasePacking = BasePacking::NONE;

    /// The circuit's proving geometry (trace length, packing): with the
    /// compiled circuit artifact (the source of the committed column widths)
    /// it yields the prover config of every [`SoundnessMode`]. The artifact
    /// generators serialize those next to the layout
    /// (`generated/prover_config_<level>_<mode>.json`, plus the mode's notes
    /// as `.md` where it has them) and the verifier generator reads the
    /// default mode's back from there.
    fn geometry() -> CircuitGeometry {
        CircuitGeometry {
            trace_len_log2: Self::TRACE_LEN_LOG2,
            base_packing: Self::BASE_PACKING,
        }
    }

    /// The prover config this circuit is proved with (and its verifier is
    /// generated for) at `level` under `mode`: trace length, sumcheck
    /// schedules, WHIR schedule, base-commitment packing. Needs the compiled
    /// circuit (the committed column count).
    fn prover_config_in_mode(
        compiled_circuit: &GKRCircuitArtifact<F>,
        level: SecurityLevel,
        mode: SoundnessMode,
    ) -> ProverConfig {
        Self::geometry().prover_config(compiled_circuit, level, mode)
    }

    /// The config in the default [`SoundnessMode`], from the geometry alone
    /// (see [`CircuitGeometry::default_mode_prover_config`]).
    fn prover_config(level: SecurityLevel) -> ProverConfig {
        Self::geometry().default_mode_prover_config(level)
    }

    /// log2 of the trace length.
    fn trace_len_log2() -> u32 {
        Self::TRACE_LEN_LOG2
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

    /// See [`DelegationCircuit::TRACE_LEN_LOG2`].
    const TRACE_LEN_LOG2: u32;
    /// See [`DelegationCircuit::BASE_PACKING`].
    const BASE_PACKING: BasePacking = BasePacking::NONE;

    /// See [`DelegationCircuit::geometry`].
    fn geometry() -> CircuitGeometry {
        CircuitGeometry {
            trace_len_log2: Self::TRACE_LEN_LOG2,
            base_packing: Self::BASE_PACKING,
        }
    }

    /// See [`DelegationCircuit::prover_config_in_mode`].
    fn prover_config_in_mode(
        compiled_circuit: &GKRCircuitArtifact<F>,
        level: SecurityLevel,
        mode: SoundnessMode,
    ) -> ProverConfig {
        Self::geometry().prover_config(compiled_circuit, level, mode)
    }

    /// See [`DelegationCircuit::prover_config`].
    fn prover_config(level: SecurityLevel) -> ProverConfig {
        Self::geometry().default_mode_prover_config(level)
    }

    /// log2 of the trace length.
    fn trace_len_log2() -> u32 {
        Self::TRACE_LEN_LOG2
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

    save_artifacts(compiled_circuit, ssa, &C::geometry());
}

pub fn generate_default_risc_v_non_mem_cycles_artifacts<
    C: RiscVCycleCircuit<BabyBearField, false>,
>(
    use_caches: bool,
) {
    let compiled_circuit: cs::gkr_compiler::GKRCircuitArtifact<BabyBearField> =
        risc_v_non_mem_get_circuit::<BabyBearField, C>(use_caches);
    let ssa = risc_v_non_mem_get_ssa_form::<BabyBearField, C>();

    save_artifacts(compiled_circuit, ssa, &C::geometry());
}

pub fn generate_default_risc_v_with_mem_cycles_artifacts<
    C: RiscVCycleCircuit<BabyBearField, true>,
>(
    use_caches: bool,
) {
    let compiled_circuit: cs::gkr_compiler::GKRCircuitArtifact<BabyBearField> =
        risc_v_with_mem_get_circuit::<BabyBearField, C>(use_caches, &[]);
    let ssa = risc_v_with_mem_get_ssa_form::<BabyBearField, C>(&[]);

    save_artifacts(compiled_circuit, ssa, &C::geometry());
}

/// File (relative to the circuit crate root) the circuit's prover config for
/// `level` under `mode` is serialized to by the artifact generators, next to
/// `generated/layout.json`.
pub fn prover_config_file_name(level: SecurityLevel, mode: SoundnessMode) -> String {
    format!(
        "generated/prover_config_{}_{}.json",
        level.dir_suffix(),
        mode.file_suffix()
    )
}

/// The notes file ([`CircuitGeometry::prover_config_notes`]) written next to
/// [`prover_config_file_name`] for the modes that have notes.
pub fn prover_config_notes_file_name(level: SecurityLevel, mode: SoundnessMode) -> String {
    format!(
        "generated/prover_config_{}_{}.md",
        level.dir_suffix(),
        mode.file_suffix()
    )
}

/// Serialize the circuit's prover config for every security level and every
/// [`SoundnessMode`] next to the layout ([`prover_config_file_name`], the
/// notes as [`prover_config_notes_file_name`]), built from the compiled
/// circuit (the committed column widths) and checked against the WHIR message
/// size (`validate_for_whir_message_size`).
pub fn save_prover_configs(
    compiled_circuit: &cs::gkr_compiler::GKRCircuitArtifact<BabyBearField>,
    geometry: &CircuitGeometry,
) {
    save_prover_configs_in(std::path::Path::new("."), compiled_circuit, geometry);
}

/// [`save_prover_configs`] with the circuit crate root at `crate_root`.
pub fn save_prover_configs_in(
    crate_root: &std::path::Path,
    compiled_circuit: &cs::gkr_compiler::GKRCircuitArtifact<BabyBearField>,
    geometry: &CircuitGeometry,
) {
    for &level in SecurityLevel::ALL {
        for &mode in SoundnessMode::ALL {
            let config = geometry.prover_config(compiled_circuit, level, mode);
            assert_eq!(1usize << config.trace_len_log2, compiled_circuit.trace_len);
            config.validate_for_whir_message_size(config.whir_message_size_log2());
            let mut dst =
                std::fs::File::create(crate_root.join(prover_config_file_name(level, mode))).unwrap();
            serde_json::to_writer_pretty(&mut dst, &config).unwrap();
            let notes_path = crate_root.join(prover_config_notes_file_name(level, mode));
            match geometry.prover_config_notes(compiled_circuit, level, mode) {
                Some(notes) => std::fs::write(notes_path, notes).unwrap(),
                None => {
                    let _ = std::fs::remove_file(notes_path);
                }
            }
        }
    }
}

pub fn save_artifacts(
    compiled_circuit: cs::gkr_compiler::GKRCircuitArtifact<BabyBearField>,
    ssa: Vec<Vec<RawExpression<BabyBearField>>>,
    geometry: &CircuitGeometry,
) {
    fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
        let mut dst = std::fs::File::create(filename).unwrap();
        serde_json::to_writer_pretty(&mut dst, el).unwrap();
    }

    use std::io::Write;
    serialize_to_file(&compiled_circuit, "generated/layout.json");
    save_prover_configs(&compiled_circuit, geometry);

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
