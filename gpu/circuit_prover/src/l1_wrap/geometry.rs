use gpu_trace::witness::circuit_type::CircuitType;

use super::L1_WRAP_NTT_LOG_MAX_DOMAIN;
use crate::upstream::{
    l1_wrap_2p21, pow_bits, GKRCircuitArtifact, L1WrapSetup, ProofProfile, Proth120, ProverConfig,
    RomGeometry,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct L1WrapGeometry {
    pub circuit_type: CircuitType,
    pub trace_log: u32,
    pub rows: usize,
    pub pack_log2: u32,
    pub log_message: u32,
    pub log_base_lde: u32,
    pub log_base_values_per_leaf: u32,
    pub cap_log: u32,
    pub memory_columns: usize,
    pub witness_columns: usize,
    pub scratch_columns: usize,
    pub setup_columns: usize,
    pub packed_base_columns: usize,
    pub packed_setup_columns: usize,
    pub num_it_sets: usize,
    pub rom: RomGeometry,
    pub decoder_offset: usize,
    pub decoder_words: usize,
    pub external_pow_bits: u32,
    pub batching_pow_bits: u32,
}

impl L1WrapGeometry {
    pub fn new(
        circuit_type: CircuitType,
        config: &ProverConfig,
        circuit: &GKRCircuitArtifact<Proth120>,
        setup: &L1WrapSetup,
    ) -> Self {
        assert!(
            circuit_type.is_l1_wrap(),
            "L1WrapGeometry requires an L1 wrap circuit type, got {circuit_type:?}"
        );
        let trace_log = circuit_type.get_domain_size_log2();
        let rows = circuit_type.get_domain_size();
        assert_eq!(
            circuit.trace_len, rows,
            "{circuit_type:?} requires a 2^{trace_log}-row artifact"
        );
        assert_eq!(
            config.trace_len_log2, trace_log as usize,
            "{circuit_type:?} requires a 2^{trace_log} prover config"
        );
        let expected =
            ProofProfile::L1Wrap.prover_config(trace_log as usize, config.security_level);
        assert!(
            config.commitment_mode == expected.commitment_mode
                && config.pack_log2 == expected.pack_log2
                && config.pack_log2 > 0
                && config.lde_factor == expected.lde_factor
                && config.cap_size == expected.cap_size
                && config.base_oracles_values_per_leaf == expected.base_oracles_values_per_leaf
                && config.sumcheck_explicit_output_size_log_2
                    == expected.sumcheck_explicit_output_size_log_2
                && config.whir_schedule == expected.whir_schedule
                && config.whir_schedule.base_lde_factor == config.lde_factor
                && config.whir_schedule.cap_size == config.cap_size,
            "{circuit_type:?} requires the ProofProfile::L1Wrap prover config"
        );
        assert!(
            config.lde_factor.is_power_of_two()
                && config.cap_size.is_power_of_two()
                && config.base_oracles_values_per_leaf.is_power_of_two(),
            "{circuit_type:?} requires power-of-two LDE, cap and leaf widths"
        );
        let pack_log2 = u32::try_from(config.pack_log2).expect("L1Wrap pack_log2 exceeds u32");
        let external_pow_bits = match circuit_type {
            CircuitType::L1Wrap21 => l1_wrap_2p21::EXTERNAL_CHALLENGES_POW_BITS,
            _ => unreachable!(),
        };
        let log_message = u32::try_from(config.whir_message_size_log2())
            .expect("L1Wrap message size exceeds u32");
        let log_base_lde = config.lde_factor.trailing_zeros();
        assert!(
            log_message + log_base_lde <= L1_WRAP_NTT_LOG_MAX_DOMAIN,
            "{circuit_type:?} base codeword 2^{} exceeds the Proth120 NTT domain 2^{L1_WRAP_NTT_LOG_MAX_DOMAIN}",
            log_message + log_base_lde
        );
        let rom = circuit_type.rom();
        assert_eq!(
            setup.trace_len, rows,
            "{circuit_type:?} setup trace length mismatch"
        );
        assert_eq!(setup.rom, rom, "{circuit_type:?} setup ROM mismatch");
        assert_eq!(
            setup.decoder_table.len(),
            rom.word_size(),
            "{circuit_type:?} decoder table must cover the ROM"
        );
        let packed = |columns: usize| columns.div_ceil(1 << pack_log2);
        let geometry = Self {
            circuit_type,
            trace_log,
            rows,
            pack_log2,
            log_message,
            log_base_lde,
            log_base_values_per_leaf: config.base_oracles_values_per_leaf.trailing_zeros(),
            cap_log: config.cap_size.trailing_zeros(),
            memory_columns: circuit.memory_layout.total_width,
            witness_columns: circuit.witness_layout.total_width,
            scratch_columns: circuit.scratch_space_size,
            setup_columns: circuit.generic_lookup_tables_width,
            packed_base_columns: packed(
                circuit.memory_layout.total_width + circuit.witness_layout.total_width,
            ),
            packed_setup_columns: packed(circuit.generic_lookup_tables_width),
            num_it_sets: circuit_type.get_num_inits_and_teardowns_sets(),
            rom,
            decoder_offset: circuit.offset_for_decoder_table,
            decoder_words: rom.word_size(),
            external_pow_bits,
            batching_pow_bits: l1_wrap_batching_pow_bits(config, circuit),
        };
        geometry.assert_artifact(circuit);
        geometry
    }

    pub fn assert_artifact(&self, circuit: &GKRCircuitArtifact<Proth120>) {
        let circuit_type = self.circuit_type;
        assert!(
            circuit.trace_len == self.rows
                && circuit.memory_layout.total_width == self.memory_columns
                && circuit.witness_layout.total_width == self.witness_columns
                && circuit.scratch_space_size == self.scratch_columns
                && circuit.generic_lookup_tables_width == self.setup_columns
                && circuit.offset_for_decoder_table == self.decoder_offset,
            "{circuit_type:?} artifact disagrees with its geometry"
        );
        assert!(
            circuit.has_decoder_lookup,
            "{circuit_type:?} requires a decoder lookup"
        );
        assert_eq!(
            circuit.offset_for_decoder_table + self.decoder_words,
            circuit.total_tables_size,
            "{circuit_type:?} decoder table must be the last lookup table"
        );
        assert_eq!(
            circuit.memory_layout.teardown_sets.len(),
            self.num_it_sets,
            "{circuit_type:?} inits-and-teardowns set count mismatch"
        );
        let layout = &circuit.witness_layout;
        assert!(
            layout.multiplicities_columns_for_range_check_16.end
                == layout
                    .multiplicities_columns_for_timestamp_range_check
                    .start
                && layout.multiplicities_columns_for_timestamp_range_check.end
                    == layout.multiplicities_columns_for_generic_lookup.start
                && layout.multiplicities_columns_for_generic_lookup.end
                    - layout.multiplicities_columns_for_range_check_16.start
                    == 3,
            "{circuit_type:?} requires three contiguous multiplicity columns"
        );
    }
}

pub fn l1_wrap_batching_pow_bits(
    config: &ProverConfig,
    circuit: &GKRCircuitArtifact<Proth120>,
) -> u32 {
    pow_bits::batched_proximity_check_pow_bits::<Proth120, Proth120>(
        config.security_level.security_bits(),
        config.whir_message_size_log2(),
        config.whir_schedule.base_lde_factor.trailing_zeros() as usize,
        pow_bits::committed_base_oracle_columns(
            circuit,
            config.pack_log2,
            config.merged_memory_and_witness(),
        ),
    )
}

#[cfg(test)]
pub(crate) mod cpu_tests {
    use super::*;
    use crate::upstream::SecurityLevel;
    use common_constants::rom::{L1_WRAP_ROM, REGULAR_ROM};
    use gpu_gkr::proth120::programs::GkrProgramsPr;
    use gpu_gkr::proth120::proof_layout::ProofLayoutPr;
    use gpu_whir::proth120::{L1WhirShape, L1_WHIR_TILE_BYTES};
    use std::panic::{catch_unwind, AssertUnwindSafe};

    pub(crate) fn committed_layout(circuit_type: CircuitType) -> GKRCircuitArtifact<Proth120> {
        let json = match circuit_type {
            CircuitType::L1Wrap21 => include_str!(
                "../../../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120_2p21.json"
            ),
            other => panic!("{other:?} has no committed Proth120 layout"),
        };
        serde_json::from_str(json).expect("committed Proth120 layout")
    }

    pub(crate) fn setup_without_evaluations(
        circuit_type: CircuitType,
        circuit: GKRCircuitArtifact<Proth120>,
    ) -> L1WrapSetup {
        let rom = circuit_type.rom();
        L1WrapSetup {
            circuit,
            table_driver: cs::tables::TableDriver::new(),
            decoder_table: vec![None; rom.word_size()],
            setup: prover::gkr::prover::setup::GKRSetup {
                hypercube_evals: Vec::new(),
            },
            trace_len: circuit_type.get_domain_size(),
            rom,
        }
    }

    pub(crate) fn wrap_geometry(circuit_type: CircuitType) -> (L1WrapGeometry, ProverConfig) {
        let circuit = committed_layout(circuit_type);
        let config =
            crate::config::prover_config(circuit_type, ProofProfile::L1Wrap, SecurityLevel::Sec100)
                .unwrap();
        let setup = setup_without_evaluations(circuit_type, circuit.clone());
        (
            L1WrapGeometry::new(circuit_type, &config, &circuit, &setup),
            config,
        )
    }

    fn assert_panics(f: impl FnOnce(), expected: &str) {
        let payload = catch_unwind(AssertUnwindSafe(f)).expect_err("expected a named panic");
        let message = payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| payload.downcast_ref::<&str>().map(|m| m.to_string()))
            .expect("panic payload is a message");
        assert!(
            message.contains(expected),
            "panic {message:?} does not name {expected:?}"
        );
    }

    #[test]
    fn cpu_l1_wrap_geometry_pins_active_wrap() {
        let (geometry, config) = wrap_geometry(CircuitType::L1Wrap21);
        assert_eq!(
            geometry,
            L1WrapGeometry {
                circuit_type: CircuitType::L1Wrap21,
                trace_log: 21,
                rows: 1 << 21,
                pack_log2: 3,
                log_message: 24,
                log_base_lde: 7,
                log_base_values_per_leaf: 1,
                cap_log: 3,
                memory_columns: 38,
                witness_columns: 58,
                scratch_columns: 41,
                setup_columns: 10,
                packed_base_columns: 12,
                packed_setup_columns: 2,
                num_it_sets: 2,
                rom: L1_WRAP_ROM,
                decoder_offset: 1_180_033,
                decoder_words: 1 << 17,
                external_pow_bits: 20,
                batching_pow_bits: 13,
            }
        );
        assert!(geometry.log_message <= 26 && geometry.pack_log2 <= 4);
        let shape = L1WhirShape::from_schedule(
            &config.whir_schedule,
            geometry.log_message,
            geometry.log_base_lde,
            geometry.log_base_values_per_leaf,
            L1_WHIR_TILE_BYTES,
        );
        let rounds = |f: fn(&gpu_whir::proth120::RoundShape) -> usize| {
            shape.rounds.iter().map(f).collect::<Vec<_>>()
        };
        assert_eq!(rounds(|r| r.folds as usize), [1, 4, 4, 4, 4]);
        assert_eq!(rounds(|r| r.queries), [12, 11, 7, 6, 5]);
        assert_eq!(rounds(|r| r.pow_bits as usize), [30, 27, 30, 20, 17]);
        let oracles = shape
            .rounds
            .iter()
            .filter_map(|r| r.oracle)
            .map(|o| (o.log_n, o.log_lde, o.log_v, o.log_domain, o.skip_bottom))
            .collect::<Vec<_>>();
        assert_eq!(
            oracles,
            [
                (23, 8, 4, 31, 5),
                (19, 12, 4, 31, 5),
                (15, 16, 4, 31, 5),
                (11, 20, 4, 31, 5),
            ]
        );
        assert_eq!(shape.term_capacity, 36);
        assert_eq!(shape.total_sumcheck_polys, 17);
        assert_eq!(shape.log_final, 7);
        assert_eq!(shape.cap_log, geometry.cap_log);
        let circuit = std::sync::Arc::new(committed_layout(CircuitType::L1Wrap21));
        assert_eq!(circuit.layers.len(), 5);
        let programs = GkrProgramsPr::compile(CircuitType::L1Wrap21, circuit).unwrap();
        let layout = ProofLayoutPr::new(&programs, &config);
        assert_eq!(
            layout.backward_layers.len(),
            programs.runtime_circuit.layers.len() + config.trace_len_log2
                - config.sumcheck_explicit_output_size_log_2
        );
        assert_eq!(
            layout.memory_claims.len(),
            geometry.packed_base_columns * 16
        );
        assert_eq!(
            layout.setup_claims.len(),
            geometry.packed_setup_columns * 16
        );
        assert_eq!(
            layout.evaluation_point.len(),
            config.whir_message_size_log2() * 16
        );
    }

    #[test]
    fn cpu_l1_wrap_geometry_rejects_mismatch() {
        let wrap21 = CircuitType::L1Wrap21;
        let circuit = committed_layout(wrap21);
        let config =
            crate::config::prover_config(wrap21, ProofProfile::L1Wrap, SecurityLevel::Sec100)
                .unwrap();
        let setup = setup_without_evaluations(wrap21, circuit.clone());
        let unified =
            CircuitType::Unrolled(gpu_trace::witness::circuit_type::UnrolledCircuitType::Unified);
        assert_panics(
            || {
                L1WrapGeometry::new(unified, &config, &circuit, &setup);
            },
            "L1WrapGeometry requires an L1 wrap circuit type, got Unrolled(Unified)",
        );
        let mut long_circuit = circuit.clone();
        long_circuit.trace_len = 1 << 22;
        assert_panics(
            || {
                L1WrapGeometry::new(wrap21, &config, &long_circuit, &setup);
            },
            "L1Wrap21 requires a 2^21-row artifact",
        );
        let mut long_config = config.clone();
        long_config.trace_len_log2 = 22;
        assert_panics(
            || {
                L1WrapGeometry::new(wrap21, &long_config, &circuit, &setup);
            },
            "L1Wrap21 requires a 2^21 prover config",
        );
        let mut unpacked = config.clone();
        unpacked.pack_log2 = 0;
        assert_panics(
            || {
                L1WrapGeometry::new(wrap21, &unpacked, &circuit, &setup);
            },
            "L1Wrap21 requires the ProofProfile::L1Wrap prover config",
        );
        let mut regular_rom = setup_without_evaluations(wrap21, circuit.clone());
        regular_rom.rom = REGULAR_ROM;
        assert_panics(
            || {
                L1WrapGeometry::new(wrap21, &config, &circuit, &regular_rom);
            },
            "L1Wrap21 setup ROM mismatch",
        );
        let mut short_decoder = setup_without_evaluations(wrap21, circuit.clone());
        short_decoder.decoder_table.pop();
        assert_panics(
            || {
                L1WrapGeometry::new(wrap21, &config, &circuit, &short_decoder);
            },
            "L1Wrap21 decoder table must cover the ROM",
        );
        let mut wrong_rows = setup_without_evaluations(wrap21, circuit.clone());
        wrong_rows.trace_len = 1 << 22;
        assert_panics(
            || {
                L1WrapGeometry::new(wrap21, &config, &circuit, &wrong_rows);
            },
            "L1Wrap21 setup trace length mismatch",
        );
        let geometry = L1WrapGeometry::new(wrap21, &config, &circuit, &setup);
        let mut wide = circuit.clone();
        wide.scratch_space_size += 1;
        assert_panics(
            || geometry.assert_artifact(&wide),
            "L1Wrap21 artifact disagrees with its geometry",
        );
        let mut split = circuit.clone();
        split
            .witness_layout
            .multiplicities_columns_for_generic_lookup
            .end += 1;
        assert_panics(
            || geometry.assert_artifact(&split),
            "L1Wrap21 requires three contiguous multiplicity columns",
        );
    }
}
