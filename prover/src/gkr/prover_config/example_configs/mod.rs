//! Default prover configurations.
//!
//! A circuit's proving geometry is decided in three steps:
//!
//! 1. its base-commitment [`BasePacking`] (physical packing by
//!    `2^physical_packing_log2` columns, and/or virtual packing = one value per
//!    column per base leaf, see [`WhirBaseRoundSchedule`]) and its committed
//!    column widths ([`BaseColumns`]) determine WHAT ENTERS WHIR: the
//!    [`WhirInput`] — the committed polynomial size and count after all
//!    packing;
//! 2. [`whir_schedule`] maps a [`SoundnessMode`] and a [`WhirInput`] to the
//!    [`WhirSchedule`] pre-computed for that shape (a finite table per mode;
//!    it PANICS for a shape nobody has computed a schedule for);
//! 3. [`prover_config`] wraps the schedule into the full [`ProverConfig`]
//!    (the GKR-side schedules only depend on the trace length).
//!
//! Two soundness accountings exist, see [`SoundnessMode`]. The
//! [`PessimisticConjecture`](SoundnessMode::PessimisticConjecture) ladders
//! are the configs proved and verified in production today; the
//! [`EthproofsSoundnessCalc`](SoundnessMode::EthproofsSoundnessCalc) ones are
//! certified by `ethereum/soundcalc` (see [`ethproofs_soundcalc`] and the
//! `soundcalc/` driver scripts next to this file).

use crate::definitions::*;
use cs::gkr_compiler::GKRCircuitArtifact;
use field::PrimeField;

use super::pow_bits::physically_committed_polys;
use super::*;

pub mod ethproofs_soundcalc;
mod pessimistic_conjecture;
mod special_configs;

pub use ethproofs_soundcalc::{
    EthproofsInternalRound, EthproofsSoundcalcEntry, ProximityRegime, RoundAnalysis,
};
pub use pessimistic_conjecture::*;
pub use special_configs::*;

pub use crate::definitions::SoundnessMode;

/// A requested circuit shape has no certified configuration. No schedule is interpolated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConfigSelectionError {
    MissingSchedule {
        mode: SoundnessMode,
        level: SecurityLevel,
        input: WhirInput,
    },
    MissingColumnCount,
    CommittedPolynomialCeiling {
        actual: usize,
        ceiling: usize,
    },
    TraceLengthMismatch {
        declared: usize,
        compiled: usize,
    },
}

impl core::fmt::Display for ConfigSelectionError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::MissingSchedule { mode, level, input } => write!(
                f, "no {mode:?} WHIR schedule for {level:?}, input {input:?}"
            ),
            Self::MissingColumnCount => write!(
                f, "the EthproofsSoundnessCalc schedule is certified for a committed-polynomial ceiling: provide the compiled circuit's column count"
            ),
            Self::CommittedPolynomialCeiling { actual, ceiling } => write!(
                f, "{actual} committed polynomials exceed the {ceiling} ceiling certified for EthproofsSoundnessCalc"
            ),
            Self::TraceLengthMismatch { declared, compiled } => write!(
                f, "declared trace length {declared} differs from compiled trace length {compiled}"
            ),
        }
    }
}

impl std::error::Error for ConfigSelectionError {}

/// How a circuit's base columns are committed. Physical and virtual packing
/// are independent: physical packing commits `2^physical_packing_log2`
/// consecutive columns as ONE `(trace_len_log2 + physical_packing_log2)`-variate
/// polynomial (fewer, larger committed polynomials); virtual packing opens
/// every committed polynomial with ONE value per base leaf and no round-0
/// sumcheck (`fold_log2 = 0`, the batched polynomial is re-committed as
/// intermediate oracle 0), see [`WhirBaseRoundSchedule`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BasePacking {
    pub physical_packing_log2: usize,
    pub virtual_packing: bool,
}

impl BasePacking {
    /// Unpacked, two values per column per base leaf (round-0 fold of 1).
    pub const NONE: Self = Self {
        physical_packing_log2: 0,
        virtual_packing: false,
    };
    /// Unpacked columns opened one value per leaf.
    pub const VIRTUAL: Self = Self {
        physical_packing_log2: 0,
        virtual_packing: true,
    };

    pub const fn physical(physical_packing_log2: usize) -> Self {
        Self {
            physical_packing_log2,
            virtual_packing: false,
        }
    }

    pub const fn physical_and_virtual(physical_packing_log2: usize) -> Self {
        Self {
            physical_packing_log2,
            virtual_packing: true,
        }
    }

    /// Round-0 sumcheck steps: `0` under virtual packing, `1` (two values per
    /// column per leaf) otherwise.
    pub const fn fold_log2(&self) -> usize {
        if self.virtual_packing {
            0
        } else {
            1
        }
    }

    /// log2 of the committed polynomial size for a `2^trace_len_log2` trace.
    pub const fn message_size_log2(&self, trace_len_log2: usize) -> usize {
        trace_len_log2 + self.physical_packing_log2
    }
}

/// Widths of a circuit's three committed base column sets.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BaseColumns {
    pub memory: usize,
    pub witness: usize,
    /// Committed (non-virtual) setup columns: the generic lookup tables.
    pub setup: usize,
}

impl BaseColumns {
    pub fn of<F: PrimeField>(compiled_circuit: &GKRCircuitArtifact<F>) -> Self {
        Self {
            memory: compiled_circuit.memory_layout.total_width,
            witness: compiled_circuit.witness_layout.total_width,
            setup: compiled_circuit.generic_lookup_tables_width,
        }
    }

    pub const fn total(&self) -> usize {
        self.memory + self.witness + self.setup
    }

    /// The number of PHYSICALLY committed polynomials after packing every set
    /// by `2^physical_packing_log2` (see
    /// [`physically_committed_polys`](super::pow_bits::physically_committed_polys)):
    /// the count the WHIR batching challenge combines.
    pub const fn committed_polys(
        &self,
        physical_packing_log2: usize,
        merged_memory_and_witness: bool,
    ) -> usize {
        if merged_memory_and_witness {
            physically_committed_polys(
                self.memory + self.witness,
                0,
                self.setup,
                physical_packing_log2,
            )
        } else {
            physically_committed_polys(self.memory, self.witness, self.setup, physical_packing_log2)
        }
    }
}

/// What enters WHIR after all packing: `num_committed_polys` committed
/// polynomials of `2^message_size_log2` evaluations, opened with a round-0
/// fold of [`Self::fold_log2`]. The key of [`whir_schedule`].
///
/// The committed-polynomial count comes from the compiled circuit artifact
/// ([`BaseColumns::of`]) — never from a declared constant — or is unknown
/// (`None`, [`Self::without_column_count`]): a mode whose schedule depends on
/// the count ([`SoundnessMode::EthproofsSoundnessCalc`], certified for a
/// ceiling) rejects an unknown count.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct WhirInput {
    /// log2 of the committed polynomial size (`trace_len_log2 +
    /// physical_packing_log2`).
    pub message_size_log2: usize,
    pub physical_packing_log2: usize,
    pub virtual_packing: bool,
    /// Physically committed polynomials across all base oracles, when known.
    pub num_committed_polys: Option<usize>,
}

impl WhirInput {
    /// The input of a `2^trace_len_log2` trace of `columns` (from the
    /// compiled circuit) committed under `packing` / `commitment_mode`.
    pub fn new(
        trace_len_log2: usize,
        packing: BasePacking,
        columns: &BaseColumns,
        commitment_mode: CommitmentMode,
    ) -> Self {
        Self {
            num_committed_polys: Some(columns.committed_polys(
                packing.physical_packing_log2,
                matches!(commitment_mode, CommitmentMode::MergedMemoryAndWitness),
            )),
            ..Self::without_column_count(trace_len_log2, packing)
        }
    }

    /// The input of a `2^trace_len_log2` trace committed under `packing` with
    /// an UNKNOWN committed-polynomial count (no compiled circuit at hand):
    /// only usable with modes whose schedules do not depend on the count.
    pub fn without_column_count(trace_len_log2: usize, packing: BasePacking) -> Self {
        Self {
            message_size_log2: packing.message_size_log2(trace_len_log2),
            physical_packing_log2: packing.physical_packing_log2,
            virtual_packing: packing.virtual_packing,
            num_committed_polys: None,
        }
    }

    pub const fn fold_log2(&self) -> usize {
        if self.virtual_packing {
            0
        } else {
            1
        }
    }

    pub const fn packing(&self) -> BasePacking {
        BasePacking {
            physical_packing_log2: self.physical_packing_log2,
            virtual_packing: self.virtual_packing,
        }
    }
}

/// THE schedule lookup: the WHIR schedule computed under `mode` at `level` for
/// what enters WHIR (`input`). Panics when no schedule has been computed for
/// that shape — every entry is a hand-verified table row, there is no
/// interpolation. Under [`SoundnessMode::EthproofsSoundnessCalc`] the entry
/// also carries the committed-polynomial ceiling its batching proof of work
/// was certified for, and `input.num_committed_polys` must not exceed it.
pub fn whir_schedule(mode: SoundnessMode, level: SecurityLevel, input: &WhirInput) -> WhirSchedule {
    try_whir_schedule(mode, level, input).unwrap_or_else(|error| panic!("{error}"))
}

/// Fallible schedule lookup, including the Ethproofs committed-polynomial ceiling.
pub fn try_whir_schedule(
    mode: SoundnessMode,
    level: SecurityLevel,
    input: &WhirInput,
) -> Result<WhirSchedule, ConfigSelectionError> {
    match mode {
        SoundnessMode::PessimisticConjecture => {
            pessimistic_conjecture::try_whir_schedule(level, input)
        }
        SoundnessMode::EthproofsSoundnessCalc => {
            Ok(ethproofs_soundcalc::try_entry(level, input)?.schedule(input.physical_packing_log2))
        }
    }
}

/// Human-readable notes on the non-obvious parameters of the schedule
/// [`whir_schedule`] returns for the same arguments (the proximity regime and
/// its slack per WHIR stage, why it was chosen, the certified bits), serialized
/// next to the config files by the circuit artifact generators. `None` for a
/// mode without such notes.
pub fn whir_schedule_notes(
    mode: SoundnessMode,
    level: SecurityLevel,
    input: &WhirInput,
) -> Option<String> {
    match mode {
        SoundnessMode::PessimisticConjecture => None,
        SoundnessMode::EthproofsSoundnessCalc => {
            Some(ethproofs_soundcalc::entry(level, input).render_notes(level, input))
        }
    }
}

/// The full prover config of a circuit with a `2^trace_len_log2` trace, base
/// commitment `packing` of `columns` (from the compiled circuit, or `None`
/// when no compiled circuit is at hand — see [`WhirInput::without_column_count`])
/// committed as separate memory and witness oracles, under `mode` at `level`:
/// the standard GKR side (windowed same-size sumchecks, default cap and
/// explicit-output size) and the [`whir_schedule`] of what enters WHIR.
pub fn prover_config(
    mode: SoundnessMode,
    level: SecurityLevel,
    trace_len_log2: usize,
    packing: BasePacking,
    columns: Option<&BaseColumns>,
) -> ProverConfig {
    try_prover_config(mode, level, trace_len_log2, packing, columns)
        .unwrap_or_else(|error| panic!("{error}"))
}

/// Resolve an existing certified config without substituting another mode or shape.
pub fn try_prover_config(
    mode: SoundnessMode,
    level: SecurityLevel,
    trace_len_log2: usize,
    packing: BasePacking,
    columns: Option<&BaseColumns>,
) -> Result<ProverConfig, ConfigSelectionError> {
    let input = match columns {
        Some(columns) => WhirInput::new(
            trace_len_log2,
            packing,
            columns,
            CommitmentMode::SeparateMemoryAndWitness,
        ),
        None => WhirInput::without_column_count(trace_len_log2, packing),
    };
    Ok(standard_config(
        trace_len_log2,
        level,
        try_whir_schedule(mode, level, &input)?,
    ))
}

/// The standard config shape around a WHIR schedule: separate memory and
/// witness commitments, windowed same-size sumchecks for the trace length,
/// default cap and explicit-output sizes.
pub fn standard_config(
    trace_len_log2: usize,
    level: SecurityLevel,
    whir_schedule: WhirSchedule,
) -> ProverConfig {
    let config = ProverConfig {
        trace_len_log2,
        commitment_mode: CommitmentMode::SeparateMemoryAndWitness,
        same_size_sumcheck_schedule: windowed_same_size_schedule(trace_len_log2),
        dimension_reducing_sumcheck_schedule: Default::default(),
        cap_size: whir_schedule.cap_size,
        sumcheck_explicit_output_size_log_2: DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
        security_level: level,
        whir_schedule,
    };
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    config
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ethproofs_column_ceiling_is_fallible() {
        let mode = SoundnessMode::EthproofsSoundnessCalc;
        let input = WhirInput {
            message_size_log2: 23,
            physical_packing_log2: 0,
            virtual_packing: false,
            num_committed_polys: Some(129),
        };
        assert_eq!(
            try_whir_schedule(mode, SecurityLevel::Sec100, &input),
            Err(ConfigSelectionError::CommittedPolynomialCeiling {
                actual: 129,
                ceiling: 128
            })
        );
        assert_eq!(
            try_whir_schedule(
                mode,
                SecurityLevel::Sec100,
                &WhirInput {
                    num_committed_polys: None,
                    ..input
                }
            ),
            Err(ConfigSelectionError::MissingColumnCount)
        );
    }

    #[test]
    fn absent_schedules_are_fallible_in_both_modes() {
        let input = WhirInput::without_column_count(19, BasePacking::NONE);
        for &mode in SoundnessMode::ALL {
            assert_eq!(
                try_whir_schedule(mode, SecurityLevel::Sec100, &input),
                Err(ConfigSelectionError::MissingSchedule {
                    mode,
                    level: SecurityLevel::Sec100,
                    input
                })
            );
        }
    }

    #[test]
    fn base_columns_count_packed_polys() {
        // blake2_with_compression: 225 + 538 + 6 columns
        let columns = BaseColumns {
            memory: 225,
            witness: 538,
            setup: 6,
        };
        assert_eq!(columns.total(), 769);
        assert_eq!(columns.committed_polys(0, false), 769);
        assert_eq!(columns.committed_polys(2, false), 57 + 135 + 2);
        assert_eq!(columns.committed_polys(4, false), 15 + 34 + 1);
        assert_eq!(columns.committed_polys(4, true), 48 + 1);
    }

    #[test]
    fn whir_input_derives_the_committed_shape() {
        let columns = BaseColumns {
            memory: 225,
            witness: 538,
            setup: 6,
        };
        let input = WhirInput::new(
            20,
            BasePacking::physical_and_virtual(2),
            &columns,
            CommitmentMode::SeparateMemoryAndWitness,
        );
        assert_eq!(input.message_size_log2, 22);
        assert_eq!(input.fold_log2(), 0);
        assert_eq!(input.num_committed_polys, Some(194));
        assert_eq!(
            WhirInput::without_column_count(20, BasePacking::physical_and_virtual(2)),
            WhirInput {
                num_committed_polys: None,
                ..input
            }
        );
        assert_eq!(input.packing(), BasePacking::physical_and_virtual(2));
        assert_eq!(BasePacking::NONE.fold_log2(), 1);
        assert_eq!(BasePacking::VIRTUAL.fold_log2(), 0);
    }

    #[test]
    fn both_modes_build_every_production_shape() {
        // (trace, packing, widest production circuit of the shape)
        let shapes = [
            (
                24,
                BasePacking::NONE,
                BaseColumns {
                    memory: 30,
                    witness: 28,
                    setup: 10,
                },
            ), // shift_binary
            (
                23,
                BasePacking::NONE,
                BaseColumns {
                    memory: 38,
                    witness: 58,
                    setup: 10,
                },
            ), // unified
            (
                22,
                BasePacking::VIRTUAL,
                BaseColumns {
                    memory: 91,
                    witness: 175,
                    setup: 8,
                },
            ), // keccak_special5
            (
                20,
                BasePacking::physical_and_virtual(2),
                BaseColumns {
                    memory: 225,
                    witness: 538,
                    setup: 6,
                },
            ), // blake2_with_compression
        ];
        for mode in SoundnessMode::ALL {
            for (trace_len_log2, packing, columns) in shapes {
                let config = prover_config(
                    *mode,
                    SecurityLevel::Sec100,
                    trace_len_log2,
                    packing,
                    Some(&columns),
                );
                assert_eq!(config.trace_len_log2, trace_len_log2);
                assert_eq!(config.pack_log2(), packing.physical_packing_log2);
                assert_eq!(config.is_virtual_packing(), packing.virtual_packing);
                assert_eq!(
                    config.whir_schedule.base_round.fold_log2,
                    packing.fold_log2()
                );
            }
        }
    }

    #[test]
    #[should_panic(expected = "committed-polynomial ceiling")]
    fn the_soundcalc_mode_needs_the_column_count() {
        prover_config(
            SoundnessMode::EthproofsSoundnessCalc,
            SecurityLevel::Sec100,
            23,
            BasePacking::NONE,
            None,
        );
    }

    #[test]
    fn the_pessimistic_mode_does_not_need_the_column_count() {
        let config = prover_config(
            SoundnessMode::PessimisticConjecture,
            SecurityLevel::Sec100,
            23,
            BasePacking::NONE,
            None,
        );
        assert_eq!(config.whir_schedule.base_round.batching_pow_bits, None);
    }

    #[test]
    fn file_suffixes_are_distinct() {
        assert_eq!(SoundnessMode::ALL.len(), 2);
        assert_ne!(
            SoundnessMode::ALL[0].file_suffix(),
            SoundnessMode::ALL[1].file_suffix()
        );
        assert_eq!(SoundnessMode::DEFAULT, SoundnessMode::PessimisticConjecture);
    }
}
