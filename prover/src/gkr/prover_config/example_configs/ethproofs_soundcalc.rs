//! The [`SoundnessMode::EthproofsSoundnessCalc`] schedules: WHIR schedules
//! certified at the security level by `ethereum/soundcalc` (commit `2af5e7d`,
//! 2026-09-21), the calculator the ethproofs listing uses.
//!
//! What soundcalc models and how it was run (`soundcalc/README.md` next to
//! this file has the reproduction recipe, `soundcalc/whir_schedule_search.py`
//! is the search that produced every entry):
//!
//! * only its WHIR PCS module (`soundcalc/pcs/whir.py`: WHIR Theorem 5.2 with
//!   the BCHKS25 proximity-gap bounds);
//! * BabyBear⁴ challenges with maximum point mass `81/2^128`, 256-bit hashes, powers
//!   batching of the committed polynomials, constraint degree 3 (soundcalc's
//!   minimum; ours is 2, so ~0.6 bit conservative);
//! * our explicit per-oracle LDE factors are written over soundcalc's
//!   "domain halves every iteration" default;
//! * the proximity regime is chosen PER WHIR ITERATION (the theorem carries a
//!   separate proximity parameter `δ_i` and list size `ℓ_i` per iteration):
//!   [`ProximityRegime::UniqueDecoding`] for a base round at rate 1/2 — there
//!   the Johnson-bound powers-batching term for the committed columns does not
//!   reach the target with the selected batching PoW; its query term alone
//!   does not establish the base round's bound —
//!   and [`ProximityRegime::JohnsonBound`] with an explicit multiplicity `m`
//!   for a base round at a lower rate, whose batching grind lifts that term to
//!   the target, and for every later oracle, where a query is worth more than
//!   under unique decoding;
//! * the price of the Johnson rounds is a proof of work before every
//!   folding challenge (their fold term starts 18–24 bits short) and before
//!   the single OOD sample of every oracle (the user-chosen alternative to a
//!   second sample), capped per shape; the late oracles' LDE factors stay low
//!   so that their domains keep that fold grind within the cap (the fold term
//!   grows with `n / ρ^1.5`);
//! * every grind is the SMALLEST that lifts its term to the target: the
//!   per-round query count is sized against the shape's query-PoW cap, then the
//!   query PoW is lowered to what the chosen count actually leaves short
//!   (e.g. 12 queries at 6.28 bits each are 75 bits, so 25 bits of grind, not
//!   the cap); the folding and OOD grinds are computed the same way;
//! * virtual packing (`fold_log2 = 0`) is emulated as a message one bit
//!   larger with a round-0 fold of 1 (soundcalc needs `k_0 ≥ 1`); the
//!   re-committed oracle 0 is then exactly our batched polynomial. The certificate
//!   omits the artificial base fold and recomputes batching on the real base code.
//!
//! A base round at rate 1/2 uses unique decoding. Its query contribution is
//! `−log2(1 − 1/4) ≈ 0.415` bits per query, so a base at `p` PoW bits needs
//! `ceil((100 − p) / 0.415)` queries for its 100-bit query term. These are WHIR
//! PCS component bounds, not whole-system or GKR soundness claims.
//!
//! The production shapes are tuned for proving time rather than for the fewest
//! queries (a lower grind cap and a cheaper oracle-0 commit for more queries).
//! They were certified with the same pinned soundcalc WHIR module.
//!
//! Each [`EthproofsSoundcalcEntry`] is certified for a CEILING on the number
//! of physically committed polynomials (it only enters the batching PoW:
//! under a unique-decoding base round computed for the ceiling with
//! [`pow_bits_for_batched_proximity`] and the certified challenge entropy; under a
//! Johnson-bound base round the grind the search certified at the ceiling); a
//! circuit with more committed
//! polynomials than the ceiling has no schedule and the lookup panics.
//! Several Johnson-bound terms of every entry sit at exactly 100 bits, so a
//! changed domain, fold or ceiling needs a re-run of the search.
//!
//! Our [`WhirInternalRound::folding_pow_bits`] is one value for EVERY
//! folding-challenge draw of an oracle, while the analysis needs one bit less
//! per sumcheck step (the folded code halves); the entries record the
//! per-step schedule and use its maximum, i.e. they grind slightly more than
//! the certification needs.

use field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};

use transcript::{Blake2sTranscript, Transcript};

use super::super::pow_bits::{ceil_log2, pow_bits_for_batched_proximity};
use super::*;

/// The proximity-gap regime an oracle's terms are evaluated under.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ProximityRegime {
    /// `δ = (1 − ρ) / 2`, list size 1, correlated-agreement error
    /// `(γ·n + 1) / |F|` (BCIKS20 style): grind-free but at most one bit per
    /// query.
    UniqueDecoding,
    /// `δ = 1 − √ρ − η` with the slack `η = √ρ / (2m)` below the Johnson
    /// radius, list size `(m + 1/2) / √ρ`, correlated-agreement error
    /// `≈ 2(m + 1/2)^5 · n / (3 ρ^1.5 |F|)` (BCHKS25 Theorem 4.2). `m = 3` is
    /// the theorem's floor; soundcalc's default heuristic would pick `m = 50`
    /// at our rates, which is far worse (the fold term grows as `(m + 1/2)^5`).
    JohnsonBound { m: u32 },
}

impl ProximityRegime {
    pub fn describe(&self, rate_log2: usize) -> String {
        match self {
            ProximityRegime::UniqueDecoding => {
                let rho = 2f64.powi(-(rate_log2 as i32));
                format!(
                    "unique decoding (δ = (1 − ρ)/2 = {:.3}, list size 1)",
                    (1.0 - rho) / 2.0
                )
            }
            ProximityRegime::JohnsonBound { m } => {
                let sqrt_rho = 2f64.powi(-(rate_log2 as i32)).sqrt();
                let eta = sqrt_rho / (2.0 * *m as f64);
                format!(
                    "Johnson bound, m = {m} (η = √ρ/(2m) = {eta:.4}, δ = 1 − √ρ − η = {:.3}, list size {:.1})",
                    1.0 - sqrt_rho - eta,
                    (*m as f64 + 0.5) / sqrt_rho
                )
            }
        }
    }
}

/// The soundcalc analysis of one oracle's round.
#[derive(Clone, Copy, Debug)]
pub struct RoundAnalysis {
    pub regime: ProximityRegime,
    /// Bits of security one query contributes under `regime` at the oracle's
    /// rate (`−log2(1 − δ)`).
    pub bits_per_query: f64,
    /// Queries a unique-decoding analysis of the same oracle would need at
    /// the shape's query PoW cap.
    pub unique_decoding_queries: usize,
    /// The folding-challenge PoW the analysis needs per sumcheck step of this
    /// oracle (decreasing by one bit per step); the schedule's single
    /// `folding_pow_bits` is the maximum. Empty for a round that needs no
    /// folding PoW.
    pub folding_pow_bits_per_step: &'static [u32],
    /// Why this regime / multiplicity / rate was chosen for this oracle.
    pub reason: &'static str,
}

/// One certified intermediate oracle: the schedule fields plus their analysis.
#[derive(Clone, Copy, Debug)]
pub struct EthproofsInternalRound {
    pub lde_factor_log2: usize,
    pub folding_log2: usize,
    pub num_queries: usize,
    pub queries_pow_bits: u32,
    pub ood_pow_bits: u32,
    pub analysis: RoundAnalysis,
}

impl EthproofsInternalRound {
    pub fn folding_pow_bits(&self) -> u32 {
        *self
            .analysis
            .folding_pow_bits_per_step
            .iter()
            .max()
            .expect("an internal round folds at least once")
    }

    fn to_round(self) -> WhirInternalRound {
        assert_eq!(
            self.analysis.folding_pow_bits_per_step.len(),
            self.folding_log2,
            "one folding PoW entry per sumcheck step"
        );
        WhirInternalRound {
            lde_factor_log2: self.lde_factor_log2,
            folding_log2: self.folding_log2,
            num_queries: self.num_queries,
            queries_pow_bits: self.queries_pow_bits,
            folding_pow_bits: self.folding_pow_bits(),
            num_ood_samples: 1,
            ood_pow_bits: self.ood_pow_bits,
        }
    }
}

/// One certified schedule: keyed by the committed polynomial size and the
/// base-round fold, valid up to `max_committed_polys` committed polynomials.
#[derive(Clone, Copy, Debug)]
pub struct EthproofsSoundcalcEntry {
    pub shape: &'static str,
    pub level: SecurityLevel,
    pub message_size_log2: usize,
    pub virtual_packing: bool,
    pub base_lde_factor_log2: usize,
    pub cap_size: usize,
    /// Ceiling on the physically committed polynomials (the count the
    /// batching challenge combines) this entry is certified for.
    pub max_committed_polys: usize,
    /// Bits soundcalc certifies for the WHIR PCS with this schedule.
    pub certified_bits: usize,
    /// The soundcalc term at `certified_bits`.
    pub binding_term: &'static str,
    pub base_num_queries: usize,
    pub base_queries_pow_bits: u32,
    pub base_batching_pow_bits: Option<u32>,
    pub base_analysis: RoundAnalysis,
    pub rounds: &'static [EthproofsInternalRound],
}

impl EthproofsSoundcalcEntry {
    pub const fn fold_log2(&self) -> usize {
        if self.virtual_packing {
            0
        } else {
            1
        }
    }

    /// The batching PoW the entry was certified with: the grind the search
    /// certified for a Johnson-bound base round, otherwise the standard
    /// [`pow_bits_for_batched_proximity`] at the committed-polynomial
    /// ceiling (which lands the batching term at 102 bits under unique
    /// decoding).
    pub fn batching_pow_bits(&self) -> u32 {
        self.base_batching_pow_bits.unwrap_or_else(|| {
            let sampler =
                <Blake2sTranscript as Transcript<BabyBearField, BabyBearExt4>>::CHALLENGE_POINT_MASS;
            let entropy = sampler.random_bits - ceil_log2(u128::from(sampler.max_preimages));
            pow_bits_for_batched_proximity(
                self.level.security_bits(),
                self.message_size_log2,
                self.base_lde_factor_log2,
                self.max_committed_polys,
                entropy as usize,
            ) as u32
        })
    }

    pub fn base_folding_pow_bits(&self) -> u32 {
        self.base_analysis
            .folding_pow_bits_per_step
            .iter()
            .copied()
            .max()
            .unwrap_or(0)
    }

    pub fn schedule(&self, physical_packing_log2: usize) -> WhirSchedule {
        assert_eq!(
            self.base_batching_pow_bits.is_some(),
            matches!(
                self.base_analysis.regime,
                ProximityRegime::JohnsonBound { .. }
            ),
            "a certified batching PoW belongs to a Johnson-bound base round, the formula to a unique-decoding one"
        );
        WhirSchedule {
            cap_size: self.cap_size,
            base_round: WhirBaseRoundSchedule {
                lde_factor_log2: self.base_lde_factor_log2,
                physical_packing_log2,
                fold_log2: self.fold_log2(),
                batching_pow_bits: Some(self.batching_pow_bits()),
                folding_pow_bits: self.base_folding_pow_bits(),
                num_queries: self.base_num_queries,
                queries_pow_bits: self.base_queries_pow_bits,
            },
            internal_rounds: self.rounds.iter().map(|r| r.to_round()).collect(),
        }
    }

    /// The markdown notes serialized next to a circuit's config file: the
    /// certification inputs, every round's regime / slack / grinds and why,
    /// and what the circuit itself contributes (`input`).
    pub fn render_notes(&self, level: SecurityLevel, input: &WhirInput) -> String {
        use std::fmt::Write;
        let mut out = String::new();
        let batching_pow_bits = self.batching_pow_bits();
        let base_rate_log2 = self.base_lde_factor_log2;
        let _ = writeln!(
            out,
            "# WHIR schedule notes — `EthproofsSoundnessCalc`, `{}`, {}\n",
            level.dir_suffix(),
            self.shape
        );
        let _ = writeln!(
            out,
            "Certified by `ethereum/soundcalc` (commit `2af5e7d`, 2026-09-21), WHIR PCS module only \
             (WHIR Theorem 5.2 with the BCHKS25 proximity-gap bounds): **{} bits**, binding term `{}`; \
             every other term is at or above the target and several Johnson-bound terms sit exactly on \
             it, so any change of a domain, a fold or the committed-polynomial ceiling needs a re-run of \
             `prover/src/gkr/prover_config/example_configs/soundcalc/whir_schedule_search.py`. \
             Model inputs: BabyBear⁴ challenges with effective denominator 2^128/81, 256-bit hashes, powers batching, \
             constraint degree 3 (soundcalc's minimum; ours is 2), our explicit per-oracle LDE factors, \
             one OOD sample per internal oracle.\n",
            self.certified_bits, self.binding_term
        );
        let _ = writeln!(out, "## This circuit\n");
        let _ = writeln!(
            out,
            "- committed polynomials entering WHIR: **{}** (from the compiled circuit; physical packing \
             2^{}{}), certified ceiling {} → batching PoW {} bits",
            input
                .num_committed_polys
                .expect("notes are rendered for a compiled circuit"),
            input.physical_packing_log2,
            if input.virtual_packing {
                ", virtual packing: one value per column per base leaf, no round-0 sumcheck"
            } else {
                ", two values per column per base leaf"
            },
            self.max_committed_polys,
            batching_pow_bits
        );
        let _ = writeln!(
            out,
            "- committed polynomial size 2^{} at the base rate 2^-{} (domain 2^{})\n",
            self.message_size_log2,
            base_rate_log2,
            self.message_size_log2 + base_rate_log2
        );
        let _ = writeln!(out, "## Rounds\n");
        let _ = writeln!(
            out,
            "| oracle | poly | LDE | domain | fold | queries | query PoW | folding PoW (per step) | OOD PoW | regime | bits/query | UDR would need |\n|---|---|---|---|---|---|---|---|---|---|---|---|"
        );
        let _ = writeln!(
            out,
            "| base | 2^{m} | 2^{r} | 2^{d} | {f} | {q} | {p} | {fp} | – | {reg} | {bpq:.3} | {udr} |",
            m = self.message_size_log2,
            r = base_rate_log2,
            d = self.message_size_log2 + base_rate_log2,
            f = self.fold_log2(),
            q = self.base_num_queries,
            p = self.base_queries_pow_bits,
            fp = self.base_folding_pow_bits(),
            reg = self.base_analysis.regime.describe(base_rate_log2),
            bpq = self.base_analysis.bits_per_query,
            udr = self.base_analysis.unique_decoding_queries,
        );
        let mut poly_size_log2 = self.message_size_log2 - self.fold_log2();
        for (i, round) in self.rounds.iter().enumerate() {
            let _ = writeln!(
                out,
                "| {i} | 2^{m} | 2^{r} | 2^{d} | {f} | {q} | {p} | {fp} {fps:?} | {op} | {reg} | {bpq:.2} | {udr} |",
                m = poly_size_log2,
                r = round.lde_factor_log2,
                d = poly_size_log2 + round.lde_factor_log2,
                f = round.folding_log2,
                q = round.num_queries,
                p = round.queries_pow_bits,
                fp = round.folding_pow_bits(),
                fps = round.analysis.folding_pow_bits_per_step,
                op = round.ood_pow_bits,
                reg = round.analysis.regime.describe(round.lde_factor_log2),
                bpq = round.analysis.bits_per_query,
                udr = round.analysis.unique_decoding_queries,
            );
            poly_size_log2 -= round.folding_log2;
        }
        let _ = writeln!(
            out,
            "\nPlain-text tail: the 2^{poly_size_log2} polynomial.\n"
        );
        let _ = writeln!(out, "## Why\n");
        let _ = writeln!(out, "- base: {}", self.base_analysis.reason);
        for (i, round) in self.rounds.iter().enumerate() {
            let _ = writeln!(out, "- oracle {i}: {}", round.analysis.reason);
        }
        let _ = writeln!(
            out,
            "\n`folding_pow_bits` is one value for every folding-challenge draw of an oracle; the analysis \
             needs one bit less per sumcheck step (listed per step above), so the schedule grinds slightly \
             more than the certification requires.\n"
        );
        out
    }
}

const BASE_UDR: RoundAnalysis = RoundAnalysis {
    regime: ProximityRegime::UniqueDecoding,
    bits_per_query: 0.415,
    unique_decoding_queries: 176,
    folding_pow_bits_per_step: &[],
    reason: "unique decoding at rate 1/2 keeps powers batching within the PoW budget; \
             176 queries at 27 PoW bits reach 100 bits for the base query term",
};

/// [`BASE_UDR`] under the production shapes' grind cap.
const BASE_UDR_26: RoundAnalysis = RoundAnalysis {
    regime: ProximityRegime::UniqueDecoding,
    bits_per_query: 0.415,
    unique_decoding_queries: 179,
    folding_pow_bits_per_step: &[],
    reason: "unique decoding at rate 1/2 keeps powers batching within the PoW budget; \
             179 queries at 26 PoW bits reach 100 bits for the base query term",
};

const BASE_UDR_2_24: RoundAnalysis = RoundAnalysis {
    folding_pow_bits_per_step: &[1],
    reason: "unique decoding at rate 1/2 with 179 queries at 26 PoW bits; \
             one bit of folding PoW brings the base fold to 100 bits",
    ..BASE_UDR_26
};

const fn jbr(
    m: u32,
    bits_per_query: f64,
    unique_decoding_queries: usize,
    folding_pow_bits_per_step: &'static [u32],
    reason: &'static str,
) -> RoundAnalysis {
    RoundAnalysis {
        regime: ProximityRegime::JohnsonBound { m },
        bits_per_query,
        unique_decoding_queries,
        folding_pow_bits_per_step,
        reason,
    }
}

/// `queries_pow_bits` is the SMALLEST grind that lifts the oracle's query
/// term (`num_queries` queries at the regime's bits per query) to the target:
/// the query count is sized against the shape's cap, and the leftover fraction
/// of a bit is not paid for with a full grind at the cap.
const fn round(
    lde_factor_log2: usize,
    folding_log2: usize,
    num_queries: usize,
    queries_pow_bits: u32,
    ood_pow_bits: u32,
    analysis: RoundAnalysis,
) -> EthproofsInternalRound {
    EthproofsInternalRound {
        lde_factor_log2,
        folding_log2,
        num_queries,
        queries_pow_bits,
        ood_pow_bits,
        analysis,
    }
}

/// Johnson bits per query at r = 13: r/2 - log2(7/6), rounded to two decimals.
#[expect(
    clippy::approx_constant,
    reason = "rounded Johnson bits per query, unrelated to the circle constant tau"
)]
const JOHNSON_R13_BITS_PER_QUERY: f64 = 6.28;

/// The certified schedules [`entry`] looks up. Sec-100, base LDE factor 2, cap 16.
pub const ENTRIES: &[EthproofsSoundcalcEntry] = &[
    EthproofsSoundcalcEntry {
        shape: "2^23 committed polynomials, two values per column per leaf (unified_reduced_machine, mul_div_unsigned)",
        level: SecurityLevel::Sec100,
        message_size_log2: 23,
        virtual_packing: false,
        base_lde_factor_log2: 1,
        cap_size: DEFAULT_CAP_SIZE,
        max_committed_polys: 128,
        certified_bits: 100,
        binding_term: "fold(i=0,s=1)",
        base_num_queries: 179,
        base_queries_pow_bits: 26,
        base_batching_pow_bits: None,
        base_analysis: BASE_UDR_26,
        rounds: &[
            round(3, 5, 53, 26, 9, jbr(8, 1.41, 90, &[22, 21, 20, 19, 18],
                "LDE 2^3 keeps the largest internal commitment at domain 2^25; m = 8 gives 1.41 bits/query within the folding PoW cap")),
            round(8, 5, 20, 25, 6, jbr(3, 3.78, 75, &[23, 22, 21, 20, 19],
                "m = 3 minimises the Johnson folding term; LDE 2^8 keeps the domain at 2^25 within the folding PoW cap")),
            round(10, 5, 16, 24, 3, jbr(3, 4.78, 75, &[23, 22, 21, 20, 19],
                "m = 3 minimises the Johnson folding term; LDE 2^10 keeps the domain at 2^22 within the folding PoW cap")),
            round(12, 4, 13, 25, 0, jbr(3, 5.78, 75, &[23, 22, 21, 20],
                "m = 3 minimises the Johnson folding term; LDE 2^12 keeps the domain at 2^19 within the folding PoW cap")),
        ],
    },
    EthproofsSoundcalcEntry {
        shape: "2^24 committed polynomials, two values per column per leaf (add_sub_lui_auipc_mop, inits_and_teardowns, jump_branch_slt, load_store_subword_only, load_store_word_only, shift_binary)",
        level: SecurityLevel::Sec100,
        message_size_log2: 24,
        virtual_packing: false,
        base_lde_factor_log2: 1,
        cap_size: DEFAULT_CAP_SIZE,
        max_committed_polys: 128,
        certified_bits: 100,
        binding_term: "fold(i=0,s=1)",
        base_num_queries: 179,
        base_queries_pow_bits: 26,
        base_batching_pow_bits: None,
        base_analysis: BASE_UDR_2_24,
        rounds: &[
            round(2, 5, 79, 26, 10, jbr(12, 0.94, 110, &[23, 22, 21, 20, 19],
                "LDE 2^2 keeps the first internal commitment at domain 2^25; m = 12 gives 0.94 bits/query within the folding PoW cap")),
            round(8, 5, 20, 25, 7, jbr(3, 3.78, 75, &[24, 23, 22, 21, 20],
                "m = 3 minimises the Johnson folding term; LDE 2^8 keeps the domain at 2^26 within the folding PoW cap")),
            round(10, 5, 16, 24, 4, jbr(3, 4.78, 75, &[24, 23, 22, 21, 20],
                "m = 3 minimises the Johnson folding term; LDE 2^10 keeps the domain at 2^23 within the folding PoW cap")),
            round(12, 4, 13, 25, 1, jbr(3, 5.78, 75, &[24, 23, 22, 21],
                "m = 3 minimises the Johnson folding term; LDE 2^12 keeps the domain at 2^20 within the folding PoW cap")),
            round(13, 3, 12, 25, 0, jbr(3, JOHNSON_R13_BITS_PER_QUERY, 75, &[23, 22, 21],
                "m = 3 minimises the Johnson folding term; LDE 2^13 keeps the domain at 2^17 within the folding PoW cap")),
        ],
    },
    EthproofsSoundcalcEntry {
        shape: "2^22 committed polynomials, virtual packing (bigint_with_control, keccak_chi5, keccak_column_parity, keccak_special5, keccak_theta_rho, blake2_g_function unpacked; blake2_with_compression packed by 2^2)",
        level: SecurityLevel::Sec100,
        message_size_log2: 22,
        virtual_packing: true,
        base_lde_factor_log2: 1,
        cap_size: DEFAULT_CAP_SIZE,
        max_committed_polys: 512,
        certified_bits: 100,
        binding_term: "OOD(i=1)",
        base_num_queries: 179,
        base_queries_pow_bits: 26,
        base_batching_pow_bits: None,
        base_analysis: BASE_UDR_26,
        rounds: &[
            round(3, 6, 53, 26, 9, jbr(8, 1.41, 90, &[22, 21, 20, 19, 18, 17],
                "LDE 2^3 keeps the largest internal commitment at domain 2^25; m = 8 gives 1.41 bits/query within the folding PoW cap")),
            round(8, 5, 20, 25, 5, jbr(3, 3.78, 75, &[22, 21, 20, 19, 18],
                "m = 3 minimises the Johnson folding term; LDE 2^8 keeps the domain at 2^24 within the folding PoW cap")),
            round(10, 5, 16, 24, 2, jbr(3, 4.78, 75, &[22, 21, 20, 19, 18],
                "m = 3 minimises the Johnson folding term; LDE 2^10 keeps the domain at 2^21 within the folding PoW cap")),
            round(12, 5, 13, 25, 0, jbr(3, 5.78, 75, &[22, 21, 20, 19, 18],
                "m = 3 minimises the Johnson folding term; LDE 2^12 keeps the domain at 2^18 within the folding PoW cap")),
        ],
    },
    EthproofsSoundcalcEntry {
        shape: "2^20 committed polynomials, two values per column per leaf (blake2_with_extended_control test circuit)",
        level: SecurityLevel::Sec100,
        message_size_log2: 20,
        virtual_packing: false,
        base_lde_factor_log2: 1,
        cap_size: DEFAULT_CAP_SIZE,
        max_committed_polys: 1024,
        certified_bits: 100,
        binding_term: "OOD(i=1)",
        base_num_queries: 176,
        base_queries_pow_bits: 27,
        base_batching_pow_bits: None,
        base_analysis: BASE_UDR,
        rounds: &[
            round(7, 5, 23, 25, 7, jbr(3, 3.28, 74, &[23, 22, 21, 20, 19],
                "m = 3 minimises the Johnson folding term; LDE 2^7 keeps the domain at 2^26 within the folding PoW cap")),
            round(9, 5, 18, 24, 4, jbr(3, 4.28, 74, &[23, 22, 21, 20, 19],
                "m = 3 minimises the Johnson folding term; LDE 2^9 keeps the domain at 2^23 within the folding PoW cap")),
            round(11, 4, 14, 27, 1, jbr(3, 5.28, 74, &[23, 22, 21, 20],
                "m = 3 minimises the Johnson folding term; LDE 2^11 keeps the domain at 2^20 within the folding PoW cap")),
            round(13, 4, 12, 25, 0, jbr(3, JOHNSON_R13_BITS_PER_QUERY, 74, &[24, 23, 22, 21],
                "m = 3 minimises the Johnson folding term; LDE 2^13 keeps the domain at 2^18 within the folding PoW cap")),
        ],
    },
    EthproofsSoundcalcEntry {
        shape: "2^20 committed polynomials, virtual packing (blake2_with_extended_control test circuit)",
        level: SecurityLevel::Sec100,
        message_size_log2: 20,
        virtual_packing: true,
        base_lde_factor_log2: 1,
        cap_size: DEFAULT_CAP_SIZE,
        max_committed_polys: 1024,
        certified_bits: 100,
        binding_term: "OOD(i=1)",
        base_num_queries: 176,
        base_queries_pow_bits: 27,
        base_batching_pow_bits: None,
        base_analysis: BASE_UDR,
        rounds: &[
            round(7, 6, 23, 25, 8, jbr(3, 3.28, 74, &[24, 23, 22, 21, 20, 19],
                "m = 3 minimises the Johnson folding term; LDE 2^7 keeps the domain at 2^27 within the folding PoW cap")),
            round(9, 5, 18, 24, 4, jbr(3, 4.28, 74, &[23, 22, 21, 20, 19],
                "m = 3 minimises the Johnson folding term; LDE 2^9 keeps the domain at 2^23 within the folding PoW cap")),
            round(11, 4, 14, 27, 1, jbr(3, 5.28, 74, &[23, 22, 21, 20],
                "m = 3 minimises the Johnson folding term; LDE 2^11 keeps the domain at 2^20 within the folding PoW cap")),
            round(13, 4, 12, 25, 0, jbr(3, JOHNSON_R13_BITS_PER_QUERY, 74, &[24, 23, 22, 21],
                "m = 3 minimises the Johnson folding term; LDE 2^13 keeps the domain at 2^18 within the folding PoW cap")),
        ],
    },
];

/// The `ProofProfile::Compression` schedule. Not in [`ENTRIES`]: it shares its
/// lookup key with a standard entry.
///
/// Each BabyBear challenge coordinate is a reduced transcript word with at
/// most three preimages. The Ext4 challenge has maximum point mass
/// `81/2^128`, so the WHIR certificate uses `2^128/81` as its denominator.
///
/// Soundcalc's SWIRL accounting charges the base list on GKR-side terms. This
/// Johnson base has `L ≈ 9.90`. Charge `log2(L)` to each lookup and
/// `k * log2(L)` to shared memory for `k` instances. The memory identity has
/// degree at most `(4k + 2j) * 2^23 + 33` with `j` inline i/t instances.
/// At `j = k = 3`, 19 memory PoW bits give 101.568 bits with the two-bit
/// reserve. The derived 14-bit lookup grind gives 101.25 bits.
pub const COMPRESSION_2_23: EthproofsSoundcalcEntry = EthproofsSoundcalcEntry {
    shape: "2^23 committed polynomials, two values per column per leaf, base LDE 2^3, merged memory and witness (unified_reduced_machine compression)",
    level: SecurityLevel::Sec100,
    message_size_log2: 23,
    virtual_packing: false,
    base_lde_factor_log2: 3,
    cap_size: 8,
    max_committed_polys: 128,
    certified_bits: 100,
    binding_term: "batching",
    base_num_queries: 59,
    base_queries_pow_bits: 25,
    base_batching_pow_bits: Some(25),
    base_analysis: jbr(3, 1.28, 91, &[17],
        "at rate 2^-3, m = 3 gives 1.28 bits/query and keeps the binding batching term at 100 bits with a 25-bit grind at the width ceiling; the fold term needs 17 PoW bits"),
    rounds: &[
        round(5, 5, 32, 25, 10, jbr(5, 2.36, 79, &[24, 23, 22, 21, 20],
            "LDE 2^5 (domain 2^27); m = 5 gives 2.36 bits/query within the 24-bit fold cap; one OOD sample needs 10 PoW bits")),
        round(8, 5, 20, 25, 6, jbr(3, 3.78, 76, &[23, 22, 21, 20, 19],
            "m = 3 minimises the (m + 1/2)^5 fold term; LDE 2^8 (domain 2^25), fold grind 23 bits; 3.78 bits/query")),
        round(10, 5, 16, 24, 3, jbr(3, 4.78, 76, &[23, 22, 21, 20, 19],
            "m = 3; LDE 2^10 (domain 2^22), fold grind 23 bits; 4.78 bits/query")),
        round(12, 4, 13, 25, 0, jbr(3, 5.78, 76, &[23, 22, 21, 20],
            "m = 3; LDE 2^12 (domain 2^19), fold grind 23 bits; 5.78 bits/query, no OOD grind")),
    ],
};

/// The entry for `input` at `level`. Panics when no schedule was certified
/// for that shape, when the committed-polynomial count is missing, or when
/// the circuit commits more polynomials than the entry's ceiling.
pub(super) fn entry(level: SecurityLevel, input: &WhirInput) -> &'static EthproofsSoundcalcEntry {
    let mode = SoundnessMode::EthproofsSoundnessCalc;
    let entry = ENTRIES
        .iter()
        .find(|e| {
            e.level == level
                && e.message_size_log2 == input.message_size_log2
                && e.virtual_packing == input.virtual_packing
        })
        .unwrap_or_else(|| {
            panic!("MissingSchedule: no {mode:?} WHIR schedule for {level:?}, input {input:?}")
        });
    let actual = input.num_committed_polys.unwrap_or_else(|| {
        panic!(
            "MissingColumnCount: the EthproofsSoundnessCalc schedule is certified for a \
             committed-polynomial ceiling: provide the compiled circuit's column count"
        )
    });
    assert!(
        actual <= entry.max_committed_polys,
        "CommittedPolynomialCeiling: {actual} committed polynomials exceed the {} ceiling \
         certified for EthproofsSoundnessCalc",
        entry.max_committed_polys
    );
    entry
}

#[cfg(test)]
mod tests {
    use super::*;

    fn input_for(entry: &EthproofsSoundcalcEntry, num_committed_polys: usize) -> WhirInput {
        WhirInput {
            message_size_log2: entry.message_size_log2,
            physical_packing_log2: 0,
            virtual_packing: entry.virtual_packing,
            num_committed_polys: Some(num_committed_polys),
        }
    }

    fn validate_entry(entry: &EthproofsSoundcalcEntry, config: &ProverConfig) {
        let schedule = entry.schedule(0);
        assert_eq!(config.whir_schedule, schedule);
        config.validate_for_whir_message_size(entry.message_size_log2);
        assert_eq!(entry.certified_bits, entry.level.security_bits());
        assert_eq!(schedule.cap_size, entry.cap_size);
        assert_eq!(
            schedule.base_round.lde_factor_log2,
            entry.base_lde_factor_log2
        );
        assert_eq!(schedule.base_round.fold_log2, entry.fold_log2());
        assert_eq!(
            schedule.base_round.batching_pow_bits,
            Some(entry.batching_pow_bits())
        );
        let base_folding_per_step = entry.base_analysis.folding_pow_bits_per_step;
        assert!(
            base_folding_per_step.is_empty() || base_folding_per_step.len() == entry.fold_log2()
        );
        assert_eq!(
            schedule.base_round.folding_pow_bits,
            base_folding_per_step.first().copied().unwrap_or(0)
        );
        assert!(schedule.base_round.folding_pow_bits <= 24);
        assert_eq!(schedule.base_round.num_queries, entry.base_num_queries);
        assert_eq!(
            schedule.base_round.queries_pow_bits,
            entry.base_queries_pow_bits
        );
        let query_term = |queries: usize, analysis: &RoundAnalysis, pow_bits: u32| {
            queries as f64 * analysis.bits_per_query + pow_bits as f64
        };
        assert!(
            query_term(
                entry.base_num_queries,
                &entry.base_analysis,
                entry.base_queries_pow_bits
            ) >= entry.certified_bits as f64
        );
        for (round, certified) in schedule.internal_rounds.iter().zip(entry.rounds) {
            assert_eq!(round.num_ood_samples, 1);
            assert!(round.queries_pow_bits <= 27);
            assert!(
                query_term(
                    round.num_queries,
                    &certified.analysis,
                    round.queries_pow_bits
                ) >= entry.certified_bits as f64
            );
            assert!(round.folding_pow_bits <= 24);
            assert!(round.ood_pow_bits <= 27);
            assert_eq!(
                certified.analysis.folding_pow_bits_per_step.len(),
                round.folding_log2
            );
            assert_eq!(
                round.folding_pow_bits, certified.analysis.folding_pow_bits_per_step[0],
                "the per-step folding PoW schedule decreases from its first entry"
            );
            assert!(matches!(
                certified.analysis.regime,
                ProximityRegime::JohnsonBound { m: 3..=12 }
            ));
        }
        // every oracle domain fits BabyBear's two-adicity
        assert!(entry.message_size_log2 + entry.base_lde_factor_log2 <= 27);
        let mut poly_size_log2 = entry.message_size_log2 - entry.fold_log2();
        for round in schedule.internal_rounds.iter() {
            assert!(poly_size_log2 + round.lde_factor_log2 <= 27);
            poly_size_log2 -= round.folding_log2;
        }
    }

    #[test]
    fn every_entry_validates_and_records_its_certification() {
        for entry in ENTRIES {
            let config = standard_config(
                entry.message_size_log2,
                entry.level,
                BaseSoundness::Ethproofs(entry.base_analysis.regime),
                entry.schedule(0),
            );
            validate_entry(entry, &config);
            let input = input_for(entry, entry.max_committed_polys);
            let notes = entry.render_notes(entry.level, &input);
            assert!(notes.contains("soundcalc"));
            assert!(notes.contains(&format!("**{} bits**", entry.certified_bits)));
            assert!(notes.contains(entry.base_analysis.reason));
            for round in entry.rounds {
                assert!(notes.contains(round.analysis.reason));
            }
            assert_eq!(
                whir_schedule(
                    SoundnessMode::EthproofsSoundnessCalc,
                    entry.level,
                    &input_for(entry, entry.max_committed_polys)
                ),
                config.whir_schedule
            );
        }
        let config = ethproofs_compression_config_for_2_23();
        validate_entry(&COMPRESSION_2_23, &config);
        assert_eq!(
            config.commitment_mode,
            CommitmentMode::MergedMemoryAndWitness
        );
    }

    #[test]
    fn batching_pow_is_the_formula_at_the_ceiling() {
        let expected = [
            (23, 1, 10),
            (24, 1, 11),
            (22, 0, 11),
            (20, 1, 10),
            (20, 0, 10),
        ];
        assert_eq!(ENTRIES.len(), expected.len());
        for (entry, (message, fold, bits)) in ENTRIES.iter().zip(expected) {
            assert_eq!(
                (entry.message_size_log2, entry.fold_log2()),
                (message, fold)
            );
            assert_eq!(entry.batching_pow_bits(), bits, "2^{message}");
        }
    }

    #[test]
    #[ignore = "requires soundcalc 2af5e7d on PYTHONPATH"]
    fn whir_schedules_meet_soundcalc_target() {
        use crate::gkr::prover_config::pow_bits::committed_base_oracle_columns;
        use field::Proth120;
        use serde_json::json;
        use std::process::{Command, Stdio};
        use transcript::{ChallengePointMass, Keccak256Transcript};

        let baby_bear: Vec<_> = ENTRIES
            .iter()
            .map(|entry| (entry, entry.schedule(0)))
            .chain([(
                &COMPRESSION_2_23,
                ethproofs_compression_config_for_2_23().whir_schedule,
            )])
            .map(|(entry, schedule)| {
                let multiplicities: Vec<_> = std::iter::once(entry.base_analysis)
                    .chain(entry.rounds.iter().map(|round| round.analysis))
                    .map(|analysis| match analysis.regime {
                        ProximityRegime::UniqueDecoding => None,
                        ProximityRegime::JohnsonBound { m } => Some(m),
                    })
                    .collect();
                json!({
                    "shape": entry.shape,
                    "message_log2": entry.message_size_log2,
                    "columns": entry.max_committed_polys,
                    "multiplicities": multiplicities,
                    "binding_term": entry.binding_term,
                    "certified_bits": entry.certified_bits,
                    "schedule": schedule,
                })
            })
            .collect();
        let wrap_layout: cs::gkr_compiler::GKRCircuitArtifact<Proth120> =
            serde_json::from_str(include_str!(
                "../../../../../circuit_defs/unrolled_circuits/unified_reduced_machine_proth120_2_22/generated/layout.json"
            ))
            .expect("embedded 2^22 Proth120 unified layout");
        let wrap = l1_wrap::ethproofs_packed_prover_config();
        assert_eq!(wrap_layout.trace_len, 1 << wrap.trace_len_log2);
        let sampler = |mass: ChallengePointMass| {
            json!({
                "random_bits": mass.random_bits,
                "max_preimages": mass.max_preimages,
            })
        };
        let data = json!({
            "baby_bear": baby_bear,
            "baby_bear_sampler": sampler(
                <Blake2sTranscript as Transcript<BabyBearField, BabyBearExt4>>::CHALLENGE_POINT_MASS,
            ),
            "l1_wrap": wrap,
            "l1_wrap_sampler": sampler(Keccak256Transcript::CHALLENGE_POINT_MASS),
            "l1_wrap_columns": committed_base_oracle_columns(
                &wrap_layout, wrap.pack_log2(), wrap.merged_memory_and_witness(),
            ),
        });
        let mut checker = Command::new("python3")
            .arg(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/src/gkr/prover_config/example_configs/soundcalc/check_schedules.py"
            ))
            .stdin(Stdio::piped())
            .spawn()
            .expect("start soundcalc schedule check");
        let input_result = serde_json::to_writer(checker.stdin.take().unwrap(), &data);
        assert!(
            checker.wait().unwrap().success(),
            "soundcalc schedule check"
        );
        input_result.unwrap();
    }

    #[test]
    fn production_shapes_are_covered() {
        let level = SecurityLevel::Sec100;
        // (trace, packing, memory, witness, setup) of every production circuit
        let circuits = [
            (24, BasePacking::NONE, 26, 22, 8),      // add_sub_lui_auipc_mop
            (24, BasePacking::NONE, 32, 0, 0),       // inits_and_teardowns
            (24, BasePacking::NONE, 26, 29, 10),     // jump_branch_slt
            (24, BasePacking::NONE, 29, 17, 9),      // load_store_subword_only
            (24, BasePacking::NONE, 29, 11, 9),      // load_store_word_only
            (24, BasePacking::NONE, 30, 28, 10),     // shift_binary
            (23, BasePacking::NONE, 26, 24, 9),      // mul_div_unsigned
            (23, BasePacking::NONE, 38, 58, 10),     // unified_reduced_machine
            (22, BasePacking::VIRTUAL, 97, 160, 3),  // bigint_with_control
            (22, BasePacking::VIRTUAL, 66, 123, 11), // keccak_chi5
            (22, BasePacking::VIRTUAL, 75, 92, 8),   // keccak_column_parity
            (22, BasePacking::VIRTUAL, 91, 175, 8),  // keccak_special5
            (22, BasePacking::VIRTUAL, 72, 127, 9),  // keccak_theta_rho
            (22, BasePacking::VIRTUAL, 55, 57, 9),   // blake2_g_function
            (20, BasePacking::physical_and_virtual(2), 225, 538, 6), // blake2_with_compression
        ];
        for (trace, packing, memory, witness, setup) in circuits {
            let columns = BaseColumns {
                memory,
                witness,
                setup,
            };
            let input = WhirInput::new(
                trace,
                packing,
                &columns,
                CommitmentMode::SeparateMemoryAndWitness,
            );
            let e = entry(level, &input);
            assert!(input.num_committed_polys.unwrap() <= e.max_committed_polys);
            prover_config(
                SoundnessMode::EthproofsSoundnessCalc,
                level,
                trace,
                packing,
                Some(&columns),
            );
        }
    }

    #[test]
    #[should_panic(expected = "exceed the 128 ceiling")]
    fn more_polys_than_the_ceiling_is_rejected() {
        let e = &ENTRIES[0];
        entry(e.level, &input_for(e, e.max_committed_polys + 1));
    }

    #[test]
    #[should_panic(expected = "no EthproofsSoundnessCalc WHIR schedule")]
    fn uncertified_shape_is_rejected() {
        entry(
            SecurityLevel::Sec100,
            &WhirInput {
                message_size_log2: 21,
                physical_packing_log2: 0,
                virtual_packing: false,
                num_committed_polys: Some(1),
            },
        );
    }
}
