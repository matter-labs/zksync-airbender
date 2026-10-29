//! The [`SoundnessMode::EthproofsSoundnessCalc`] schedules: WHIR schedules
//! certified at the security level by `ethereum/soundcalc` (commit `2af5e7d`,
//! 2026-09-21), the calculator the ethproofs listing uses.
//!
//! What soundcalc models and how it was run (`soundcalc/README.md` next to
//! this file has the reproduction recipe, `soundcalc/whir_schedule_search.py`
//! is the search that produced every entry):
//!
//! * only its WHIR PCS module (`soundcalc/pcs/whir.py`: WHIR Theorem 5.2 with
//!   the BCHKS25 proximity-gap bounds) — soundcalc has no model of our GKR
//!   circuit layer, whose lookup / memory challenges sit at 105–118 bits by
//!   our own field-size accounting;
//! * BabyBear⁴ challenge field (`|F| ≈ 2^123.6`), 256-bit hashes, powers
//!   batching of the committed polynomials, constraint degree 3 (soundcalc's
//!   minimum; ours is 2, so ~0.6 bit conservative);
//! * our explicit per-oracle LDE factors are written over soundcalc's
//!   "domain halves every iteration" default;
//! * the proximity regime is chosen PER WHIR ITERATION (the theorem carries a
//!   separate proximity parameter `δ_i` and list size `ℓ_i` per iteration):
//!   [`ProximityRegime::UniqueDecoding`] for the base round — at rate 1/2 the
//!   Johnson-bound batching term of `N − 1` columns is 73–90 bits for any
//!   multiplicity and cannot be lifted within any sane batching PoW, and the
//!   Johnson radius at rate 1/2 is below the unique-decoding one anyway —
//!   and [`ProximityRegime::JohnsonBound`] with an explicit multiplicity `m`
//!   afterwards, where a query is worth 1.9–6.8 bits instead of ≤ 1;
//! * the price of the Johnson rounds is a proof of work before every
//!   folding challenge (their fold term starts 18–24 bits short) and before
//!   the single OOD sample of every oracle (the user-chosen alternative to a
//!   second sample), capped at 24 and 27 bits; the late oracles' LDE factors
//!   are cut from the pessimistic ladder's so that their domains keep that
//!   fold grind within the cap (the fold term grows with `n / ρ^1.5`);
//! * every grind is the SMALLEST that lifts its term to the target: the
//!   per-round query count is sized against a 27-bit query-PoW cap, then the
//!   query PoW is lowered to what the chosen count actually leaves short
//!   (e.g. 12 queries at 6.28 bits each are 75 bits, so 25 bits of grind, not
//!   27); the folding and OOD grinds are computed the same way;
//! * virtual packing (`fold_log2 = 0`) is emulated as a message one bit
//!   larger with a round-0 fold of 1 (soundcalc needs `k_0 ≥ 1`); the
//!   re-committed oracle 0 is then exactly our batched polynomial, the
//!   emulated base fold term is 1 bit conservative, and the batching term is
//!   recomputed on the real base code.
//!
//! What this mode changes against the pessimistic ladder, and why it cannot
//! keep the base round: under both accepted regimes a query into the rate-1/2
//! base oracle is worth at most `−log2(1 − 1/4) ≈ 0.415` bits, so today's 89
//! queries at 26 PoW bits certify 62 bits whatever the later rounds do; 100
//! bits need `ceil((100 − 28) / 0.415) = 174` base queries at 28 PoW bits
//! (base LDE factor and round-0 fold unchanged). Every later round keeps its
//! fold; the second oracle keeps its LDE factor, the later ones move to a
//! better rate at the cost of a few queries.
//!
//! Each [`EthproofsSoundcalcEntry`] is certified for a CEILING on the number
//! of physically committed polynomials (it only enters the batching PoW,
//! which is computed for the ceiling with the same formula as everywhere
//! else, [`batched_proximity_check_pow_bits`]); a circuit with more committed
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

use super::super::pow_bits::batched_proximity_check_pow_bits;
use super::*;

/// The proximity-gap regime an oracle's terms are evaluated under.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
    /// the same query PoW (for reference; the base round IS unique decoding).
    pub unique_decoding_queries: usize,
    /// The folding-challenge PoW the analysis needs per sumcheck step of this
    /// oracle (decreasing by one bit per step); the schedule's single
    /// `folding_pow_bits` is the maximum. Empty for a round without folds.
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
    /// Ceiling on the physically committed polynomials (the count the
    /// batching challenge combines) this entry is certified for.
    pub max_committed_polys: usize,
    /// Bits soundcalc certifies for the WHIR PCS with this schedule.
    pub certified_bits: usize,
    /// The soundcalc term at `certified_bits`.
    pub binding_term: &'static str,
    pub base_num_queries: usize,
    pub base_queries_pow_bits: u32,
    pub base_analysis: RoundAnalysis,
    pub rounds: &'static [EthproofsInternalRound],
    /// The pessimistic-conjecture ladder of the same shape, for comparison.
    pub pessimistic_ladder: &'static str,
}

impl EthproofsSoundcalcEntry {
    pub const fn fold_log2(&self) -> usize {
        if self.virtual_packing {
            0
        } else {
            1
        }
    }

    /// The batching PoW the entry was certified with: the standard
    /// [`batched_proximity_check_pow_bits`] at the committed-polynomial
    /// ceiling (which lands the batching term at 102 bits under unique
    /// decoding).
    pub fn batching_pow_bits(&self) -> u32 {
        batched_proximity_check_pow_bits::<BabyBearField, BabyBearExt4>(
            self.level.security_bits(),
            self.message_size_log2,
            DEFAULT_LDE_FACTOR.trailing_zeros() as usize,
            self.max_committed_polys,
        )
    }

    pub fn schedule(&self, physical_packing_log2: usize) -> WhirSchedule {
        WhirSchedule {
            cap_size: DEFAULT_CAP_SIZE,
            base_round: WhirBaseRoundSchedule {
                lde_factor_log2: DEFAULT_LDE_FACTOR.trailing_zeros() as usize,
                physical_packing_log2,
                fold_log2: self.fold_log2(),
                batching_pow_bits: Some(self.batching_pow_bits()),
                folding_pow_bits: 0,
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
        let base_rate_log2 = DEFAULT_LDE_FACTOR.trailing_zeros() as usize;
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
             Model inputs: BabyBear⁴ challenge field (|F| ≈ 2^123.6), 256-bit hashes, powers batching, \
             constraint degree 3 (soundcalc's minimum; ours is 2), our explicit per-oracle LDE factors, \
             one OOD sample per oracle. The GKR circuit layer is outside the model (105–118 bits by our \
             own field-size accounting).\n",
            self.certified_bits, self.binding_term
        );
        let _ = writeln!(out, "## This circuit\n");
        let _ = writeln!(
            out,
            "- committed polynomials entering WHIR: **{}** (from the compiled circuit; physical packing \
             2^{}{}), certified ceiling {} → batching PoW {} bits (computed for the ceiling with \
             `pow_bits_for_batched_proximity`; batching term 102 bits under unique decoding)",
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
            "| base | 2^{m} | 2^{r} | 2^{d} | {f} | {q} | {p} | 0 | – | {reg} | {bpq:.3} | {udr} |",
            m = self.message_size_log2,
            r = base_rate_log2,
            d = self.message_size_log2 + base_rate_log2,
            f = self.fold_log2(),
            q = self.base_num_queries,
            p = self.base_queries_pow_bits,
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
        let _ = writeln!(out, "## Against the pessimistic-conjecture ladder\n");
        let _ = writeln!(out, "{}\n", self.pessimistic_ladder);
        let _ = writeln!(
            out,
            "The base round cannot stay at the ladder's 89 queries / 26 PoW bits: under both accepted \
             regimes a query into the rate-1/2 base oracle is worth at most 0.415 bits, so that base round \
             certifies 62 bits whatever the later rounds do; 100 bits need ceil((100 − 28) / 0.415) = 174 \
             queries at 28 PoW bits with the base LDE factor and round-0 fold unchanged. The later oracles' \
             LDE factors are cut because the Johnson-bound fold term grows with n / ρ^1.5 and must stay \
             within a 24-bit folding grind."
        );
        out
    }
}

const BASE_UDR: RoundAnalysis = RoundAnalysis {
    regime: ProximityRegime::UniqueDecoding,
    bits_per_query: 0.415,
    unique_decoding_queries: 174,
    folding_pow_bits_per_step: &[],
    reason: "unique decoding is the only regime certifiable at rate 1/2: the Johnson-bound batching \
             term of the committed columns is 73–90 bits for any multiplicity and cannot be lifted \
             within any sane batching PoW, and the Johnson radius at rate 1/2 (0.28–0.48 bits/query) \
             is below the unique-decoding one (0.415) anyway; 174 queries at 28 PoW bits put the base \
             query term at exactly 100 bits (no folding PoW needed: the unique-decoding fold term is \
             above 100 by itself)",
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
/// the query count is sized against a 27-bit cap, and the leftover fraction of
/// a bit is not paid for with a full 27-bit grind.
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

/// Every certified schedule. Sec-100, base LDE factor 2, cap 16.
pub const ENTRIES: &[EthproofsSoundcalcEntry] = &[
    EthproofsSoundcalcEntry {
        shape: "2^23 committed polynomials, two values per column per leaf (unified_reduced_machine, mul_div_unsigned)",
        level: SecurityLevel::Sec100,
        message_size_log2: 23,
        virtual_packing: false,
        max_committed_polys: 128,
        certified_bits: 100,
        binding_term: "OOD(i=1)",
        base_num_queries: 174,
        base_queries_pow_bits: 28,
        base_analysis: BASE_UDR,
        rounds: &[
            round(5, 5, 31, 27, 8, jbr(5, 2.36, 77, &[22, 21, 20, 19, 18],
                "LDE 2^5 as in the ladder (domain 2^27); rate 2^-5 is still moderate, so m = 5 (above the floor) buys 2.36 bits/query at a 22-bit folding grind — 31 queries where unique decoding would need 77; the OOD term of this largest oracle needs 8 PoW bits with a single sample")),
            round(9, 5, 18, 24, 5, jbr(3, 4.28, 74, &[24, 23, 22, 21, 20],
                "m = 3 (the theorem's floor) minimises the (m + 1/2)^5 fold term; LDE 2^9 (the ladder's) keeps the domain at 2^26 where the fold grind is 24 bits; 4.28 bits/query")),
            round(11, 5, 14, 27, 2, jbr(3, 5.28, 74, &[24, 23, 22, 21, 20],
                "m = 3; LDE cut from the ladder's 2^14 to 2^11 so the 2^23 domain keeps the fold grind at 24 bits; 5.28 bits/query")),
            round(13, 4, 12, 25, 0, jbr(3, JOHNSON_R13_BITS_PER_QUERY, 74, &[24, 23, 22, 21],
                "m = 3; LDE cut from the ladder's 2^19 to 2^13 (domain 2^20) so 24 bits of fold grind suffice; 6.28 bits/query, the OOD term needs no grind")),
        ],
        pessimistic_ladder: "ladder: folds [1,5,5,5,4], LDE log2 [4,9,14,19], queries [89,23,10,7,5], query PoW [26,24,25,19,21], no folding / OOD PoW.",
    },
    EthproofsSoundcalcEntry {
        shape: "2^24 committed polynomials, two values per column per leaf (add_sub_lui_auipc_mop, inits_and_teardowns, jump_branch_slt, load_store_subword_only, load_store_word_only, shift_binary)",
        level: SecurityLevel::Sec100,
        message_size_log2: 24,
        virtual_packing: false,
        max_committed_polys: 128,
        certified_bits: 100,
        binding_term: "OOD(i=1)",
        base_num_queries: 174,
        base_queries_pow_bits: 28,
        base_analysis: BASE_UDR,
        rounds: &[
            round(4, 5, 39, 26, 9, jbr(8, 1.91, 80, &[24, 23, 22, 21, 20],
                "LDE 2^4 as in the ladder (domain 2^27, the field's two-adicity cap); at rate 2^-4 the Johnson radius is close to the unique-decoding one, m = 8 keeps the fold grind of this 2^27 domain at the 24-bit cap for 1.91 bits/query — 39 queries where unique decoding would need 80; the OOD term needs 9 PoW bits")),
            round(8, 5, 20, 25, 5, jbr(3, 3.78, 74, &[22, 21, 20, 19, 18],
                "m = 3 (the theorem's floor) minimises the (m + 1/2)^5 fold term; LDE cut from the ladder's 2^9 to 2^8 (domain 2^26) so the fold grind is 22 bits; 3.78 bits/query")),
            round(10, 5, 16, 24, 2, jbr(3, 4.78, 74, &[22, 21, 20, 19, 18],
                "m = 3; LDE cut from the ladder's 2^14 to 2^10 (domain 2^23), fold grind 22 bits; 4.78 bits/query")),
            round(12, 4, 13, 25, 0, jbr(3, 5.78, 74, &[22, 21, 20, 19],
                "m = 3; LDE cut from the ladder's 2^19 to 2^12 (domain 2^20), fold grind 22 bits; 5.78 bits/query, no OOD grind")),
            round(14, 3, 11, 26, 0, jbr(3, 6.78, 74, &[23, 22, 21],
                "m = 3; LDE cut from the ladder's 2^19 to 2^14 (domain 2^18), fold grind 23 bits; 6.78 bits/query, no OOD grind")),
        ],
        pessimistic_ladder: "ladder: folds [1,5,5,5,4,3], LDE log2 [4,9,14,19,19], queries [89,23,10,7,5,5], query PoW [26,24,25,19,21,21], no folding / OOD PoW.",
    },
    EthproofsSoundcalcEntry {
        shape: "2^22 committed polynomials, virtual packing (bigint_with_control, keccak_chi5, keccak_column_parity, keccak_special5, keccak_theta_rho, blake2_g_function unpacked; blake2_with_compression packed by 2^2)",
        level: SecurityLevel::Sec100,
        message_size_log2: 22,
        virtual_packing: true,
        max_committed_polys: 512,
        certified_bits: 100,
        binding_term: "OOD(i=1)",
        base_num_queries: 174,
        base_queries_pow_bits: 28,
        base_analysis: BASE_UDR,
        rounds: &[
            round(5, 6, 31, 27, 8, jbr(5, 2.36, 77, &[22, 21, 20, 19, 18, 17],
                "the re-committed batched polynomial at LDE 2^5 (the virtual twin's: domain 2^27, folded by 6); rate 2^-5 is still moderate, so m = 5 buys 2.36 bits/query at a 22-bit folding grind — 31 queries where unique decoding would need 77; its OOD term needs 8 PoW bits with a single sample")),
            round(9, 5, 18, 24, 4, jbr(3, 4.28, 74, &[23, 22, 21, 20, 19],
                "m = 3 (the theorem's floor) minimises the (m + 1/2)^5 fold term; LDE cut from the ladder's 2^11 to 2^9 (domain 2^25), fold grind 23 bits; 4.28 bits/query")),
            round(11, 5, 14, 27, 1, jbr(3, 5.28, 74, &[23, 22, 21, 20, 19],
                "m = 3; LDE cut from the ladder's 2^15 to 2^11 (domain 2^22), fold grind 23 bits; 5.28 bits/query")),
            round(13, 5, 12, 25, 0, jbr(3, JOHNSON_R13_BITS_PER_QUERY, 74, &[23, 22, 21, 20, 19],
                "m = 3; LDE cut from the ladder's 2^19 to 2^13 (domain 2^19), fold grind 23 bits; 6.28 bits/query, no OOD grind")),
        ],
        pessimistic_ladder: "ladder (virtual twin): folds [0,6,5,5,5], LDE log2 [5,11,15,19], queries [89,15,8,6,5], query PoW [26,25,27,25,21], no folding / OOD PoW.",
    },
    EthproofsSoundcalcEntry {
        shape: "2^20 committed polynomials, two values per column per leaf (blake2_with_extended_control test circuit)",
        level: SecurityLevel::Sec100,
        message_size_log2: 20,
        virtual_packing: false,
        max_committed_polys: 1024,
        certified_bits: 100,
        binding_term: "OOD(i=1)",
        base_num_queries: 174,
        base_queries_pow_bits: 28,
        base_analysis: BASE_UDR,
        rounds: &[
            round(8, 5, 20, 25, 6, jbr(3, 3.78, 74, &[23, 22, 21, 20, 19],
                "LDE 2^8 as in the ladder (domain 2^27); m = 3 (the theorem's floor) minimises the (m + 1/2)^5 fold term, fold grind 23 bits; 3.78 bits/query — 20 queries where unique decoding would need 74; the OOD term needs 6 PoW bits")),
            round(10, 5, 16, 24, 3, jbr(3, 4.78, 74, &[23, 22, 21, 20, 19],
                "m = 3; LDE cut from the ladder's 2^13 to 2^10 (domain 2^24), fold grind 23 bits; 4.78 bits/query")),
            round(12, 4, 13, 25, 0, jbr(3, 5.78, 74, &[23, 22, 21, 20],
                "m = 3; LDE cut from the ladder's 2^15 to 2^12 (domain 2^21), fold grind 23 bits; 5.78 bits/query, no OOD grind")),
            round(14, 4, 11, 26, 0, jbr(3, 6.78, 74, &[24, 23, 22, 21],
                "m = 3; LDE cut from the ladder's 2^19 to 2^14 (domain 2^19), fold grind 24 bits; 6.78 bits/query, no OOD grind")),
        ],
        pessimistic_ladder: "ladder: folds [1,5,5,4,4], LDE log2 [8,13,15,19], queries [89,11,7,6,5], query PoW [26,27,25,25,21], no folding / OOD PoW.",
    },
    EthproofsSoundcalcEntry {
        shape: "2^20 committed polynomials, virtual packing (blake2_with_extended_control test circuit)",
        level: SecurityLevel::Sec100,
        message_size_log2: 20,
        virtual_packing: true,
        max_committed_polys: 1024,
        certified_bits: 100,
        binding_term: "OOD(i=1)",
        base_num_queries: 174,
        base_queries_pow_bits: 28,
        base_analysis: BASE_UDR,
        rounds: &[
            round(7, 6, 22, 27, 7, jbr(4, 3.33, 74, &[24, 23, 22, 21, 20, 19],
                "the re-committed batched polynomial at LDE 2^7 (the virtual twin's: domain 2^27, folded by 6); m = 4 keeps the fold grind of the 2^27 domain at the 24-bit cap for 3.33 bits/query — 22 queries where unique decoding would need 74; its OOD term needs 7 PoW bits")),
            round(10, 5, 16, 24, 3, jbr(3, 4.78, 74, &[23, 22, 21, 20, 19],
                "m = 3 (the theorem's floor) minimises the (m + 1/2)^5 fold term; LDE cut from the ladder's 2^13 to 2^10 (domain 2^24), fold grind 23 bits; 4.78 bits/query")),
            round(12, 4, 13, 25, 0, jbr(3, 5.78, 74, &[23, 22, 21, 20],
                "m = 3; LDE cut from the ladder's 2^15 to 2^12 (domain 2^21), fold grind 23 bits; 5.78 bits/query, no OOD grind")),
            round(14, 4, 11, 26, 0, jbr(3, 6.78, 74, &[24, 23, 22, 21],
                "m = 3; LDE cut from the ladder's 2^19 to 2^14 (domain 2^19), fold grind 24 bits; 6.78 bits/query, no OOD grind")),
        ],
        pessimistic_ladder: "ladder (virtual twin): folds [0,6,5,4,4], LDE log2 [7,13,15,19], queries [89,13,7,6,5], query PoW [26,27,25,25,21], no folding / OOD PoW.",
    },
];

/// The entry for `input` at `level`; panics when no schedule was certified
/// for that shape, or when the circuit commits more polynomials than the
/// entry's ceiling.
pub(super) fn entry(level: SecurityLevel, input: &WhirInput) -> &'static EthproofsSoundcalcEntry {
    let entry = ENTRIES
        .iter()
        .find(|e| {
            e.level == level
                && e.message_size_log2 == input.message_size_log2
                && e.virtual_packing == input.virtual_packing
        })
        .unwrap_or_else(|| {
            panic!(
                "no EthproofsSoundnessCalc WHIR schedule has been certified for a 2^{} message with {} \
                 at {:?}; run example_configs/soundcalc/whir_schedule_search.py for the shape and add \
                 its entry to example_configs/ethproofs_soundcalc.rs",
                input.message_size_log2,
                if input.virtual_packing {
                    "virtual packing"
                } else {
                    "two values per column per leaf"
                },
                level
            )
        });
    let num_committed_polys = input.num_committed_polys.expect(
        "the EthproofsSoundnessCalc schedule is certified for a committed-polynomial ceiling: build \
         the config from the compiled circuit (WhirInput::new), not without a column count",
    );
    assert!(
        num_committed_polys <= entry.max_committed_polys,
        "{} committed polynomials exceed the {} ceiling the EthproofsSoundnessCalc schedule for a 2^{} \
         message was certified for; re-run the search with a larger ceiling",
        num_committed_polys,
        entry.max_committed_polys,
        input.message_size_log2
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

    #[test]
    fn every_entry_validates_and_records_its_certification() {
        for entry in ENTRIES {
            let input = input_for(entry, entry.max_committed_polys);
            let schedule = entry.schedule(0);
            let config = standard_config(entry.message_size_log2, entry.level, schedule.clone());
            config.validate_for_whir_message_size(entry.message_size_log2);
            assert_eq!(entry.certified_bits, entry.level.security_bits());
            assert_eq!(schedule.base_round.fold_log2, entry.fold_log2());
            assert_eq!(
                schedule.base_round.batching_pow_bits,
                Some(entry.batching_pow_bits())
            );
            assert_eq!(schedule.base_round.folding_pow_bits, 0);
            assert_eq!(schedule.base_round.num_queries, 174);
            assert_eq!(schedule.base_round.queries_pow_bits, 28);
            for (round, certified) in schedule.internal_rounds.iter().zip(entry.rounds) {
                assert_eq!(round.num_ood_samples, 1);
                assert!((24..=27).contains(&round.queries_pow_bits));
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
                    ProximityRegime::JohnsonBound { m: 3..=8 }
                ));
            }
            // every oracle domain fits BabyBear's two-adicity
            let mut poly_size_log2 = entry.message_size_log2 - entry.fold_log2();
            for round in schedule.internal_rounds.iter() {
                assert!(poly_size_log2 + round.lde_factor_log2 <= 27);
                poly_size_log2 -= round.folding_log2;
            }
            assert_eq!(
                whir_schedule(SoundnessMode::EthproofsSoundnessCalc, entry.level, &input),
                schedule
            );
            let notes = entry.render_notes(entry.level, &input);
            assert!(notes.contains("soundcalc"));
            assert!(notes.contains(&format!("**{} bits**", entry.certified_bits)));
            for round in entry.rounds {
                assert!(notes.contains(round.analysis.reason));
            }
        }
    }

    #[test]
    fn batching_pow_is_the_formula_at_the_ceiling() {
        // 123 - (message + 1) - ceil_log2(ceiling), lifted to 100
        let expected = [(23, 128, 8), (24, 128, 9), (22, 512, 9), (20, 1024, 8)];
        for (message, ceiling, bits) in expected {
            for entry in ENTRIES
                .iter()
                .filter(|e| e.message_size_log2 == message && e.max_committed_polys == ceiling)
            {
                assert_eq!(entry.batching_pow_bits(), bits, "2^{message}");
            }
        }
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
            let config = prover_config(
                SoundnessMode::EthproofsSoundnessCalc,
                level,
                trace,
                packing,
                Some(&columns),
            );
            assert_eq!(config.whir_schedule.base_round.num_queries, 174);
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
