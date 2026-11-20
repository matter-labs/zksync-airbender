//! WHIR verifier generation from the prover's `WhirSchedule` + the packing factor.
//!
//! The WHIR proving configuration (fold/query/PoW schedule, base rate, merkle cap) is NOT
//! encoded in the circuit artifact — it must be supplied by the caller as the same
//! `prover::gkr::prover::WhirSchedule` the prover used. Together with `pack_log2` (the prover's
//! `ProverConfig::pack_log2`) and the artifact's column widths, that fully determines every WHIR verifier
//! parameter, so GKR and WHIR are driven from one source and cannot drift.
//!
//! This module derives all of those parameters ([`WhirGenConfig`]), renders the per-round
//! schedule Yul that `whir.sol` used to hardcode as a `switch VARIANT` block, and sizes every
//! WHIR memory region from the schedule ([`WhirGenConfig::memory_regions`]) so the memory map
//! is generated rather than hand-placed. Each oracle's RS-codeword root is derived from its
//! evaluation domain. The base oracle also uses its inverse for coset folding.

use super::{Lit, MAX_NONCE_POW_BITS};
use crate::encoding::params::{oracle_geometry, OracleGeometry};
use field::Proth120;
use prover::gkr::prover_config::ProverConfig;

/// Every WHIR verifier parameter, derived from `(WhirSchedule, pack_log2, trace_len_log2, widths)`.
#[derive(Clone, Debug)]
pub struct WhirGenConfig {
    pub num_rounds: usize,
    pub folds: Vec<usize>,   // whir_steps_schedule
    pub queries: Vec<usize>, // whir_queries_schedule
    pub pow_bits: Vec<u32>,  // whir_pow_schedule
    pub folding_pow_bits: Vec<u32>,
    /// OOD difficulty for each intermediate oracle (committed by rounds 0..N-1).
    pub ood_pow_bits: Vec<u32>,
    pub cap_size: usize,
    pub cap_log2: usize,
    pub pack_log2: usize,
    pub base_lde_bits: usize, // log2(base_lde_factor)
    pub message_log2: usize,  // trace_len_log2 + pack_log2
    pub codeword_log2: usize, // base message_log2 + base_lde_bits
    oracles: Vec<OracleGeometry>,
    pub rfin: usize,         // final-poly log2 = message_log2 - Σ folds
    pub nz: usize,           // WHIR evaluation-point coords = message_log2
    pub merged_mw: usize,    // ceil(num_memwit / 2^pack_log2)  (merged mem+wit base columns)
    pub setup_merged: usize, // ceil(num_setup  / 2^pack_log2)  (merged setup base columns)
    pub gcount: usize,       // gamma-batched base columns = merged_mw + setup_merged
    pub gen: u128,           // primitive 2^codeword_log2-th root of unity (RS domain generator)
    pub gen_inv: u128,       // its inverse
}

impl WhirGenConfig {
    /// `num_memwit` = merged memory+witness base width, `num_setup` = generic-lookup setup width
    /// (both pre-packing column counts, from the artifact).
    pub fn derive(prover_config: &ProverConfig, num_memwit: usize, num_setup: usize) -> Self {
        let schedule = &prover_config.whir_schedule;
        assert!(
            !schedule.is_virtual_packing(),
            "the compressed calldata requires a folded base round"
        );
        for round in &schedule.internal_rounds {
            assert_eq!(
                round.num_ood_samples, 1,
                "the compressed calldata encodes exactly one OOD sample"
            );
        }
        let pack_log2 = prover_config.pack_log2();
        let trace_len_log2 = prover_config.trace_len_log2;
        let folds = schedule.fold_steps();
        let queries = schedule.queries_per_round();
        let pow_bits = schedule.queries_pow_bits_per_round();
        let folding_pow_bits: Vec<_> = core::iter::once(schedule.base_round.folding_pow_bits)
            .chain(schedule.internal_rounds.iter().map(|r| r.folding_pow_bits))
            .collect();
        let ood_pow_bits: Vec<_> = schedule
            .internal_rounds
            .iter()
            .map(|r| r.ood_pow_bits)
            .collect();
        // Limit claimed difficulty to the width of the calldata nonce.
        for (gate, difficulties) in [
            ("query", &pow_bits),
            ("folding", &folding_pow_bits),
            ("OOD", &ood_pow_bits),
        ] {
            for &bits in difficulties {
                assert!(
                    bits <= MAX_NONCE_POW_BITS,
                    "{gate} PoW {bits} exceeds the {MAX_NONCE_POW_BITS}-bit calldata nonce width"
                );
            }
        }
        let num_rounds = folds.len();
        assert!(num_rounds >= 2, "WHIR schedule needs at least 2 rounds");
        assert_eq!(
            queries.len(),
            num_rounds,
            "WHIR query schedule length != fold schedule length"
        );
        assert_eq!(
            pow_bits.len(),
            num_rounds,
            "WHIR pow schedule length != fold schedule length"
        );
        assert!(
            folds.iter().all(|&f| f >= 1),
            "every WHIR round must fold at least one variable"
        );
        assert!(
            schedule.cap_size.is_power_of_two() && schedule.cap_size > 0,
            "WHIR cap_size {} is not a power of two",
            schedule.cap_size
        );
        assert!(
            schedule.base_lde_factor().is_power_of_two() && schedule.base_lde_factor() > 0,
            "WHIR base_lde_factor {} is not a power of two",
            schedule.base_lde_factor()
        );

        let cap_log2 = schedule.cap_size.trailing_zeros() as usize;
        let base_lde_bits = schedule.base_lde_factor_log2();
        let message_log2 = trace_len_log2 + pack_log2;
        let codeword_log2 = message_log2 + base_lde_bits;
        let total_folds: usize = folds.iter().sum();
        assert!(
            total_folds <= message_log2,
            "WHIR folds sum {total_folds} exceeds message size log2 {message_log2}"
        );
        let rfin = message_log2 - total_folds;
        assert!(
            rfin > 0,
            "WHIR final polynomial must contain at least two monomials"
        );
        let oracles = oracle_geometry(prover_config);
        assert!(
            oracles.iter().all(|o| o.domain_log2 <= 120),
            "WHIR domain exceeds Proth120 two-adicity"
        );
        let pack = 1usize << pack_log2;
        let merged_mw = num_memwit.div_ceil(pack);
        let setup_merged = num_setup.div_ceil(pack);

        let gen = Proth120::TWO_ADICITY_GENERATORS[codeword_log2].to_u128();
        let gen_inv = Proth120::TWO_ADICITY_GENERATORS_INVERSED[codeword_log2].to_u128();

        let cfg = Self {
            num_rounds,
            folds,
            queries,
            pow_bits,
            folding_pow_bits,
            ood_pow_bits,
            cap_size: schedule.cap_size,
            cap_log2,
            pack_log2,
            base_lde_bits,
            message_log2,
            codeword_log2,
            oracles,
            rfin,
            nz: message_log2,
            merged_mw,
            setup_merged,
            gcount: merged_mw + setup_merged,
            gen,
            gen_inv,
        };
        // every round's query-index bit count must leave room for the cap levels
        for r in 0..num_rounds {
            assert!(cfg.qib(r) <= 32, "WHIR query index exceeds 32 bits");
            assert!(
                cfg.qib(r) >= cap_log2,
                "WHIR round {r}: query index bits {} < cap_log2 {cap_log2}",
                cfg.qib(r)
            );
        }
        cfg
    }

    /// Query-index bits of the oracle opened in round `r`.
    pub fn qib(&self, r: usize) -> usize {
        self.oracles[r].query_index_bits
    }

    pub(super) fn variable_domains(&self) -> bool {
        self.oracles
            .iter()
            .any(|oracle| oracle.domain_log2 != self.codeword_log2)
    }

    pub(super) fn oracle_root(&self, r: usize) -> u128 {
        Proth120::TWO_ADICITY_GENERATORS[self.oracles[r].domain_log2].to_u128()
    }

    /// Select the codeword root for a query's oracle on variable-domain schedules.
    pub(super) fn oracle_roots_yul(&self) -> String {
        use std::fmt::Write as _;
        let mut out =
            String::from("        function oracle_root(r) -> root {\n            switch r\n");
        for r in 0..self.num_rounds - 1 {
            writeln!(
                &mut out,
                "            case {r} {{ root := 0x{:032X} }}",
                self.oracle_root(r)
            )
            .unwrap();
        }
        writeln!(
            &mut out,
            "            default {{ root := 0x{:032X} }}",
            self.oracle_root(self.num_rounds - 1)
        )
        .unwrap();
        out.push_str("        }\n");
        out
    }

    /// Final-polynomial Horner evaluation with eight coefficients per cursor/loop update.
    /// The fixed remainder uses literal offsets; coefficients stay in the existing MONO region.
    pub fn final_horner_yul(&self) -> String {
        const MONO: &str = "__TEMPLATE_WHIR_MONO_PTR";
        let n = 1usize << self.rfin;
        let tail = (n - 1) % 8;
        let last_byte = (n - 1) * 32;
        let tail_byte = tail * 32;
        let mut out = format!("        // {n} monomial coefficients, one 32-byte word each; highest coefficient at byte {last_byte}.\n        // Process blocks of 8 words (256 bytes), offsets 224/192/160/128/96/64/32/0;\n        // stop at byte {tail_byte}, then finish the {tail} remaining low coefficients.\n        function horner_{n}(x) -> ev {{\n");
        if n > 8 {
            out.push_str(&format!(
                "            let ptr := add({MONO}, {})\n\
                 \x20           let end := add({MONO}, {})\n\
                 \x20           ev := mload(ptr)\n\
                 \x20           for {{ }} gt(ptr, end) {{ }} {{\n\
                 \x20               ptr := sub(ptr, 256)\n",
                (n - 1) * 32,
                tail * 32,
            ));
            for offset in (0..8).rev().map(|i| i * 32) {
                let addr = if offset == 0 {
                    "ptr".to_string()
                } else {
                    format!("add(ptr, {offset})")
                };
                out.push_str(&format!(
                    "                ev := addmod(mulmod(ev, x, P), mload({addr}), P)\n"
                ));
            }
            out.push_str("            }\n");
        } else {
            out.push_str(&format!(
                "            ev := mload(add({MONO}, {}))\n",
                (n - 1) * 32
            ));
        }
        for offset in (0..tail).rev().map(|i| i * 32) {
            let addr = if offset == 0 {
                MONO.to_string()
            } else {
                format!("add({MONO}, {offset})")
            };
            out.push_str(&format!(
                "            ev := addmod(mulmod(ev, x, P), mload({addr}), P)\n"
            ));
        }
        out.push_str("        }\n");
        out
    }

    /// Render the per-round `switch r { case i { fold q pow_bits qib vp cb } … }` block that
    /// replaces the `// __WHIR_SCHEDULE_SWITCH__` marker. Per round: `vp = 2^fold`,
    /// `qib = domain_log2 - fold`, and `cb = lde_log2` for the current oracle.
    pub fn schedule_switch_yul(&self) -> String {
        let mut out = String::from("            switch r\n");
        for r in 0..self.num_rounds {
            let fold = self.folds[r];
            let q = self.queries[r];
            let pow = self.pow_bits[r];
            let fold_pow = self.folding_pow_bits[r];
            let ood_pow = self.ood_pow_bits.get(r).copied().unwrap_or(0);
            let vp = 1usize << fold;
            let qib = self.qib(r);
            let cb = self.oracles[r].lde_log2;
            let selector = if r + 1 == self.num_rounds {
                "default".to_string()
            } else {
                format!("case {r}")
            };
            out.push_str(&format!(
                "            // Round {r}: fold {fold} variables at {fold_pow} PoW bits; {q} queries at {pow} PoW bits, OOD PoW {ood_pow}; {qib}-bit indices, {vp} values per leaf, {cb} coset bits.\n            {selector} {{ fold := {fold} q := {q} pow_bits := {pow} fold_pow_bits := {fold_pow} ood_pow_bits := {ood_pow} qib := {qib} vp := {vp} cb := {cb} }}\n"
            ));
        }
        out
    }

    /// The WHIR half's memory regions — `(constant name in whir.sol, size in bytes as a
    /// readable expression)` in allocation order — every size derived from the schedule,
    /// mirroring exactly how the Yul in whir.sol indexes each region (documented per entry).
    /// The generator lays them out contiguously above the GKR heap and assigns the resulting
    /// absolute offsets to the `__TEMPLATE_WHIR_*` pointer constants.
    pub fn memory_regions(&self) -> Vec<(&'static str, Lit, &'static str)> {
        let max_fold = *self.folds.iter().max().unwrap();
        let max_q = *self.queries.iter().max().unwrap();
        let cap = Lit::pow2(self.cap_log2 as u128);
        let cap_bytes = cap.mul(&Lit::num(32));
        let w32 = Lit::num(32);
        let slot = |n: usize| Lit::num(n as u128).mul(&w32);
        // Constraint entries (push_pow, 96 B each): every internal round pushes one OOD point + 1 per
        // query; the final round pushes none.
        let numpow: usize = (0..self.num_rounds - 1).map(|r| self.queries[r] + 1).sum();
        // LEAF scratch: round 0 hashes each base oracle's leaf separately (merged_mw or
        // setup_merged columns × vp0/2 words); a later round r hashes vp_r/2 words of the
        // intermediate oracle.
        let leaf_words = (0..self.num_rounds)
            .map(|r| {
                let words = (1usize << self.folds[r]) / 2;
                if r == 0 {
                    self.merged_mw.max(self.setup_merged) * words
                } else {
                    words
                }
            })
            .max()
            .unwrap()
            .max(1);
        // DRAW_BUF: `draw_queries(q, qib)` squeezes `padded` LE u32 words, one per 32-byte
        // slot, with padded = next_multiple_of(ceil(q·qib / 32) + 1, 8).
        let draw_words = (0..self.num_rounds)
            .map(|r| {
                let num_bits = self.queries[r] * self.qib(r);
                let nrw = num_bits.div_ceil(32);
                (nrw + 1).next_multiple_of(8)
            })
            .max()
            .unwrap();
        let nmono = Lit::pow2(self.rfin as u128);
        // Seed plus the largest in-place absorb: the cap, three u128 sumcheck
        // coefficients, the single OOD value, or the PoW nonce.
        let absorb_bytes = cap_bytes.value.max(64);
        let seed = w32.add(&Lit::num(absorb_bytes));
        vec![
            ("SEED_PTR", seed, "WHIR transcript seed and absorb scratch"),
            ("Z_PTR", slot(self.nz), "Opening-point coordinates"),
            (
                "POW_PTR",
                Lit::num(numpow as u128).mul(&Lit::num(96)),
                "Deferred OOD and query constraints",
            ),
            ("ACC_PREF_PTR", w32.clone(), "Accumulated prefix product"),
            (
                "GAMMA_PTR",
                slot(self.gcount),
                "Base-column batching challenges",
            ),
            ("FOLD_CH_PTR", slot(max_fold), "Round folding challenges"),
            // only round 0 (the coset fold) reads the high-power offsets
            (
                "HPO_PTR",
                Lit::pow2(self.folds[0] as u128 - 1).mul(&w32),
                "Round-0 high-power offsets",
            ),
            (
                "FBUF_PTR",
                Lit::pow2(max_fold as u128).mul(&w32),
                "Folded leaf scratch",
            ),
            ("LEAF_PTR", slot(leaf_words), "Merkle leaf hashing scratch"),
            ("REG_CD", w32.clone(), "Calldata cursor"),
            ("REG_CLAIM", w32.clone(), "Current opening claim"),
            ("REG_NUMPOW", w32.clone(), "Deferred constraint count"),
            ("REG_ZIOFF", w32.clone(), "Opening coordinate cursor"),
            ("REG_CC", w32.clone(), "Current claim correction"),
            (
                "REG_CURDELIN",
                w32.clone(),
                "Current delinearization challenge",
            ),
            ("BCAP0_PTR", cap_bytes.clone(), "Base oracle cap"),
            ("QCAP_PTR", cap_bytes.clone(), "Current oracle cap"),
            ("NCAP_PTR", cap_bytes.clone(), "Next oracle cap"),
            ("QIDX_BUF_PTR", slot(max_q), "Query indices"),
            (
                "DRAW_BUF_PTR",
                slot(draw_words),
                "Transcript query-draw scratch",
            ),
            // do_final: 2^rfin monomials, then the tail absorb (32 + nmono·16 B) and the
            // halving-fold scratch (nmono words) share FEVAL
            ("MONO_PTR", nmono.mul(&w32), "Final polynomial monomials"),
            // rfin > 0, so nmono ≥ 2 and the tail absorb (32 + nmono·16 B) fits in the nmono-word
            // fold scratch
            (
                "FEVAL_PTR",
                nmono.mul(&w32),
                "Final polynomial absorb and fold scratch",
            ),
        ]
    }
}
