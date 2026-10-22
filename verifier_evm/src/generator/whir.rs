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
//! is generated rather than hand-placed. The RS-codeword domain generators `GEN`/`GEN_INV` are
//! computed from the Proth120 field (a primitive `2^codeword_log2`-th root of unity), not
//! hand-supplied.

use super::Lit;
use field::Proth120;
use prover::gkr::prover_config::ProverConfig;

/// Every WHIR verifier parameter, derived from `(WhirSchedule, pack_log2, trace_len_log2, widths)`.
#[derive(Clone, Debug)]
pub struct WhirGenConfig {
    pub num_rounds: usize,
    pub folds: Vec<usize>,   // whir_steps_schedule
    pub queries: Vec<usize>, // whir_queries_schedule
    pub pow_bits: Vec<u32>,  // whir_pow_schedule
    pub cap_size: usize,
    pub cap_log2: usize,
    pub pack_log2: usize,
    pub base_lde_bits: usize, // log2(base_lde_factor)
    pub message_log2: usize,  // trace_len_log2 + pack_log2
    pub codeword_log2: usize, // message_log2 + base_lde_bits
    pub rfin: usize,          // final-poly log2 = message_log2 - Σ folds
    pub nz: usize,            // WHIR evaluation-point coords = message_log2
    pub merged_mw: usize,     // ceil(num_memwit / 2^pack_log2)  (merged mem+wit base columns)
    pub setup_merged: usize,  // ceil(num_setup  / 2^pack_log2)  (merged setup base columns)
    pub gcount: usize,        // gamma-batched base columns + 1 = merged_mw + setup_merged + 1
    pub gen: u128,            // primitive 2^codeword_log2-th root of unity (RS domain generator)
    pub gen_inv: u128,        // its inverse
}

impl WhirGenConfig {
    /// `num_memwit` = merged memory+witness base width, `num_setup` = generic-lookup setup width
    /// (both pre-packing column counts, from the artifact).
    pub fn derive(prover_config: &ProverConfig, num_memwit: usize, num_setup: usize) -> Self {
        let schedule = &prover_config.whir_schedule;
        let pack_log2 = prover_config.pack_log2;
        let trace_len_log2 = prover_config.trace_len_log2;
        let folds = schedule.whir_steps_schedule.clone();
        let queries = schedule.whir_queries_schedule.clone();
        let pow_bits = schedule.whir_pow_schedule.clone();
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
            schedule.base_lde_factor.is_power_of_two() && schedule.base_lde_factor > 0,
            "WHIR base_lde_factor {} is not a power of two",
            schedule.base_lde_factor
        );

        let cap_log2 = schedule.cap_size.trailing_zeros() as usize;
        let base_lde_bits = schedule.base_lde_factor.trailing_zeros() as usize;
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
        assert_eq!(schedule.whir_steps_lde_factors.len(), num_rounds - 1);
        let mut lde_bits = base_lde_bits;
        for (fold, lde) in folds.iter().zip(&schedule.whir_steps_lde_factors) {
            lde_bits += fold;
            assert_eq!(
                *lde,
                1usize << lde_bits,
                "EVM WHIR requires a constant codeword domain"
            );
        }
        let pack = 1usize << pack_log2;
        let merged_mw = num_memwit.div_ceil(pack);
        let setup_merged = num_setup.div_ceil(pack);

        assert!(
            codeword_log2 <= 120,
            "codeword_log2 {codeword_log2} exceeds the Proth120 two-adicity (120)"
        );
        let gen = Proth120::TWO_ADICITY_GENERATORS[codeword_log2].to_u128();
        let gen_inv = Proth120::TWO_ADICITY_GENERATORS_INVERSED[codeword_log2].to_u128();

        let cfg = Self {
            num_rounds,
            folds,
            queries,
            pow_bits,
            cap_size: schedule.cap_size,
            cap_log2,
            pack_log2,
            base_lde_bits,
            message_log2,
            codeword_log2,
            rfin,
            nz: message_log2,
            merged_mw,
            setup_merged,
            gcount: merged_mw + setup_merged + 1,
            gen,
            gen_inv,
        };
        // every round's query-index bit count must leave room for the cap levels
        for r in 0..num_rounds {
            assert!(
                cfg.qib(r) >= cap_log2,
                "WHIR round {r}: query index bits {} < cap_log2 {cap_log2}",
                cfg.qib(r)
            );
        }
        cfg
    }

    /// Query-index bits of round `r`'s oracle tree: `codeword_log2 - fold_r`.
    fn qib(&self, r: usize) -> usize {
        self.codeword_log2 - self.folds[r]
    }

    /// Final-polynomial Horner evaluation with eight coefficients per cursor/loop update.
    /// The fixed remainder uses literal offsets; coefficients stay in the existing MONO region.
    pub fn final_horner_yul(&self) -> String {
        const MONO: &str = "__TEMPLATE_WHIR_MONO_PTR";
        let n = 1usize << self.rfin;
        let tail = (n - 1) % 8;
        let mut out = format!("        function horner_{n}(x) -> ev {{\n");
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
    /// `qib = codeword_log2 - fold`, `cb = base_lde_bits + Σ folds[..r]`.
    pub fn schedule_switch_yul(&self) -> String {
        let mut out = String::from("            switch r\n");
        let mut prefolds = 0usize;
        for r in 0..self.num_rounds {
            let fold = self.folds[r];
            let q = self.queries[r];
            let pow = self.pow_bits[r];
            let vp = 1usize << fold;
            let qib = self.qib(r);
            let cb = self.base_lde_bits + prefolds;
            prefolds += fold;
            let selector = if r + 1 == self.num_rounds {
                "default".to_string()
            } else {
                format!("case {r}")
            };
            out.push_str(&format!(
                "            {selector} {{ fold := {fold} q := {q} pow_bits := {pow} qib := {qib} vp := {vp} cb := {cb} }}\n"
            ));
        }
        out
    }

    /// The WHIR half's memory regions — `(constant name in whir.sol, size in bytes as a
    /// readable expression)` in allocation order — every size derived from the schedule,
    /// mirroring exactly how the Yul in whir.sol indexes each region (documented per entry).
    /// The generator lays them out contiguously above the GKR heap and assigns the resulting
    /// absolute offsets to the `__TEMPLATE_WHIR_*` pointer constants.
    pub fn memory_regions(&self) -> Vec<(&'static str, Lit)> {
        let max_fold = *self.folds.iter().max().unwrap();
        let max_q = *self.queries.iter().max().unwrap();
        let cap = Lit::pow2(self.cap_log2 as u128);
        let cap_bytes = cap.mul(&Lit::num(32));
        let w32 = Lit::num(32);
        let slot = |n: usize| Lit::num(n as u128).mul(&w32);
        // POW entries (push_pow, 96 B each): every internal round pushes 1 ood point + 1 per
        // query; the final round pushes none.
        let numpow: usize = (0..self.num_rounds - 1).map(|r| self.queries[r] + 1).sum();
        // LEAF scratch: round 0 hashes (merged_mw + setup_merged) columns × vp0/2 words of
        // the base oracles; a later round r hashes vp_r/2 words of the intermediate oracle.
        let leaf_words = (0..self.num_rounds)
            .map(|r| {
                let words = (1usize << self.folds[r]) / 2;
                if r == 0 {
                    (self.merged_mw + self.setup_merged) * words
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
        // seed word + the largest in-place absorb: the intermediate cap (cap·32 B), or the
        // 48-B sumcheck poly / 16-B ood value / 8-B PoW nonce (all < 64 B)
        let seed = if cap_bytes.value >= 64 {
            w32.add(&cap_bytes)
        } else {
            w32.add(&Lit::num(64))
        };
        vec![
            ("SEED_PTR", seed),
            ("Z_PTR", slot(self.nz)),
            ("POW_PTR", Lit::num(numpow as u128).mul(&Lit::num(96))),
            ("ACC_PREF_PTR", w32.clone()),
            ("GAMMA_PTR", slot(self.gcount)),
            ("FOLD_CH_PTR", slot(max_fold)),
            ("HPO_PTR", Lit::pow2(max_fold as u128 - 1).mul(&w32)),
            ("FBUF_PTR", Lit::pow2(max_fold as u128).mul(&w32)),
            ("LEAF_PTR", slot(leaf_words)),
            ("REG_CD", w32.clone()),
            ("REG_CLAIM", w32.clone()),
            ("REG_NUMPOW", w32.clone()),
            ("REG_ZIOFF", w32.clone()),
            ("REG_CC", w32.clone()),
            ("REG_CURDELIN", w32.clone()),
            ("HANDOFF_BATCHING_PTR", w32.clone()),
            ("BCAP0_PTR", cap_bytes.clone()),
            ("BCAP1_PTR", cap_bytes.clone()),
            ("QCAP_PTR", cap_bytes.clone()),
            ("NCAP_PTR", cap_bytes.clone()),
            ("QIDX_BUF_PTR", slot(max_q)),
            ("DRAW_BUF_PTR", slot(draw_words)),
            // do_final: 2^rfin monomials, then the tail absorb (32 + nmono·16 B) and the
            // halving-fold scratch (nmono words) share FEVAL
            ("MONO_PTR", nmono.mul(&w32)),
            ("FEVAL_PTR", w32.add(&nmono.mul(&w32))),
        ]
    }
}
