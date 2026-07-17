//! WHIR verifier generation from the prover's `WhirSchedule` + the packing factor.
//!
//! The WHIR proving configuration (fold/query/PoW schedule, base rate, merkle cap) is NOT
//! encoded in the circuit artifact — it must be supplied by the caller as the same
//! `prover::gkr::prover::WhirSchedule` the prover used. Together with `pack_log2` (from the GKR
//! `CommitmentMode`) and the artifact's column widths, that fully determines every WHIR verifier
//! parameter, so GKR and WHIR are driven from one source and cannot drift.
//!
//! This module derives all of those parameters ([`WhirGenConfig`]) and renders the per-round
//! schedule Yul that `whir.sol` used to hardcode as a `switch VARIANT` block. The RS-codeword
//! domain generators `GEN`/`GEN_INV` are computed from the Proth120 field (a primitive
//! `2^codeword_log2`-th root of unity), not hand-supplied.

use field::Proth120;
use prover::gkr::prover::WhirSchedule;

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
    pub nbcaps: usize,        // number of base-oracle merkle caps (witness, setup) = 2
    pub gen: u128,            // primitive 2^codeword_log2-th root of unity (RS domain generator)
    pub gen_inv: u128,        // its inverse
}

impl WhirGenConfig {
    /// `num_memwit` = merged memory+witness base width, `num_setup` = generic-lookup setup width
    /// (both pre-packing column counts, from the artifact).
    pub fn derive(
        schedule: &WhirSchedule,
        pack_log2: usize,
        trace_len_log2: usize,
        num_memwit: usize,
        num_setup: usize,
    ) -> Self {
        let folds = schedule.whir_steps_schedule.clone();
        let queries = schedule.whir_queries_schedule.clone();
        let pow_bits = schedule.whir_pow_schedule.clone();
        let num_rounds = folds.len();
        assert_eq!(queries.len(), num_rounds, "WHIR query schedule length != fold schedule length");
        assert_eq!(pow_bits.len(), num_rounds, "WHIR pow schedule length != fold schedule length");
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
        let pack = 1usize << pack_log2;
        let merged_mw = num_memwit.div_ceil(pack);
        let setup_merged = num_setup.div_ceil(pack);

        assert!(
            codeword_log2 <= 120,
            "codeword_log2 {codeword_log2} exceeds the Proth120 two-adicity (120)"
        );
        let gen = Proth120::TWO_ADICITY_GENERATORS[codeword_log2].to_u128();
        let gen_inv = Proth120::TWO_ADICITY_GENERATORS_INVERSED[codeword_log2].to_u128();

        Self {
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
            nbcaps: 2,
            gen,
            gen_inv,
        }
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
            let qib = self.codeword_log2 - fold;
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
}
