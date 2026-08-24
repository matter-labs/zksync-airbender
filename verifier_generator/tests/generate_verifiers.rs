use std::io::Write;

use prover::field::baby_bear::base::BabyBearField;
use verifier_common::test_circuits::{CircuitData, SecurityLevel, CIRCUITS};
use verifier_generator::field_wrapper::FieldWrapper;
use verifier_generator::gkr::GKRGeneratedFiles;
use verifier_generator::{gkr, utils, whir, DefaultBabyBearField};

const LEVELS_TO_GENERATE: &[SecurityLevel] = &[SecurityLevel::Sec100];

fn write_and_fmt(path: &str, content: &proc_macro2::TokenStream) {
    let mut dst = std::fs::File::create(path).unwrap();
    dst.write_all(content.to_string().as_bytes()).unwrap();
    drop(dst);
    std::process::Command::new("rustfmt")
        .arg(path)
        .status()
        .ok();
}

fn generate_common<MW: FieldWrapper>() {
    let max_fold_steps = CIRCUITS
        .iter()
        .flat_map(|c| {
            LEVELS_TO_GENERATE
                .iter()
                .flat_map(move |&level| c.whir_schedule_for(level).whir_steps_schedule.iter())
        })
        .copied()
        .max()
        .unwrap();

    let field_use_stmts = MW::field_use_statements();
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();

    let transcript_fns = utils::transcript::generate_transcript_helpers::<MW>();
    let sumcheck_fns = utils::sumcheck::generate_sumcheck_helpers::<MW>();
    let gkr_fns = gkr::generate_gkr_common::<MW>();
    let whir_fns = whir::generate_whir_common::<MW>(max_fold_steps);

    let common = quote::quote! {
        use ::verifier_common::field_ops;
        use ::verifier_common::field::{Field, FieldExtension, PrimeField};
        use ::verifier_common::blake2s_u32::{DelegatedBlake2sState, BLAKE2S_DIGEST_SIZE_U32_WORDS};
        use ::verifier_common::non_determinism_source::NonDeterminismSource;
        use ::verifier_common::errors::ErrorCreator;
        use ::verifier_common::structs::{CommitBuf, TranscriptState};
        use ::verifier_common::lazy_vec::LazyVec;
        pub use ::verifier_common::structs::{ext_from_nds, ext_from_raw_words};
        pub use ::verifier_common::SUMCHECK_POLY_COEFFS;
        #field_use_stmts

        pub const EXT_DEGREE: usize =
            <#quartic_struct as FieldExtension<#field_struct>>::DEGREE;

        #transcript_fns
        #sumcheck_fns
        #gkr_fns
        #whir_fns
    };

    let common_dir = CircuitData::common_generated_dir();
    std::fs::create_dir_all(&common_dir).unwrap();
    write_and_fmt(&format!("{}/mod.rs", common_dir), &common);
}

fn generate_gkr_verifier<MW: FieldWrapper<BaseField = BabyBearField>>(
    circuit: &CircuitData,
    prover_config: &prover::gkr::prover_config::ProverConfig,
    commitment_mode: &prover::gkr::prover::CommitmentMode,
    dir: &str,
) -> GKRGeneratedFiles {
    let compiled_circuit = circuit.compiled_circuit();

    let files = gkr::generate_gkr_inlined_for_commitment_mode::<MW>(
        &compiled_circuit,
        prover_config.sumcheck_explicit_output_size_log_2,
        &prover_config.whir_schedule,
        prover_config.security_level.security_bits() as u32,
        commitment_mode,
    );

    write_and_fmt(&format!("{}/constants.rs", dir), &files.constants);
    write_and_fmt(&format!("{}/gkr.rs", dir), &files.gkr);

    files
}

fn generate_whir_verifier<MW: FieldWrapper>(
    prover_config: &prover::gkr::prover_config::ProverConfig,
    dir: &str,
    gkr_files: &GKRGeneratedFiles,
) {
    let whir_schedule = &prover_config.whir_schedule;

    let whir_initial = whir::generate_whir_initial_round::<MW>(
        whir_schedule,
        &gkr_files.oracles,
        gkr_files.trace_len_log2,
    );
    let whir_internal =
        whir::generate_whir_internal_rounds::<MW>(whir_schedule, gkr_files.trace_len_log2);
    let whir_final = whir::generate_whir_final_round::<MW>(whir_schedule, gkr_files.trace_len_log2);

    // Compute max hash buf size across all WHIR rounds (padded to 16-word boundary)
    let initial_vpf = 1usize << whir_schedule.whir_steps_schedule[0];
    let initial_hbs = (gkr_files
        .oracles
        .iter()
        .map(|(_, o)| o.num_columns * initial_vpf)
        .max()
        .unwrap_or(0)
        + 15)
        / 16
        * 16;
    let num_whir_rounds = whir_schedule.whir_steps_schedule.len();
    let internal_hbs = if num_whir_rounds > 2 {
        let max_fold = *whir_schedule.whir_steps_schedule[1..num_whir_rounds - 1]
            .iter()
            .max()
            .unwrap();
        ((1usize << max_fold) * 4 + 15) / 16 * 16
    } else {
        0
    };
    let final_hbs =
        ((1usize << whir_schedule.whir_steps_schedule[num_whir_rounds - 1]) * 4 + 15) / 16 * 16;
    let whir_hash_buf_size = initial_hbs.max(internal_hbs).max(final_hbs);

    let whir_verify = whir::generate_whir_verify::<MW>(whir_hash_buf_size);
    let whir_code = quote::quote! {
        #whir_initial
        #whir_internal
        #whir_final
        #whir_verify
    };
    write_and_fmt(&format!("{}/whir.rs", dir), &whir_code);
}

static COMMON_ONCE: std::sync::Once = std::sync::Once::new();

fn ensure_common() {
    COMMON_ONCE.call_once(|| {
        generate_common::<DefaultBabyBearField>();
    });
}

fn generate_verifier_for_circuit<MW: FieldWrapper<BaseField = BabyBearField>>(
    circuit: &CircuitData,
    level: SecurityLevel,
) {
    let prover_config = circuit.prover_config_for(level);
    generate_verifier_for_circuit_with_config::<MW>(
        circuit,
        prover_config,
        &prover::gkr::prover::CommitmentMode::SeparateMemoryAndWitness,
        level.dir_suffix(),
    );
}

/// Like [`generate_verifier_for_circuit`] but with an EXPLICIT prover config,
/// base [`CommitmentMode`] and output dir suffix — for special-purpose
/// verifier variants whose LDE factor / WHIR schedule / base-commitment shape
/// differ from the standard per-level configs (e.g. the high-LDE, merged-tree
/// "L1 feeder" unified verifier).
///
/// [`CommitmentMode`]: prover::gkr::prover::CommitmentMode
fn generate_verifier_for_circuit_with_config<MW: FieldWrapper<BaseField = BabyBearField>>(
    circuit: &CircuitData,
    prover_config: &prover::gkr::prover_config::ProverConfig,
    commitment_mode: &prover::gkr::prover::CommitmentMode,
    dir_suffix: &str,
) {
    ensure_common();

    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    let field_use_stmts = MW::field_use_statements();

    let dir = format!("{}/{}", circuit.generated_dir(), dir_suffix);
    std::fs::create_dir_all(&dir).unwrap();

    let gkr_files = generate_gkr_verifier::<MW>(circuit, prover_config, commitment_mode, &dir);
    generate_whir_verifier::<MW>(prover_config, &dir, &gkr_files);

    let mod_rs = quote::quote! {
        pub mod constants;
        pub mod gkr;
        pub mod whir;
        #[path = "../../common/mod.rs"]
        pub mod common;

        use ::verifier_common::GKRExternalChallenges;
        use ::verifier_common::non_determinism_source::NonDeterminismSource;
        use ::verifier_common::errors::ErrorCreator;
        #field_use_stmts

        pub fn verify<I: NonDeterminismSource<#field_struct>, E: ErrorCreator>(
            external_challenges: &GKRExternalChallenges<#field_struct, #quartic_struct>,
            nd_source: &mut I,
        ) -> Result<constants::ConcreteVerifierOutput, E::Error> {
            ::verifier_common::verify_impl::<
            I,
            E,
            #field_struct,
            #quartic_struct,
            { constants::INIT_AND_TEARDOWN_SETS },
            { constants::EXTERNAL_CHALLENGES_FLATTENED_SIZE },
            { constants::CAP_SIZE },
            { constants::NUM_MEMORY_COMMITS },
            { constants::NUM_WITNESS_COMMITS },
            { constants::NUM_SETUP_COMMITS },
            { constants::PADDING_WORDS },
            { constants::GKR_ROUNDS },
            { constants::GKR_ADDRS },
            gkr::VerifierImplementation,
        >(external_challenges, nd_source)
        }
    };
    write_and_fmt(&format!("{}/mod.rs", dir), &mod_rs);
}

/// High-LDE "L1 feeder" unified verifier: same circuit and 100-bit target as
/// `unified_reduced_machine` at sec_100, but every oracle domain sits at
/// BabyBear's two-adicity cap (base LDE 16; round-0 queries 87 -> 21), the
/// schedule terminates at a plain-text 2^3 tail, and the base commitment is
/// the MERGED memory+witness tree (one Merkle path per round-0 query instead
/// of two). Generated into `.../unified_reduced_machine/sec_100_l1_feeder`.
#[test]
fn unified_reduced_machine_l1_feeder() {
    let circuit = CIRCUITS
        .iter()
        .find(|c| c.name == "unified_reduced_machine")
        .unwrap();
    let prover_config = prover::gkr::prover_config::example_configs::l1_feeder_config_for_2_23();
    assert_eq!(
        circuit.compiled_circuit().trace_len.trailing_zeros(),
        23,
        "the L1 feeder config is computed for the 2^23 unified circuit"
    );
    generate_verifier_for_circuit_with_config::<DefaultBabyBearField>(
        circuit,
        &prover_config,
        &prover::gkr::prover::CommitmentMode::MergedMemoryAndWitness,
        "sec_100_l1_feeder",
    );
}

macro_rules! generate_circuit_tests {
    ($($name:ident; $prod_path:expr),* $(,)?) => {
        $(
            #[test]
            fn $name() {
                let circuit = CIRCUITS.iter().find(|c| c.name == stringify!($name)).unwrap();
                for level in LEVELS_TO_GENERATE {
                    generate_verifier_for_circuit::<DefaultBabyBearField>(circuit, *level);
                }
            }
        )*
    };
}
verifier_common::gkr_circuits!(generate_circuit_tests);
