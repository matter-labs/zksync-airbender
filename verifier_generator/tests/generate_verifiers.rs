use std::io::Write;

use prover::field::baby_bear::base::BabyBearField;
use prover::gkr::prover_config::SoundnessMode;
use verifier_common::test_circuits::{verifier_dir_name, CircuitData, SecurityLevel, ALL_CIRCUITS};
use verifier_generator::field_wrapper::FieldWrapper;
use verifier_generator::gkr::GKRGeneratedFiles;
use verifier_generator::{gkr, utils, whir, DefaultBabyBearField};

const LEVELS_TO_GENERATE: &[SecurityLevel] = &[SecurityLevel::Sec100];

fn write_and_fmt(path: &str, content: &proc_macro2::TokenStream) {
    let content = quote::quote! {
        #![allow(
            dead_code,
            unused_imports,
            unused_unsafe,
            unused_assignments,
            clippy::needless_range_loop,
            clippy::too_many_arguments,
            clippy::manual_div_ceil,
            clippy::borrow_deref_ref,
            clippy::identity_op,
            clippy::missing_safety_doc,
            clippy::duplicate_mod,
            clippy::large_const_arrays
        )]
        #content
    };
    let mut dst = std::fs::File::create(path).unwrap();
    dst.write_all(content.to_string().as_bytes()).unwrap();
    drop(dst);
    std::process::Command::new("rustfmt")
        .arg(path)
        .status()
        .ok();
}

fn generate_common<MW: FieldWrapper>() {
    let max_fold_steps = ALL_CIRCUITS
        .iter()
        .flat_map(|c| {
            LEVELS_TO_GENERATE.iter().flat_map(move |&level| {
                SoundnessMode::ALL
                    .iter()
                    .flat_map(move |&mode| c.whir_schedule_for_mode(level, mode).fold_steps())
            })
        })
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
    dir: &str,
) -> GKRGeneratedFiles {
    let compiled_circuit = circuit.compiled_circuit();

    let files = gkr::generate_gkr_inlined::<MW>(&compiled_circuit, prover_config);

    write_and_fmt(&format!("{}/constants.rs", dir), &files.constants);

    files
}

fn generate_whir_verifier<MW: FieldWrapper>(
    prover_config: &prover::gkr::prover_config::ProverConfig,
    dir: &str,
    gkr_files: &GKRGeneratedFiles,
) {
    let whir_schedule = &prover_config.whir_schedule;

    // Every WHIR-side size derives from the committed (packed) column length,
    // `trace_len_log2 + pack_log2`.
    let message_size_log2 = gkr_files.whir_message_size_log2;
    let whir_initial = whir::generate_whir_initial_round::<MW>(
        whir_schedule,
        &gkr_files.oracles,
        message_size_log2,
    );
    let whir_internal = whir::generate_whir_internal_rounds::<MW>(whir_schedule, message_size_log2);
    let whir_final = whir::generate_whir_final_round::<MW>(whir_schedule, message_size_log2);

    // Compute max hash buf size across all WHIR rounds (padded to 16-word boundary)
    let initial_vpf = whir_schedule.base_values_per_leaf();
    let initial_hbs = gkr_files
        .oracles
        .values()
        .map(|o| o.num_columns * initial_vpf)
        .max()
        .unwrap_or(0)
        .div_ceil(16)
        * 16;
    let fold_steps = whir_schedule.fold_steps();
    let num_whir_rounds = fold_steps.len();
    let internal_hbs = if num_whir_rounds > 2 {
        let max_fold = *fold_steps[1..num_whir_rounds - 1].iter().max().unwrap();
        ((1usize << max_fold) * 4).div_ceil(16) * 16
    } else {
        0
    };
    let final_hbs = ((1usize << fold_steps[num_whir_rounds - 1]) * 4).div_ceil(16) * 16;
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

/// The verifiers of `circuit` for every soundness mode at `level`, generated into
/// `verifier/src/generated/<circuit>/<mode>/`. Their GKR verifier must be identical in every
/// mode; it is written once, to `<circuit>/gkr.rs`, before the `mod.rs` files that include it.
fn generate_standard_verifiers_for_circuit<MW: FieldWrapper<BaseField = BabyBearField>>(
    circuit: &CircuitData,
    level: SecurityLevel,
) {
    let parts: Vec<_> = SoundnessMode::ALL
        .iter()
        .map(|&mode| {
            let prover_config = circuit.prover_config_for_mode(level, mode);
            let (dir, gkr) =
                generate_verifier_parts::<MW>(circuit, prover_config, verifier_dir_name(mode));
            (mode, dir, gkr)
        })
        .collect();
    let (first_mode, _, gkr) = &parts[0];
    for (mode, _, other) in &parts[1..] {
        assert!(
            other.to_string() == gkr.to_string(),
            "{}: the {mode:?} GKR verifier differs from the {first_mode:?} one and cannot be shared",
            circuit.name
        );
    }
    write_and_fmt(&format!("{}/gkr.rs", circuit.generated_dir()), gkr);
    for (_, dir, _) in &parts {
        write_mod_rs::<MW>(
            dir,
            quote::quote! {
                #[path = "../gkr.rs"]
                pub mod gkr;
            },
        );
    }
}

/// The verifier of `circuit` for an EXPLICIT prover config with its own GKR verifier, generated
/// into `verifier/src/generated/<circuit>/<dir_suffix>/`.
fn generate_verifier_for_circuit_with_config<MW: FieldWrapper<BaseField = BabyBearField>>(
    circuit: &CircuitData,
    prover_config: &prover::gkr::prover_config::ProverConfig,
    dir_suffix: &str,
) {
    let (dir, gkr) = generate_verifier_parts::<MW>(circuit, prover_config, dir_suffix);
    write_and_fmt(&format!("{dir}/gkr.rs"), &gkr);
    write_mod_rs::<MW>(&dir, quote::quote! { pub mod gkr; });
}

/// Writes the constants and WHIR verifier of `circuit` for `prover_config` into
/// `verifier/src/generated/<circuit>/<dir_suffix>/` and returns that directory and the GKR
/// verifier, which the caller places.
fn generate_verifier_parts<MW: FieldWrapper<BaseField = BabyBearField>>(
    circuit: &CircuitData,
    prover_config: &prover::gkr::prover_config::ProverConfig,
    dir_suffix: &str,
) -> (String, proc_macro2::TokenStream) {
    ensure_common();
    let dir = format!("{}/{}", circuit.generated_dir(), dir_suffix);
    std::fs::create_dir_all(&dir).unwrap();
    let gkr_files = generate_gkr_verifier::<MW>(circuit, prover_config, &dir);
    generate_whir_verifier::<MW>(prover_config, &dir, &gkr_files);
    (dir, gkr_files.gkr)
}

fn write_mod_rs<MW: FieldWrapper<BaseField = BabyBearField>>(
    dir: &str,
    gkr_mod: proc_macro2::TokenStream,
) {
    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    let field_use_stmts = MW::field_use_statements();

    let mod_rs = quote::quote! {
        pub mod constants;
        #gkr_mod
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
            { constants::CLAIM_POINT_CAPACITY },
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
/// of two). Generated into `.../unified_reduced_machine/pessimistic_conjecture_l1_feeder`
/// (a pessimistic-conjecture variant; no soundcalc twin has been designed).
#[test]
fn unified_reduced_machine_l1_feeder() {
    let circuit = ALL_CIRCUITS
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
        "pessimistic_conjecture_l1_feeder",
    );
}

macro_rules! generate_circuit_tests {
    ($($name:ident; $prod_path:expr),* $(,)?) => {
        $(
            #[test]
            fn $name() {
                let circuit = ALL_CIRCUITS.iter().find(|c| c.name == stringify!($name)).unwrap();
                for level in LEVELS_TO_GENERATE {
                    generate_standard_verifiers_for_circuit::<DefaultBabyBearField>(circuit, *level);
                }
            }
        )*
    };
}
verifier_common::gkr_circuits!(generate_circuit_tests);
