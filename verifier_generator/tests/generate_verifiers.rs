use std::io::Write;

use prover::field::baby_bear::base::BabyBearField;
use prover::gkr::prover_config::SoundnessMode;
use verifier_common::test_circuits::{verifier_dir_name, CircuitData, SecurityLevel, CIRCUITS};
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
    let max_fold_steps = CIRCUITS
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
    write_and_fmt(&format!("{}/gkr.rs", dir), &files.gkr);

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

/// The verifier of `circuit` for the config of `mode` at `level`, generated
/// into `verifier/src/generated/<circuit>/<mode>/`.
fn generate_verifier_for_circuit<MW: FieldWrapper<BaseField = BabyBearField>>(
    circuit: &CircuitData,
    level: SecurityLevel,
    mode: SoundnessMode,
) {
    let prover_config = circuit.prover_config_for_mode(level, mode);
    generate_verifier_for_circuit_with_config::<MW>(
        circuit,
        prover_config,
        verifier_dir_name(mode),
    );
}

/// Like [`generate_verifier_for_circuit`] but with an EXPLICIT prover config,
/// output dir suffix — for special-purpose
/// verifier variants whose LDE factor / WHIR schedule / base-commitment shape
/// differ from the standard per-level configs (e.g. the high-LDE, merged-tree
/// "L1 feeder" unified verifier).
///
fn generate_verifier_for_circuit_with_config<MW: FieldWrapper<BaseField = BabyBearField>>(
    circuit: &CircuitData,
    prover_config: &prover::gkr::prover_config::ProverConfig,
    dir_suffix: &str,
) {
    ensure_common();

    let field_struct = MW::field_struct();
    let quartic_struct = MW::quartic_struct();
    let field_use_stmts = MW::field_use_statements();

    let dir = format!("{}/{}", circuit.generated_dir(), dir_suffix);
    std::fs::create_dir_all(&dir).unwrap();

    let gkr_files = generate_gkr_verifier::<MW>(circuit, prover_config, &dir);
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
            { constants::CLAIM_POINT_CAPACITY },
            { constants::GKR_ADDRS },
            gkr::VerifierImplementation,
        >(external_challenges, nd_source)
        }
    };
    write_and_fmt(&format!("{}/mod.rs", dir), &mod_rs);
}

/// The L1 feeder unified verifier: the 2^22 `unified_reduced_machine_2_22`
/// circuit under `l1_feeder_config_for_2_22` (every oracle domain at
/// BabyBear's two-adicity cap, base LDE 16, cap 16, a plain-text 2^3 tail)
/// with the MERGED memory+witness base commitment. Generated into
/// `.../unified_reduced_machine_2_22/pessimistic_conjecture_l1_feeder`; the circuit is not
/// a `gkr_circuits!` catalogue entry, so no standard verifier exists for it.
#[test]
fn unified_reduced_machine_l1_feeder() {
    let circuit = CircuitData::new(
        "unified_reduced_machine_2_22",
        "../circuit_defs/unrolled_circuits/unified_reduced_machine_2_22",
    );
    let prover_config = prover::gkr::prover_config::example_configs::l1_feeder_config_for_2_22();
    let compiled = circuit.compiled_circuit();
    assert_eq!(
        compiled.trace_len.trailing_zeros() as usize,
        prover_config.trace_len_log2,
        "the L1 feeder config is computed for the 2^22 unified circuit"
    );
    generate_verifier_for_circuit_with_config::<DefaultBabyBearField>(
        &circuit,
        &prover_config,
        "pessimistic_conjecture_l1_feeder",
    );
}

/// ONE-OFF: generate a verifier for `ONE_OFF_CIRCUIT` from the prover config
/// file `ONE_OFF_CONFIG` (e.g. the `test_proofs/<circuit>_<suffix>_prover_config.json`
/// a `GKR_BASE_PACKING_OVERRIDE` prover run writes) into
/// `verifier/src/generated/<circuit>/<ONE_OFF_DIR_SUFFIX>/`.
#[test]
#[ignore = "one-off experiments; driven by ONE_OFF_CIRCUIT / ONE_OFF_CONFIG / ONE_OFF_DIR_SUFFIX"]
fn one_off_from_prover_config_file() {
    let name = std::env::var("ONE_OFF_CIRCUIT").expect("ONE_OFF_CIRCUIT");
    let config_path = std::env::var("ONE_OFF_CONFIG").expect("ONE_OFF_CONFIG");
    let dir_suffix = std::env::var("ONE_OFF_DIR_SUFFIX").expect("ONE_OFF_DIR_SUFFIX");
    let circuit = CIRCUITS
        .iter()
        .find(|c| c.name == name)
        .expect("registered circuit");
    let file = std::fs::File::open(&config_path).unwrap_or_else(|e| panic!("{config_path}: {e}"));
    let prover_config: prover::gkr::prover_config::ProverConfig =
        serde_json::from_reader(std::io::BufReader::new(file)).unwrap();
    assert_eq!(
        circuit.compiled_circuit().trace_len.trailing_zeros() as usize,
        prover_config.trace_len_log2,
    );
    prover_config.validate_for_whir_message_size(prover_config.whir_message_size_log2());
    generate_verifier_for_circuit_with_config::<DefaultBabyBearField>(
        circuit,
        &prover_config,
        &dir_suffix,
    );
}

/// The 2^23 L1 feeder unified verifier (profile A): the 2^23
/// `unified_reduced_machine` circuit under `l1_feeder_a_config_for_2_23`
/// (base LDE 4, cap 4, every later oracle domain at 2^27, a plain-text 2^3
/// tail) with the MERGED memory+witness base commitment. Generated into
/// `.../unified_reduced_machine/pessimistic_conjecture_l1_feeder_a`, beside the standard
/// verifier of the same circuit.
#[test]
fn unified_reduced_machine_l1_feeder_a() {
    let circuit = CircuitData::new(
        "unified_reduced_machine",
        "../circuit_defs/unrolled_circuits/unified_reduced_machine",
    );
    let prover_config = prover::gkr::prover_config::example_configs::l1_feeder_a_config_for_2_23();
    let compiled = circuit.compiled_circuit();
    assert_eq!(
        compiled.trace_len.trailing_zeros() as usize,
        prover_config.trace_len_log2,
        "profile A is computed for the 2^23 unified circuit"
    );
    generate_verifier_for_circuit_with_config::<DefaultBabyBearField>(
        &circuit,
        &prover_config,
        "pessimistic_conjecture_l1_feeder_a",
    );
}

macro_rules! generate_circuit_tests {
    ($($name:ident; $prod_path:expr),* $(,)?) => {
        $(
            #[test]
            fn $name() {
                let circuit = CIRCUITS.iter().find(|c| c.name == stringify!($name)).unwrap();
                for level in LEVELS_TO_GENERATE {
                    for mode in SoundnessMode::ALL {
                        generate_verifier_for_circuit::<DefaultBabyBearField>(circuit, *level, *mode);
                    }
                }
            }
        )*
    };
}
verifier_common::gkr_circuits!(generate_circuit_tests);
