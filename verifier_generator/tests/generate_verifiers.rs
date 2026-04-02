use std::io::Write;

use verifier_common::test_circuits::{CircuitData, CIRCUITS};
use verifier_generator::gkr::GKRGeneratedFiles;
use verifier_generator::mersenne_wrapper::MersenneWrapper;
use verifier_generator::{gkr, utils, whir, DefaultBabyBearField};

fn write_and_fmt(path: &str, content: &proc_macro2::TokenStream) {
    let mut dst = std::fs::File::create(path).unwrap();
    dst.write_all(content.to_string().as_bytes()).unwrap();
    drop(dst);
    std::process::Command::new("rustfmt")
        .arg(path)
        .status()
        .ok();
}

fn generate_common<MW: MersenneWrapper>() {
    let max_fold_steps = CIRCUITS
        .iter()
        .flat_map(|c| &c.whir_schedule().whir_steps_schedule)
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
        use core::mem::MaybeUninit;
        use ::verifier_common::field_ops;
        use ::verifier_common::field::{Field, FieldExtension, PrimeField};
        use ::verifier_common::blake2s_u32::{
            AlignedArray64, DelegatedBlake2sState,
            BLAKE2S_DIGEST_SIZE_U32_WORDS,
        };
        use ::verifier_common::non_determinism_source::NonDeterminismSource;
        use ::verifier_common::transcript::{Blake2sTranscript, Seed};
        use ::verifier_common::gkr::GKRVerificationError;
        use ::verifier_common::lazy_vec::LazyVec;
        #field_use_stmts

        pub const EXT_DEGREE: usize =
            <#quartic_struct as FieldExtension<#field_struct>>::DEGREE;
        // 64 u32 words = 8 Blake2s digests. Sufficient for all current draws:
        // single field element = 4 words → padded to 8, gamma = same.
        pub const DRAW_BUF_CAPACITY: usize = 64;

        #transcript_fns
        #sumcheck_fns
        #gkr_fns
        #whir_fns
    };

    let common_dir = CircuitData::common_generated_dir();
    std::fs::create_dir_all(&common_dir).unwrap();
    write_and_fmt(&format!("{}/mod.rs", common_dir), &common);
}

fn generate_gkr_verifier<MW: MersenneWrapper>(
    circuit: &CircuitData,
    dir: &str,
) -> GKRGeneratedFiles {
    let compiled_circuit = circuit.compiled_circuit();
    let proof = circuit.proof();

    let files = gkr::generate_gkr_inlined::<MW, _, _, _>(
        &compiled_circuit,
        &proof,
        4,
        circuit.whir_schedule(),
    );

    write_and_fmt(&format!("{}/constants.rs", dir), &files.constants);
    write_and_fmt(&format!("{}/gkr.rs", dir), &files.gkr);

    files
}

fn generate_whir_verifier<MW: MersenneWrapper>(
    circuit: &CircuitData,
    dir: &str,
    gkr_files: &GKRGeneratedFiles,
) {
    let whir_schedule = circuit.whir_schedule();

    let whir_initial = whir::generate_whir_inlined::<MW>(
        whir_schedule,
        gkr_files.num_mem_oracle_cols,
        gkr_files.num_wit_oracle_cols,
        gkr_files.num_setup_oracle_cols,
        gkr_files.trace_len_log2,
    );
    let whir_internal =
        whir::generate_whir_internal_rounds::<MW>(whir_schedule, gkr_files.trace_len_log2);
    let whir_final = whir::generate_whir_final_round::<MW>(whir_schedule, gkr_files.trace_len_log2);

    // Compute max hash buf size across all WHIR rounds (padded to 16-word boundary)
    let initial_vpf = 1usize << whir_schedule.whir_steps_schedule[0];
    let initial_hbs = ([
        gkr_files.num_mem_oracle_cols,
        gkr_files.num_wit_oracle_cols,
        gkr_files.num_setup_oracle_cols,
    ]
    .iter()
    .map(|&c| c * initial_vpf)
    .max()
    .unwrap()
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

fn generate_verifier_for_circuit<MW: MersenneWrapper>(circuit: &CircuitData) {
    let dir = circuit.generated_dir();
    std::fs::create_dir_all(&dir).unwrap();

    let gkr_files = generate_gkr_verifier::<MW>(circuit, &dir);
    generate_whir_verifier::<MW>(circuit, &dir, &gkr_files);

    let mod_rs = quote::quote! {
        pub mod constants;
        pub mod gkr;
        pub mod whir;
        #[path = "../common/mod.rs"]
        pub mod common;
        pub use gkr::verify_gkr;

        use ::verifier_common::non_determinism_source::NonDeterminismSource;
        use ::verifier_common::gkr::GKRVerificationError;

        #[derive(Clone, Debug)]
        #[allow(dead_code)]
        pub enum VerificationError {
            Gkr(GKRVerificationError),
            Whir(common::WhirVerificationError),
        }

        #[allow(unused_braces, unused_mut, unused_variables)]
        pub fn verify<I: NonDeterminismSource>() -> Result<(), VerificationError> {
            let gkr_output = verify_gkr::<I>()
                .map_err(VerificationError::Gkr)?;
            let mut seed = gkr_output.whir_transcript_seed;
            let mut hasher = ::verifier_common::blake2s_u32::DelegatedBlake2sState::new();
            whir::verify_whir::<I>(
                &mut hasher,
                &mut seed,
                gkr_output.whir_batching_challenge,
                &gkr_output.setup_cap,
                &gkr_output.memory_cap,
                &gkr_output.witness_cap,
            ).map_err(VerificationError::Whir)
        }
    };
    write_and_fmt(&format!("{}/mod.rs", dir), &mod_rs);
}

#[test]
fn generate_verifiers() {
    use rayon::prelude::*;

    generate_common::<DefaultBabyBearField>();

    CIRCUITS.par_iter().for_each(|circuit| {
        generate_verifier_for_circuit::<DefaultBabyBearField>(circuit);
    });
}
