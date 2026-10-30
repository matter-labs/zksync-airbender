//! Standalone L1 compression test program: takes the recursion pipeline's
//! stable point (1 unified + 1 blake proof) and compresses it all the way to
//! the single Proth120 packed L1 proof with ALL oracles in memory
//! (`program_prover::compression::compress_fixed_point_to_l1_in_mode`).
//!
//! Meant for large external machines (target shape: 192 cores + enough RAM to
//! materialize the ~2^31 packed RS codewords). Build for such a box with
//!
//! ```text
//! cargo build --release -p program_prover --features l1 \
//!     --target x86_64-unknown-linux-gnu --bin l1_compression
//! ```
//!
//! (cross-linking from a non-x86 host needs an x86_64-linux linker, e.g.
//! `cargo zigbuild`; building on the target machine itself also works), then
//!
//! ```text
//! l1_compression --bundle final_layer_0_bundle.json [--threads 192] [--out-dir .]
//! ```
//!
//! run from a repo checkout (the fsv verifier programs and the Proth120
//! circuit layout are read from the checkout by default). The input is a
//! versioned JSON proof bundle (`--bundle`, the format of
//! `program_prover::bundle::write_program_proof_bundle`), which carries its
//! soundness mode and is read in the expected mode. At this revision nothing
//! in the recursion flow writes that bundle (only tests call the writer), so
//! this program has no producer for its input. The retired `--proof` +
//! `--setups` pair of bincode caches is rejected without being read
//! (`L1InputError::LegacyBincodeUnsupported`). The supported L1 route is the
//! L1 stack's pipeline targets (`ProofTarget::{L1Feeder, L1}`) once that stack
//! is rebased. Outputs:
//! `unified_circuit_proof_proth120.json` +
//! `unified_circuit_proof_proth120_commitment_mod_aux_data.json` in the
//! output directory — the exact fixture pair the EVM tooling consumes.
//!
//! `--soundness-mode` (default `pessimistic-conjecture`) is the expected mode
//! of the input and of every layer. `ethproofs-soundcalc` is rejected before
//! any input is read: the L1 feeder/wrap/EVM profile exists only in
//! pessimistic_conjecture.

use full_statement_verifier::program_proof::ProgramProof;
use program_prover::bundle::{read_l1_input, read_program_proof_bundle, ProgramProofBundleV1};
use program_prover::compression::{compress_fixed_point_to_l1_in_mode, validate_l1_soundness_mode};
use prover::definitions::SoundnessMode;
use prover::gkr::prover::WhirOracleStorage;
use prover::worker::Worker;
use setups::Setups;
use std::path::PathBuf;

fn serialize_pretty_to_file<T: serde::Serialize>(el: &T, path: &PathBuf) {
    let mut dst =
        std::fs::File::create(path).unwrap_or_else(|e| panic!("create {}: {e}", path.display()));
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

/// The proof and setups to compress.
#[derive(Debug, PartialEq, Eq)]
enum Input {
    /// A versioned proof bundle.
    Bundle(PathBuf),
    /// The legacy zlib-compressed bincode pair.
    Legacy { proof: PathBuf, setups: PathBuf },
}

struct Args {
    input: Input,
    soundness_mode: SoundnessMode,
    fsv_dir: PathBuf,
    circuit: PathBuf,
    out_dir: PathBuf,
    threads: Option<usize>,
    use_caches: bool,
    feeder_recompute: bool,
}

const USAGE: &str = "usage: l1_compression (--bundle <file> | --proof <file> --setups <file>) \
    [--soundness-mode <pessimistic-conjecture|ethproofs-soundcalc=pessimistic-conjecture>] \
    [--fsv-dir <dir=tools/gkr_verifier/full_statement_verifiers>] \
    [--circuit <file=cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json>] \
    [--out-dir <dir=.>] [--threads <n=all cores>] [--no-caches] [--feeder-recompute]";

fn parse_args(args: impl IntoIterator<Item = String>) -> Args {
    let mut bundle = None;
    let mut proof = None;
    let mut setups = None;
    let mut soundness_mode = SoundnessMode::DEFAULT;
    let mut fsv_dir = PathBuf::from("tools/gkr_verifier/full_statement_verifiers");
    let mut circuit =
        PathBuf::from("cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json");
    let mut out_dir = PathBuf::from(".");
    let mut threads = None;
    let mut use_caches = true;
    let mut feeder_recompute = false;

    let mut it = args.into_iter();
    while let Some(arg) = it.next() {
        let mut value = |name: &str| -> String {
            it.next()
                .unwrap_or_else(|| panic!("{name} needs a value\n{USAGE}"))
        };
        match arg.as_str() {
            "--bundle" => bundle = Some(PathBuf::from(value("--bundle"))),
            "--proof" => proof = Some(PathBuf::from(value("--proof"))),
            "--setups" => setups = Some(PathBuf::from(value("--setups"))),
            "--soundness-mode" => {
                let name = value("--soundness-mode");
                soundness_mode = SoundnessMode::from_cli_name(&name)
                    .unwrap_or_else(|| panic!("unknown --soundness-mode `{name}`\n{USAGE}"))
            }
            "--fsv-dir" => fsv_dir = PathBuf::from(value("--fsv-dir")),
            "--circuit" => circuit = PathBuf::from(value("--circuit")),
            "--out-dir" => out_dir = PathBuf::from(value("--out-dir")),
            "--threads" => {
                threads = Some(
                    value("--threads")
                        .parse()
                        .expect("--threads must be a number"),
                )
            }
            "--no-caches" => use_caches = false,
            "--feeder-recompute" => feeder_recompute = true,
            "--help" | "-h" => {
                println!("{USAGE}");
                std::process::exit(0);
            }
            other => panic!("unknown argument `{other}`\n{USAGE}"),
        }
    }
    let input = match (bundle, proof, setups) {
        (Some(bundle), None, None) => Input::Bundle(bundle),
        (None, Some(proof), Some(setups)) => Input::Legacy { proof, setups },
        (Some(_), _, _) => panic!("--bundle replaces --proof and --setups\n{USAGE}"),
        (None, _, _) => panic!("give --bundle, or both --proof and --setups\n{USAGE}"),
    };
    Args {
        input,
        soundness_mode,
        fsv_dir,
        circuit,
        out_dir,
        threads,
        use_caches,
        feeder_recompute,
    }
}

/// The proof and setups to compress. An unsupported soundness mode is rejected before any
/// input is read; the legacy bincode pair is rejected without reading it.
fn load_input(args: &Args) -> Result<(ProgramProof, Setups), String> {
    validate_l1_soundness_mode(args.soundness_mode).map_err(|e| e.to_string())?;
    match &args.input {
        Input::Bundle(path) => read_program_proof_bundle(path, args.soundness_mode)
            .map(ProgramProofBundleV1::into_parts),
        Input::Legacy { proof, setups } => {
            read_l1_input(proof, setups, args.soundness_mode).map_err(|e| e.to_string())
        }
    }
}

fn main() {
    let args = parse_args(std::env::args().skip(1));
    let (proof, setups) = load_input(&args).unwrap_or_else(|e| panic!("l1_compression: {e}"));
    println!(
        "l1_compression: input {:?} ({} cycles executed), soundness mode {}, fsv dir {}",
        args.input,
        proof.executed_cycles(),
        args.soundness_mode.cli_name(),
        args.fsv_dir.display(),
    );

    let worker = match args.threads {
        Some(n) => Worker::new_with_num_threads(n),
        None => Worker::new(),
    };
    println!("l1_compression: using {} worker threads", worker.num_cores);

    // This program targets large machines, so the feeder stages default to
    // fully in-memory oracles (oracle recompute otherwise dominates), with
    // contiguous-buffer intermediate oracles; --feeder-recompute restores the
    // memory-light policy.
    let feeder_storage = if args.feeder_recompute {
        WhirOracleStorage::fully_recompute()
    } else {
        WhirOracleStorage::fully_in_memory_continuous()
    };

    // The GKR prover phases run recursion-heavy code on the calling thread;
    // give the whole compression a generous stack instead of relying on the
    // platform main-thread default.
    let result = std::thread::Builder::new()
        .name("l1_compression".to_string())
        .stack_size(1 << 26)
        .spawn(move || {
            compress_fixed_point_to_l1_in_mode(
                &proof,
                &setups,
                &args.fsv_dir,
                &args.circuit,
                args.use_caches,
                feeder_storage,
                &worker,
                args.soundness_mode,
            )
        })
        .expect("spawn compression thread")
        .join()
        .expect("compression must not panic")
        .unwrap_or_else(|e| panic!("l1_compression: {e}"));

    std::fs::create_dir_all(&args.out_dir).expect("create output directory");
    let proof_path = args.out_dir.join("unified_circuit_proof_proth120.json");
    let aux_path = args
        .out_dir
        .join("unified_circuit_proof_proth120_commitment_mod_aux_data.json");
    serialize_pretty_to_file(&result.l1_proof, &proof_path);
    serialize_pretty_to_file(&result.l1_operation_mode, &aux_path);
    println!(
        "l1_compression: wrote {} and {}",
        proof_path.display(),
        aux_path.display()
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(args: &[&str]) -> Args {
        parse_args(args.iter().map(|arg| arg.to_string()))
    }

    #[test]
    fn soundness_mode_defaults_to_pessimistic_conjecture() {
        let args = parse(&["--proof", "p.bin", "--setups", "s.bin"]);
        assert_eq!(args.soundness_mode, SoundnessMode::PessimisticConjecture);
        assert_eq!(
            args.input,
            Input::Legacy {
                proof: "p.bin".into(),
                setups: "s.bin".into()
            }
        );
    }

    #[test]
    fn every_mode_is_accepted_by_its_cli_name() {
        for mode in SoundnessMode::ALL {
            let args = parse(&["--bundle", "b.json", "--soundness-mode", mode.cli_name()]);
            assert_eq!(args.soundness_mode, *mode);
            assert_eq!(args.input, Input::Bundle("b.json".into()));
        }
    }

    #[test]
    #[should_panic(expected = "unknown --soundness-mode `ethproofs`")]
    fn other_spellings_are_rejected() {
        parse(&["--bundle", "b.json", "--soundness-mode", "ethproofs"]);
    }

    #[test]
    #[should_panic(expected = "--bundle replaces --proof and --setups")]
    fn bundle_excludes_the_legacy_pair() {
        parse(&["--bundle", "b.json", "--setups", "s.bin"]);
    }

    #[test]
    #[should_panic(expected = "give --bundle, or both --proof and --setups")]
    fn legacy_pair_needs_both_files() {
        parse(&["--proof", "p.bin"]);
    }

    #[test]
    fn unsupported_mode_is_rejected_before_the_input() {
        let args = parse(&[
            "--bundle",
            "missing.json",
            "--soundness-mode",
            "ethproofs-soundcalc",
        ]);
        let err = load_input(&args).err().unwrap();
        assert!(err.contains("(deferred product scope)"), "{err}");
    }

    #[test]
    fn legacy_pair_is_rejected_without_reading() {
        let args = parse(&["--proof", "missing.bin", "--setups", "missing.bin"]);
        assert_eq!(
            load_input(&args).err().unwrap(),
            program_prover::bundle::L1InputError::LegacyBincodeUnsupported.to_string()
        );
    }

    #[test]
    fn bundle_is_read_in_the_expected_mode() {
        let args = parse(&["--bundle", "missing.json"]);
        let err = load_input(&args).err().unwrap();
        assert!(err.starts_with("open missing.json"), "{err}");
    }
}
