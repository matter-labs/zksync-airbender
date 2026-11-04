//! Standalone L1 compression test program: takes the recursion pipeline's
//! stable point (1 unified + 1 blake proof) and compresses it all the way to
//! the single Proth120 packed L1 proof with ALL oracles in memory
//! (`program_prover::compression::compress_fixed_point_to_l1`).
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
//! soundness mode. The L1 feeder/wrap/EVM profile exists only in
//! pessimistic_conjecture, so the bundle is read as a pessimistic_conjecture
//! bundle and any other is refused. At this revision nothing in the recursion
//! flow writes that bundle (only tests call the writer), so this program has
//! no producer for its input. Outputs:
//! `unified_circuit_proof_proth120.json` +
//! `unified_circuit_proof_proth120_commitment_mod_aux_data.json` in the
//! output directory — the exact fixture pair the EVM tooling consumes.

use full_statement_verifier::program_proof::ProgramProof;
use program_prover::bundle::{read_program_proof_bundle, ProgramProofBundleV1};
use program_prover::compression::compress_fixed_point_to_l1;
use prover::definitions::SoundnessMode;
use prover::gkr::prover::WhirOracleStorage;
use prover::worker::Worker;
use setups::Setups;
use std::path::PathBuf;

fn serialize_pretty_to_file<T: serde::Serialize>(el: &T, path: &PathBuf) {
    let mut dst = std::io::BufWriter::new(
        std::fs::File::create(path).unwrap_or_else(|e| panic!("create {}: {e}", path.display())),
    );
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
    std::io::Write::flush(&mut dst).unwrap();
}

struct Args {
    /// The versioned proof bundle to compress.
    bundle: PathBuf,
    fsv_dir: PathBuf,
    circuit: PathBuf,
    out_dir: PathBuf,
    threads: Option<usize>,
    use_caches: bool,
    feeder_recompute: bool,
}

const USAGE: &str = "usage: l1_compression --bundle <file> \
    [--fsv-dir <dir=tools/gkr_verifier/full_statement_verifiers>] \
    [--circuit <file=cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json>] \
    [--out-dir <dir=.>] [--threads <n=all cores>] [--no-caches] [--feeder-recompute]";

fn parse_args(args: impl IntoIterator<Item = String>) -> Args {
    let mut bundle = None;
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
    Args {
        bundle: bundle.unwrap_or_else(|| panic!("give --bundle\n{USAGE}")),
        fsv_dir,
        circuit,
        out_dir,
        threads,
        use_caches,
        feeder_recompute,
    }
}

/// The proof and setups to compress: a pessimistic_conjecture bundle; one in another mode is
/// refused, not rebound.
fn load_input(args: &Args) -> Result<(ProgramProof, Setups), String> {
    read_program_proof_bundle(&args.bundle, SoundnessMode::PessimisticConjecture)
        .map(ProgramProofBundleV1::into_parts)
}

fn main() {
    let args = parse_args(std::env::args().skip(1));
    let (proof, setups) = load_input(&args).unwrap_or_else(|e| panic!("l1_compression: {e}"));
    println!(
        "l1_compression: input {} ({} cycles executed), fsv dir {}",
        args.bundle.display(),
        proof.executed_cycles(),
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
            compress_fixed_point_to_l1(
                &proof,
                &setups,
                &args.fsv_dir,
                &args.circuit,
                args.use_caches,
                feeder_storage,
                &worker,
            )
        })
        .expect("spawn compression thread")
        .join()
        .expect("compression must not panic");

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
    use prover::definitions::ProvingSelection;

    fn parse(args: &[&str]) -> Args {
        parse_args(args.iter().map(|arg| arg.to_string()))
    }

    #[test]
    fn bundle_and_defaults_are_parsed() {
        let args = parse(&["--bundle", "b.json"]);
        assert_eq!(args.bundle, PathBuf::from("b.json"));
        assert_eq!(
            args.fsv_dir,
            PathBuf::from("tools/gkr_verifier/full_statement_verifiers")
        );
        assert!(args.use_caches && !args.feeder_recompute && args.threads.is_none());
    }

    #[test]
    #[should_panic(expected = "give --bundle")]
    fn bundle_is_required() {
        parse(&[]);
    }

    #[test]
    #[should_panic(expected = "unknown argument `--soundness-mode`")]
    fn soundness_mode_is_not_an_option() {
        parse(&[
            "--bundle",
            "b.json",
            "--soundness-mode",
            "pessimistic-conjecture",
        ]);
    }

    #[test]
    #[should_panic(expected = "unknown argument `--proof`")]
    fn bincode_pair_is_not_an_input() {
        parse(&["--proof", "p.bin", "--setups", "s.bin"]);
    }

    #[test]
    fn missing_bundle_is_reported() {
        let err = load_input(&parse(&["--bundle", "missing.json"]))
            .err()
            .unwrap();
        assert!(err.starts_with("open missing.json"), "{err}");
    }

    /// An ethproofs bundle is refused by its mode binding, not read as pessimistic.
    #[test]
    fn ethproofs_bundle_is_refused() {
        let dir = std::env::temp_dir().join(format!("l1-compression-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("ethproofs.json");
        let proof = ProgramProof {
            riscv_proofs: Default::default(),
            compiled_riscv_circuits: Default::default(),
            inits_and_teardown_proofs: Vec::new(),
            inits_and_teardowns_circuit: None,
            delegation_proofs: Default::default(),
            compiled_delegation_circuits: Default::default(),
            register_final_values: Vec::new(),
            final_pc: 0,
            final_timestamp: 4,
            end_params: [0; 8],
            recursion_chain_preimage: None,
            recursion_chain_hash: None,
            pow_challenge: 0,
            num_it_circuits: None,
        };
        program_prover::bundle::write_program_proof_bundle(
            &path,
            ProvingSelection {
                soundness_mode: SoundnessMode::EthproofsSoundnessCalc,
                ..ProvingSelection::default()
            },
            &proof,
            &Setups::new(),
        )
        .unwrap();
        let err = load_input(&parse(&["--bundle", path.to_str().unwrap()]))
            .err()
            .unwrap();
        std::fs::remove_dir_all(&dir).unwrap();
        assert_eq!(
            err,
            "SoundnessModeMismatch: expected PessimisticConjecture, bundle is EthproofsSoundnessCalc"
        );
    }
}
