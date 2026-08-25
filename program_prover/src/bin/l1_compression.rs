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
//! l1_compression --proof final_layer_0_proof_<tags>.bin \
//!     --setups final_layer_0_setups_<tags>.bin [--threads 192] [--out-dir .]
//! ```
//!
//! run from a repo checkout (the fsv verifier programs and the Proth120
//! circuit layout are read from the checkout by default). The proof/setups
//! inputs are the zlib-compressed bincode caches the `prover_examples`
//! recursion tests write. Outputs: `unified_circuit_proof_proth120.json` +
//! `unified_circuit_proof_proth120_commitment_mod_aux_data.json` in the
//! output directory — the exact fixture pair the EVM tooling consumes.

use full_statement_verifier::program_proof::ProgramProof;
use program_prover::compression::compress_fixed_point_to_l1;
use prover::gkr::prover::WhirOracleStorage;
use prover::worker::Worker;
use setups::Setups;
use std::io::Read;
use std::path::PathBuf;

fn deserialize_compressed_from_file<T: serde::de::DeserializeOwned>(path: &PathBuf) -> T {
    use flate2::read::ZlibDecoder;
    let mut src =
        std::fs::File::open(path).unwrap_or_else(|e| panic!("open {}: {e}", path.display()));
    let mut buffer = vec![];
    src.read_to_end(&mut buffer)
        .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let mut decoder = ZlibDecoder::new(&buffer[..]);
    let mut unpacked: Vec<u8> = vec![];
    decoder
        .read_to_end(&mut unpacked)
        .unwrap_or_else(|e| panic!("decompress {}: {e}", path.display()));
    bincode::deserialize_from(&unpacked[..])
        .unwrap_or_else(|e| panic!("deserialize {}: {e}", path.display()))
}

fn serialize_pretty_to_file<T: serde::Serialize>(el: &T, path: &PathBuf) {
    let mut dst =
        std::fs::File::create(path).unwrap_or_else(|e| panic!("create {}: {e}", path.display()));
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

struct Args {
    proof: PathBuf,
    setups: PathBuf,
    fsv_dir: PathBuf,
    circuit: PathBuf,
    out_dir: PathBuf,
    threads: Option<usize>,
    use_caches: bool,
    feeder_recompute: bool,
}

const USAGE: &str = "usage: l1_compression --proof <file> --setups <file> \
    [--fsv-dir <dir=tools/gkr_verifier>] \
    [--circuit <file=cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json>] \
    [--out-dir <dir=.>] [--threads <n=all cores>] [--no-caches] [--feeder-recompute]";

fn parse_args() -> Args {
    let mut proof = None;
    let mut setups = None;
    let mut fsv_dir = PathBuf::from("tools/gkr_verifier");
    let mut circuit =
        PathBuf::from("cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json");
    let mut out_dir = PathBuf::from(".");
    let mut threads = None;
    let mut use_caches = true;
    let mut feeder_recompute = false;

    let mut it = std::env::args().skip(1);
    while let Some(arg) = it.next() {
        let mut value = |name: &str| -> String {
            it.next()
                .unwrap_or_else(|| panic!("{name} needs a value\n{USAGE}"))
        };
        match arg.as_str() {
            "--proof" => proof = Some(PathBuf::from(value("--proof"))),
            "--setups" => setups = Some(PathBuf::from(value("--setups"))),
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
        proof: proof.unwrap_or_else(|| panic!("--proof is required\n{USAGE}")),
        setups: setups.unwrap_or_else(|| panic!("--setups is required\n{USAGE}")),
        fsv_dir,
        circuit,
        out_dir,
        threads,
        use_caches,
        feeder_recompute,
    }
}

fn main() {
    let args = parse_args();

    let proof: ProgramProof = deserialize_compressed_from_file(&args.proof);
    let setups: Setups = deserialize_compressed_from_file(&args.setups);
    println!(
        "l1_compression: input proof from {} ({} cycles executed), fsv dir {}",
        args.proof.display(),
        proof.executed_cycles(),
        args.fsv_dir.display(),
    );

    let worker = match args.threads {
        Some(n) => Worker::new_with_num_threads(n),
        None => Worker::new(),
    };
    println!("l1_compression: using {} worker threads", worker.num_cores);

    // This program targets large machines, so the feeder stages default to
    // fully in-memory oracles (oracle recompute otherwise dominates);
    // --feeder-recompute restores the memory-light policy.
    let feeder_storage = if args.feeder_recompute {
        WhirOracleStorage::fully_recompute()
    } else {
        WhirOracleStorage::fully_in_memory()
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
    serialize_pretty_to_file(&result.l1_commitment_mode, &aux_path);
    println!(
        "l1_compression: wrote {} and {}",
        proof_path.display(),
        aux_path.display()
    );
}
