//! Capture or verify the committed continuation-binder golden.
//!
//! `--write` re-serializes the snapshot of every layer of the 12 committed
//! `*_layout_gkr.json` layouts; `--check` fails if the committed bytes disagree.

use gpu_gkr::backward::{
    build_continuation_golden, continuation_golden_path, decode_golden, encode_golden,
};

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    let path = continuation_golden_path();
    let entries = build_continuation_golden();
    let bytes = encode_golden(&entries);

    match mode.as_str() {
        "--write" => {
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent).expect("creating the artifacts directory");
            }
            std::fs::write(&path, &bytes).expect("writing the golden");
            println!(
                "wrote {} ({} entries, {} bytes)",
                path.display(),
                entries.len(),
                bytes.len()
            );
        }
        "--check" => {
            let committed = std::fs::read(&path).unwrap_or_else(|error| {
                panic!("reading {}: {error} (run --write first)", path.display())
            });
            if committed == bytes {
                println!(
                    "{} is current ({} entries, {} bytes)",
                    path.display(),
                    entries.len(),
                    bytes.len()
                );
                return;
            }
            let expected = decode_golden(&committed).expect("decoding the committed golden");
            report_first_difference(&expected, &entries);
            eprintln!(
                "{} is stale: {} committed bytes vs {} recomputed",
                path.display(),
                committed.len(),
                bytes.len()
            );
            std::process::exit(1);
        }
        other => {
            eprintln!(
                "usage: generate_windowed_continuation_golden --write|--check (got {other:?})"
            );
            std::process::exit(2);
        }
    }
}

fn report_first_difference(
    expected: &[gpu_gkr::backward::GoldenEntry],
    actual: &[gpu_gkr::backward::GoldenEntry],
) {
    if expected.len() != actual.len() {
        eprintln!(
            "entry count changed: committed {} vs recomputed {}",
            expected.len(),
            actual.len()
        );
    }
    for (committed, recomputed) in expected.iter().zip(actual) {
        if committed == recomputed {
            continue;
        }
        eprintln!(
            "first divergence at {} layer {}",
            committed.layout, committed.dto.layer
        );
        for (want, got) in committed.dto.rounds.iter().zip(&recomputed.dto.rounds) {
            if want != got {
                eprintln!("  round {} differs", want.absolute_round);
                eprintln!("  committed: {want:?}");
                eprintln!("  recomputed: {got:?}");
                break;
            }
        }
        if committed.dto.final_evaluations != recomputed.dto.final_evaluations {
            eprintln!(
                "  final evaluations differ: {:?} vs {:?}",
                committed.dto.final_evaluations, recomputed.dto.final_evaluations
            );
        }
        break;
    }
}
