//! Refreshes the `tools/verifier/*.setup.json` snapshots from the embedded recursion
//! verifier binaries.
//!
//! Each snapshot is the `UnrolledProgramSetup` that
//! `execution_utils::verifier_binaries::derive_recursion_setup` computes for one of the
//! four embedded binaries (80/100-bit security, unrolled/unified layer): minutes of CPU
//! work per binary that `verifier_binaries::recursion_setup` serves precomputed at
//! runtime. `tools/reproduce/reproduce.sh` runs this right after rebuilding the binaries,
//! and the `check_verifiers` CI job fails on the resulting diff if a snapshot was stale.
//!
//! Every snapshot is re-derived and compared against the file on disk; only stale files
//! are rewritten. Exits 0 either way, reporting what changed.
//!
//! ```text
//! cargo run --profile cli -p execution_utils --features verifier_binaries \
//!     --bin regenerate_recursion_setups
//! ```

use execution_utils::unrolled::UnrolledProgramSetup;
use execution_utils::verifier_binaries::{derive_recursion_setup, recursion_setup_snapshot_path};
use execution_utils::RecursionLayer;
use std::time::Instant;
use verifier_common::SecurityModel;

fn main() {
    let mut rewritten = Vec::new();
    for security in [SecurityModel::Security80, SecurityModel::Security100] {
        for recursion in [RecursionLayer::Unrolled, RecursionLayer::Unified] {
            let path = recursion_setup_snapshot_path(security, recursion);
            let start = Instant::now();
            let derived = derive_recursion_setup(security, recursion);
            let on_disk: Option<UnrolledProgramSetup> = std::fs::read_to_string(&path)
                .ok()
                .and_then(|json| serde_json::from_str(&json).ok());
            let status = if on_disk.as_ref() == Some(&derived) {
                "up to date"
            } else {
                let mut json = serde_json::to_string_pretty(&derived).unwrap();
                json.push('\n');
                std::fs::write(&path, json)
                    .unwrap_or_else(|e| panic!("cannot write {}: {e}", path.display()));
                rewritten.push(path.clone());
                "REWRITTEN"
            };
            println!(
                "{status}: {} ({security:?} {recursion:?}, derived in {:.1?}, end_params {:?})",
                path.display(),
                start.elapsed(),
                derived.end_params
            );
        }
    }
    if rewritten.is_empty() {
        println!("all recursion setup snapshots match the embedded binaries");
    } else {
        println!(
            "{} snapshot(s) were stale and have been rewritten; commit them alongside the binaries",
            rewritten.len()
        );
    }
}
