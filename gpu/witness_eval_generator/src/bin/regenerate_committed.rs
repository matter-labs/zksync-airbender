//! Regenerate every committed `witness_generation_fn.cuh` from its committed
//! SSA/layout inputs, in place. Run this after an intentional change to the
//! witness codegen, then commit the refreshed artifacts:
//!
//! ```text
//! cargo run -p gpu_witness_eval_generator --bin regenerate_committed
//! ```
//!
//! The `committed_witness_cuh_is_current` test fails until the artifacts match
//! current codegen again. This binary and that test share the [`CIRCUITS`]
//! table, so they cannot disagree about which files to touch.

use gpu_witness_eval_generator::{CIRCUITS, repo_root};
use std::fs;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = repo_root();
    for circuit in CIRCUITS {
        let code = circuit.regenerate(&root)?;
        let out = circuit.committed_path(&root);
        if let Some(parent) = out.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&out, code)?;
        println!("wrote {}", circuit.committed_cuh);
    }
    Ok(())
}
