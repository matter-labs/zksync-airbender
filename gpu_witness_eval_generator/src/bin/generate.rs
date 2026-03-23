use gpu_witness_eval_generator::generate_from_files;
use std::env;
use std::fs;
use std::path::PathBuf;

fn usage(program: &str) -> String {
    format!("usage: {program} <layout.json> <ssa.json> <output.cuh> [--write-memory]")
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = env::args();
    let program = args.next().unwrap_or_else(|| "generate".to_owned());
    let mut positional = Vec::new();
    let mut write_memory = false;

    for arg in args {
        if arg == "--write-memory" {
            write_memory = true;
        } else {
            positional.push(arg);
        }
    }

    if positional.len() != 3 {
        return Err(usage(&program).into());
    }

    let layout_path = PathBuf::from(&positional[0]);
    let ssa_path = PathBuf::from(&positional[1]);
    let output_path = PathBuf::from(&positional[2]);
    let code = generate_from_files(&layout_path, &ssa_path, write_memory)?;

    if let Some(parent) = output_path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(output_path, code)?;

    Ok(())
}
