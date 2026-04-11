use gpu_witness_eval_generator::generate_add_sub_lui_auipc_mop_main_backward_from_files;
use std::env;
use std::fs;
use std::path::PathBuf;

fn usage(program: &str) -> String {
    format!("usage: {program} <layout.json> <output.cuh>")
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = env::args();
    let program = args
        .next()
        .unwrap_or_else(|| "generate_gkr_main_backward".to_owned());
    let positional = args.collect::<Vec<_>>();
    if positional.len() != 2 {
        return Err(usage(&program).into());
    }

    let layout_path = PathBuf::from(&positional[0]);
    let output_path = PathBuf::from(&positional[1]);
    let code = generate_add_sub_lui_auipc_mop_main_backward_from_files(&layout_path)?;

    if let Some(parent) = output_path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(output_path, code)?;
    Ok(())
}
