use ::field::Proth120;
use ::field::baby_bear::base::BabyBearField;
use gpu_witness_eval_generator::generate_from_files_for_field;
use std::env;
use std::fs;
use std::path::PathBuf;

fn usage(program: &str) -> String {
    format!(
        "usage: {program} <layout.json> <ssa.json> <output.cuh> [--write-memory] [--field babybear|proth120]"
    )
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = env::args();
    let program = args.next().unwrap_or_else(|| "generate".to_owned());
    let mut positional = Vec::new();
    let mut write_memory = false;
    let mut field = "babybear".to_owned();

    while let Some(arg) = args.next() {
        if arg == "--write-memory" {
            write_memory = true;
        } else if arg == "--field" {
            field = args.next().ok_or_else(|| usage(&program))?;
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
    let code = match field.as_str() {
        "babybear" => {
            generate_from_files_for_field::<BabyBearField>(&layout_path, &ssa_path, write_memory)?
        }
        "proth120" => {
            generate_from_files_for_field::<Proth120>(&layout_path, &ssa_path, write_memory)?
        }
        _ => return Err(format!("unknown field {field:?}\n{}", usage(&program)).into()),
    };

    if let Some(parent) = output_path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(output_path, code)?;

    Ok(())
}
