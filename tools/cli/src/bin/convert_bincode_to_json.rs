use execution_utils::ProgramProof;
use std::env;
use std::fs;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 3 {
        eprintln!("Usage: {} <input.bin> <output.json>", args[0]);
        std::process::exit(1);
    }

    let input_path = &args[1];
    let output_path = &args[2];

    println!("Reading bincode from: {}", input_path);
    let bincode_data = fs::read(input_path).expect("Failed to read input file");

    println!("Deserializing ProgramProof from bincode...");
    let program_proof: ProgramProof = bincode::serde::decode_from_slice(
        &bincode_data,
        bincode::config::standard(),
    )
    .expect("Failed to deserialize ProgramProof")
    .0;

    println!("Serializing to JSON...");
    let json_data = serde_json::to_string_pretty(&program_proof)
        .expect("Failed to serialize to JSON");

    println!("Writing JSON to: {}", output_path);
    fs::write(output_path, json_data).expect("Failed to write output file");

    println!("Conversion complete!");
}
