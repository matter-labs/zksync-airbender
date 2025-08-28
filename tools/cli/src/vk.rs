use execution_utils::{Machine, VerificationKey};
use sha3::{Digest, Keccak256};

pub fn generate_vk(bin_path: &String, machine: &Option<Machine>, output: &Option<String>) {
    let binary = std::fs::read(bin_path).expect("Failed to read binary file");

    let mut hasher = Keccak256::new();
    hasher.update(&binary);
    let hash = hasher.finalize();
    let bytecode_hash_hex = format!("{:x}", hash);
    let params = execution_utils::generate_params_for_binary(
        &binary,
        machine.clone().unwrap_or(Machine::Standard),
    );

    let params_hex = params
        .iter()
        .map(|p| format!("{:08x}", p))
        .collect::<Vec<_>>()
        .join("");

    let vk = VerificationKey {
        machine_type: machine.clone().unwrap_or(Machine::Standard),
        bytecode_hash_hex,
        params,
        params_hex,
    };

    println!("Verification key generated: {:?}", vk);

    if let Some(output) = output {
        let json = serde_json::to_string_pretty(&vk)
            .expect("Failed to serialize verification key to JSON");
        std::fs::write(output, json).expect("Failed to write verification key to output file");
        println!("Verification key written to {}", output);
    }
}
