fn main() {
    if let Err(error) = gpu_prover::memory_sweep::main_entry() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
