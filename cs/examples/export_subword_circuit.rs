//! Export the complete native subword circuit with bounded ROM materialization.
mod rom_export {
    include!("../../formal_verification/native/rom_tables.rs");
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() != 1 {
        return Err("usage: export_subword_circuit OUTPUT.json".into());
    }
    let circuit = rom_export::compile_subword_circuit(&[], false);
    let mut output = std::io::BufWriter::new(std::fs::File::create(&args[0])?);
    serde_json::to_writer_pretty(&mut output, &circuit)?;
    std::io::Write::flush(&mut output)?;
    println!("Exported complete native subword circuit to {}", args[0]);
    Ok(())
}
