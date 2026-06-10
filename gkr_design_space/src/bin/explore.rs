//! Usage: cargo run -p gkr_design_space --bin explore -- <ir.json>... [--json <out.json>]

use gkr_design_space::import::load_circuit;
use gkr_design_space::report::{build_report, to_markdown};
use std::path::PathBuf;

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let json_out = args.iter().position(|a| a == "--json").map(|i| {
        let path = args[i + 1].clone();
        args.drain(i..=i + 1);
        PathBuf::from(path)
    });
    if args.is_empty() {
        eprintln!("usage: explore <codegen_ir.json>... [--json <out.json>]");
        std::process::exit(2);
    }
    let mut reports = Vec::new();
    for path in &args {
        let c = load_circuit(std::path::Path::new(path)).unwrap_or_else(|e| panic!("{e}"));
        let r = build_report(path, &c, json_out.is_some());
        println!("{}", to_markdown(&r));
        reports.push(r);
    }
    if let Some(out) = json_out {
        std::fs::write(&out, serde_json::to_string_pretty(&reports).unwrap()).unwrap();
        eprintln!("json written to {}", out.display());
    }
}
