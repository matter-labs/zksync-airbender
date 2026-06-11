//! Usage: cargo run -p gkr_eval_isa --bin isac -- <ir.json>... [--json <out.json>]

use gkr_design_space::import::load_circuit;
use gkr_eval_isa::report::{circuit_cost, to_markdown};

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let json_out = args.iter().position(|a| a == "--json").map(|i| {
        let p = args[i + 1].clone();
        args.drain(i..=i + 1);
        p
    });
    if args.is_empty() {
        eprintln!("usage: isac <codegen_ir.json>... [--json <out.json>]");
        std::process::exit(2);
    }
    let costs: Vec<_> = args
        .iter()
        .map(|p| {
            let c = load_circuit(std::path::Path::new(p)).unwrap_or_else(|e| panic!("{e}"));
            circuit_cost(p, &c)
        })
        .collect();
    println!("{}", to_markdown(&costs));
    if let Some(out) = json_out {
        std::fs::write(&out, serde_json::to_string_pretty(&costs).unwrap()).unwrap();
        eprintln!("json written to {out}");
    }
}
