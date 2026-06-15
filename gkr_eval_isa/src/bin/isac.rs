//! Usage: cargo run -p gkr_eval_isa --bin isac -- <ir.json>... [--json <out.json>]
//!        cargo run -p gkr_eval_isa --bin isac -- --v2 [<ir.json>...]
//!
//! Default (no `--v2`): the v1 unified-budget pin-trade report.
//! `--v2`: the ISA-v2 static cost report (size, histograms, matrix table, R2
//! register/occupancy proxy) over the fixtures passed, or the standard 22-
//! fixture corpus when none are given. Prints markdown to STDOUT only (the
//! controller redirects to the report path); never writes a file.

use gkr_design_space::import::load_circuit;
use gkr_eval_isa::report::{circuit_cost, to_markdown};
use gkr_eval_isa::report_v2;

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();

    // --v2 arm: ISA-v2 static cost report.
    if let Some(i) = args.iter().position(|a| a == "--v2") {
        args.remove(i);
        // Fixtures passed, else the standard corpus the v1 arm sweeps.
        let paths: Vec<std::path::PathBuf> = if args.is_empty() {
            gkr_eval_isa::test_support::all_fixtures()
        } else {
            args.iter().map(std::path::PathBuf::from).collect()
        };
        std::panic::set_hook(Box::new(|_| {}));
        let reports: Vec<_> = paths
            .iter()
            .map(|p| {
                let name = p.file_name().and_then(|n| n.to_str()).unwrap_or("?").to_string();
                let c = load_circuit(p).unwrap_or_else(|e| panic!("{e:?}"));
                report_v2::circuit_cost_v2(&name, &c)
            })
            .collect();
        let _ = std::panic::take_hook();
        // STDOUT only — no file write (the controller redirects).
        println!("{}", report_v2::to_markdown(&reports));
        return;
    }

    let json_out = args.iter().position(|a| a == "--json").map(|i| {
        let p = args[i + 1].clone();
        args.drain(i..=i + 1);
        p
    });
    if args.is_empty() {
        eprintln!("usage: isac <codegen_ir.json>... [--json <out.json>]");
        eprintln!("       isac --v2 [<codegen_ir.json>...]");
        std::process::exit(2);
    }
    let loaded: Vec<_> = args
        .iter()
        .map(|p| (p, load_circuit(std::path::Path::new(p)).unwrap_or_else(|e| panic!("{e}"))))
        .collect();
    // Infeasible grid cells panic inside circuit_cost (caught there); keep
    // their backtrace spam off stderr during the sweep.
    std::panic::set_hook(Box::new(|_| {}));
    let costs: Vec<_> = loaded.iter().map(|(p, c)| circuit_cost(p, c)).collect();
    let _ = std::panic::take_hook();
    println!("{}", to_markdown(&costs));
    if let Some(out) = json_out {
        std::fs::write(&out, serde_json::to_string_pretty(&costs).unwrap()).unwrap();
        eprintln!("json written to {out}");
    }
}
