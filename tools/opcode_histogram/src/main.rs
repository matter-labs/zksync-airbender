use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use opcode_histogram::{histogram, Mnemonic};

fn print_usage() {
    eprintln!(
        "Usage: opcode_histogram [--json] <path-to-.text-or-.bin> [more paths...]\n\
         \n\
         Walks each input as 4-byte-aligned little-endian RV32 instructions\n\
         and prints per-mnemonic counts. Pass `--json` to emit a single JSON\n\
         object keyed by file path (each value is a {{mnemonic: count}} map).\n"
    );
}

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() || args.iter().any(|a| a == "-h" || a == "--help") {
        print_usage();
        return ExitCode::from(1);
    }

    let json_mode = if let Some(pos) = args.iter().position(|a| a == "--json") {
        args.remove(pos);
        true
    } else {
        false
    };

    let mut all: BTreeMap<String, BTreeMap<Mnemonic, u64>> = BTreeMap::new();
    let mut had_error = false;

    for path_str in &args {
        let path = PathBuf::from(path_str);
        let bytes = match fs::read(&path) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("error: failed to read {}: {}", path.display(), e);
                had_error = true;
                continue;
            }
        };
        let h = histogram(&bytes);
        all.insert(path_str.clone(), h);
    }

    if json_mode {
        // Hand-rolled JSON to avoid pulling serde in for a one-shot tool.
        print!("{{");
        let mut first_path = true;
        for (path, h) in &all {
            if !first_path {
                print!(",");
            }
            first_path = false;
            print!("{}:{{", json_string(path));
            let mut first_entry = true;
            for (mn, count) in h {
                if !first_entry {
                    print!(",");
                }
                first_entry = false;
                print!("{}:{}", json_string(&mnemonic_label(*mn)), count);
            }
            print!("}}");
        }
        println!("}}");
    } else {
        for (path, h) in &all {
            println!("=== {} ===", path);
            let mut entries: Vec<(Mnemonic, u64)> = h.iter().map(|(k, v)| (*k, *v)).collect();
            entries.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
            let total: u64 = entries.iter().map(|(_, c)| c).sum();
            println!("  total instructions: {}", total);
            for (mn, count) in entries {
                println!("  {:>20}  {:>10}", mnemonic_label(mn), count);
            }
            println!();
        }
    }

    if had_error {
        ExitCode::from(2)
    } else {
        ExitCode::SUCCESS
    }
}

fn mnemonic_label(mn: Mnemonic) -> String {
    match mn {
        Mnemonic::Unknown {
            opcode,
            funct3,
            funct7,
        } => format!(
            "Unknown(op=0b{:07b},f3=0b{:03b},f7=0b{:07b})",
            opcode, funct3, funct7
        ),
        other => format!("{:?}", other),
    }
}

fn json_string(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
