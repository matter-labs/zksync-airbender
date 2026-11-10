use serde_json::Value;
use std::io::Write;
use std::path::Path;

fn assert_relative_labels(value: &Value) {
    match value {
        Value::String(label) => {
            if let Some((_, location)) = label.split_once("Variable at ") {
                let (file, _) = location.rsplit_once("::").expect("variable label location");
                assert!(
                    !Path::new(file).is_absolute(),
                    "absolute variable label: {label}"
                );
            }
        }
        Value::Array(values) => values.iter().for_each(assert_relative_labels),
        Value::Object(values) => values.values().for_each(assert_relative_labels),
        _ => {}
    }
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    assert!(
        args.len() >= 2,
        "usage: fixture-codec decode FILE | check FILE MODE CHAIN"
    );
    match args[0].as_str() {
        "decode" => {
            assert_eq!(args.len(), 2);
            let bytes = std::fs::read(&args[1]).unwrap();
            std::io::stdout()
                .lock()
                .write_all(&proof_fixtures::decode_json(&bytes))
                .unwrap();
        }
        "check" => {
            assert_eq!(args.len(), 4);
            let artifact: Value = proof_fixtures::read_file(&args[1]);
            let mode = match args[2].as_str() {
                "pessimistic_conjecture" => "PessimisticConjecture",
                "ethproofs_soundcalc" => "EthproofsSoundnessCalc",
                _ => panic!("unknown soundness mode: {}", args[2]),
            };
            let (target, entries) = match args[3].as_str() {
                "base" => ("Base", 1),
                "unified" => ("RecursionUnified", 3),
                "unrolled" => ("RecursionUnrolled", 2),
                "unrolled_unified" => ("RecursionUnified", 4),
                _ => panic!("unknown chain: {}", args[3]),
            };
            assert_eq!(artifact["schema_version"], 5);
            assert_eq!(artifact["security_level"], "Sec100");
            assert_eq!(artifact["soundness_mode"], mode);
            assert_eq!(artifact["target"], target);
            assert_eq!(artifact["program_cycles"], 97);
            assert_eq!(
                artifact["chain_end_params"].as_array().unwrap().len(),
                entries
            );
            assert!(artifact.get("backend").is_none());
            assert!(artifact.get("timings_ms").is_none());
            assert_relative_labels(&artifact);
        }
        _ => panic!("unknown fixture-codec command: {}", args[0]),
    }
}
