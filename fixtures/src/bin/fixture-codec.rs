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
    assert_eq!(
        args.len(),
        2,
        "usage: fixture-codec decode FILE | check FILE"
    );
    match args[0].as_str() {
        "decode" => {
            let bytes = std::fs::read(&args[1]).unwrap();
            std::io::stdout()
                .lock()
                .write_all(&proof_fixtures::decode_json(&bytes))
                .unwrap();
        }
        "check" => assert_relative_labels(&proof_fixtures::read_file::<Value>(&args[1])),
        _ => panic!("unknown fixture-codec command: {}", args[0]),
    }
}
