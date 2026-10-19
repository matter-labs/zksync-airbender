use std::path::{Path, PathBuf};

pub fn parse_hex(raw: &str) -> Vec<u32> {
    let raw = raw.trim();
    assert!(
        raw.len().is_multiple_of(8),
        "expected eight hex digits per word"
    );
    raw.as_bytes()
        .chunks(8)
        .map(|chunk| {
            u32::from_str_radix(std::str::from_utf8(chunk).expect("ASCII witness"), 16)
                .expect("invalid witness word")
        })
        .collect()
}

pub fn load_words(path: &Path) -> Vec<u32> {
    let raw =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    parse_hex(&raw)
}

/// Sorted local inputs; discovery and parsing finish without creating a GPU
/// context. All paths are input-only and never modified by the generator.
pub fn discover(directory: &Path) -> Vec<(String, PathBuf)> {
    for guest in ["app.bin", "app.text"] {
        assert!(directory.join(guest).is_file(), "missing guest {guest}");
    }
    let mut inputs = Vec::new();
    for entry in std::fs::read_dir(directory.join("inputs")).expect("list local prover inputs") {
        let path = entry.expect("read local input entry").path();
        if path.extension().and_then(|s| s.to_str()) != Some("hex") {
            continue;
        }
        assert!(path.is_file(), "not an input file: {}", path.display());
        let id = path
            .file_stem()
            .and_then(|s| s.to_str())
            .expect("UTF8 input name");
        assert!(
            !id.is_empty()
                && id
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-'),
            "invalid local input id {id:?}"
        );
        inputs.push((id.to_owned(), path));
    }
    inputs.sort_by(|a, b| a.0.cmp(&b.0));
    assert!(!inputs.is_empty(), "local corpus has no inputs/*.hex");
    inputs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cpu_cost_model_inputs_have_stable_order_and_word_encoding() {
        let root = std::env::temp_dir().join(format!("cal-inputs-{}", std::process::id()));
        std::fs::create_dir(&root).unwrap();
        std::fs::create_dir(root.join("inputs")).unwrap();
        for guest in ["app.bin", "app.text"] {
            std::fs::write(root.join(guest), [0u8; 4]).unwrap();
        }
        assert!(std::panic::catch_unwind(|| discover(&root)).is_err());
        std::fs::write(root.join("inputs/20.hex"), "12345678ffffffff\n").unwrap();
        std::fs::write(root.join("inputs/10.hex"), "0000000100000002").unwrap();
        let inputs = discover(&root);
        assert_eq!(
            inputs.iter().map(|(id, _)| id.as_str()).collect::<Vec<_>>(),
            ["10", "20"]
        );
        assert_eq!(load_words(&inputs[0].1), [1, 2]);
        assert_eq!(load_words(&inputs[1].1), [0x1234_5678, u32::MAX]);
        std::fs::remove_file(root.join("app.text")).unwrap();
        assert!(std::panic::catch_unwind(|| discover(&root)).is_err());
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn cpu_cost_model_inputs_reject_malformed_words() {
        assert!(std::panic::catch_unwind(|| parse_hex("0000000")).is_err());
        assert!(std::panic::catch_unwind(|| parse_hex("0000000z")).is_err());
    }
}
