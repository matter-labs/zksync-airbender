//! Instrumented verifier renders for the F1 ↔ v0 oracle: every `keccak256` result except the
//! Merkle leaf and node hashes (transcript absorbs and draws, PoW digests, query draws, the
//! committed state) is appended to a log, and every `return(p, len)` returns
//! `[count][hash_0..hash_{count−1}]` followed by the verifier's own return data. Merkle hashing
//! is wire-data verification, not transcript: with a setup frontier F1 walks shorter setup paths.

/// The log: `count` at `LOG_PTR`, then one word per hash. Above every verifier region.
pub(crate) const LOG_PTR: usize = 0x40000;

const HELPERS: &str = "\
        function ilog_k(h) -> r {
            r := h
            let n := add(mload(__LOG__), 1)
            mstore(add(__LOG__, mul(32, n)), h)
            mstore(__LOG__, n)
        }
        function ilog_return(p, len) {
            let head := mul(32, add(mload(__LOG__), 1))
            mcopy(add(__LOG__, head), p, len)
            return(__LOG__, add(head, len))
        }
";

fn rewrite_calls(src: &str, op: &str, wrap: &dyn Fn(&str) -> String) -> String {
    let is_ident = |c: char| c.is_ascii_alphanumeric() || c == '_';
    let pattern = format!("{op}(");
    let mut out = String::with_capacity(src.len() + src.len() / 16);
    let mut rest = src;
    while let Some(at) = rest.find(&pattern) {
        out.push_str(&rest[..at]);
        let tail = &rest[at..];
        let line = &out[out.rfind('\n').map_or(0, |i| i + 1)..];
        if out.chars().next_back().is_some_and(is_ident) || line.contains("//") {
            out.push_str(&pattern);
            rest = &tail[pattern.len()..];
            continue;
        }
        let mut depth = 0usize;
        let end = tail
            .char_indices()
            .find_map(|(i, ch)| {
                match ch {
                    '(' => depth += 1,
                    ')' => {
                        depth -= 1;
                        if depth == 0 {
                            return Some(i);
                        }
                    }
                    _ => {}
                }
                None
            })
            .expect("unbalanced call");
        let args = rewrite_calls(&tail[op.len() + 1..end], op, wrap);
        out.push_str(&wrap(&args));
        rest = &tail[end + 1..];
    }
    out.push_str(rest);
    out
}

/// The instrumented render of a generated verifier source.
pub fn instrument(src: &str) -> String {
    let src = rewrite_calls(src, "keccak256", &|args| {
        let merkle = ["0, 64", "__TEMPLATE_WHIR_LEAF_PTR, mul("]
            .iter()
            .any(|p| args.trim_start().starts_with(p));
        if merkle {
            format!("keccak256({args})")
        } else {
            format!("ilog_k(keccak256({args}))")
        }
    });
    let src = rewrite_calls(&src, "return", &|args| format!("ilog_return({args})"));
    let at = src
        .find("\n        function ")
        .expect("verifier has no Yul function")
        + 1;
    let helpers = HELPERS.replace("__LOG__", &LOG_PTR.to_string());
    format!("{}{helpers}{}", &src[..at], &src[at..])
}
