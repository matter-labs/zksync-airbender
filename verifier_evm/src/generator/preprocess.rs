//! Line directives for template variants: `// #if NAME`, `// #if !NAME`, `// #else`,
//! `// #endif` (nestable). Directive lines are dropped; a source without directives is
//! returned unchanged.

pub(crate) fn preprocess(src: &str, flags: &[&str]) -> String {
    // One entry per open block: (this branch emits, the enclosing block emits).
    let mut stack: Vec<(bool, bool)> = Vec::new();
    let mut out = String::with_capacity(src.len());
    for line in src.split_inclusive('\n') {
        let directive = line.trim();
        let active = stack.last().is_none_or(|(on, outer)| *on && *outer);
        if let Some(cond) = directive.strip_prefix("// #if ") {
            let (negated, name) = match cond.trim().strip_prefix('!') {
                Some(name) => (true, name),
                None => (false, cond.trim()),
            };
            stack.push((flags.contains(&name) != negated, active));
        } else if directive == "// #else" {
            let (on, _) = stack.last_mut().expect("`// #else` without `// #if`");
            *on = !*on;
        } else if directive == "// #endif" {
            stack.pop().expect("`// #endif` without `// #if`");
        } else if active {
            out.push_str(line);
        }
    }
    assert!(stack.is_empty(), "unterminated `// #if`");
    out
}

#[cfg(test)]
mod tests {
    use super::preprocess;

    #[test]
    fn selects_branches() {
        let src =
            "a\n// #if F1\nb\n// #if !X\nc\n// #else\nd\n// #endif\n// #else\ne\n// #endif\nf";
        assert_eq!(preprocess(src, &[]), "a\ne\nf");
        assert_eq!(preprocess(src, &["F1"]), "a\nb\nc\nf");
        assert_eq!(preprocess(src, &["F1", "X"]), "a\nb\nd\nf");
        assert_eq!(preprocess("x\ny\n", &["F1"]), "x\ny\n");
    }

    #[test]
    #[should_panic(expected = "unterminated")]
    fn rejects_unterminated() {
        preprocess("// #if F1\nx\n", &[]);
    }
}
