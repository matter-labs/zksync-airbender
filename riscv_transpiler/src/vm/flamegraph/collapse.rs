use std::collections::HashMap;

use rayon::prelude::*;

/// Converts distinct raw stacks with their sample counts into `inferno`'s
/// collapsed stack format (`root;...;leaf count`), given the frame names of
/// every address (`symbols`). Stacks are collapsed in parallel; distinct raw
/// stacks that symbolize to the same path are merged.
pub(super) fn build_collapsed_stack_lines(
    stacks: &[(&[u32], usize)],
    symbols: &HashMap<u32, Vec<String>>,
) -> Vec<String> {
    let collapsed_line_counts: HashMap<String, usize> = stacks
        .par_iter()
        .fold(
            || (HashMap::new(), Vec::with_capacity(64)),
            |(mut counts, mut buffer), (stack, count)| {
                if let Some(line) = collapse_stack(stack, symbols, &mut buffer) {
                    *counts.entry(line).or_default() += count;
                }
                (counts, buffer)
            },
        )
        .map(|(counts, _)| counts)
        .reduce(HashMap::new, |a, b| {
            if a.len() < b.len() {
                return merge_counts(b, a);
            }
            merge_counts(a, b)
        });

    let mut remapped = Vec::with_capacity(collapsed_line_counts.len());
    for (line, count) in collapsed_line_counts.into_iter() {
        let mut line_with_count = line;
        line_with_count.push(' ');
        line_with_count.push_str(&count.to_string());
        remapped.push(line_with_count);
    }

    remapped
}

fn merge_counts(
    mut into: HashMap<String, usize>,
    from: HashMap<String, usize>,
) -> HashMap<String, usize> {
    for (line, count) in from {
        *into.entry(line).or_default() += count;
    }
    into
}

/// Symbolizes one raw stack (sampled `pc` first, then callsites) into a
/// root-first `;`-separated path. `buffer` is scratch space for the merged
/// leaf-first frame list.
fn collapse_stack<'a>(
    stack: &[u32],
    symbols: &'a HashMap<u32, Vec<String>>,
    buffer: &mut Vec<&'a str>,
) -> Option<String> {
    buffer.clear();

    // Stack unwinding and DWARF frame expansion can produce overlapping
    // frame sequences. We merge overlaps to avoid duplicate path segments.
    for pc in stack.iter().copied() {
        let Some(names) = try_frames_for_pc(symbols, pc) else {
            continue;
        };
        append_frames_with_overlap(buffer, names);
    }

    if buffer.is_empty() {
        return None;
    }

    // `inferno` collapsed format expects root-first paths separated by `;`.
    // Our merged buffer is leaf-first, so we reverse it at serialization.
    let mut line = String::with_capacity(buffer.len() * 16 + 12);
    for (idx, el) in buffer.iter().rev().enumerate() {
        if idx > 0 {
            line.push(';');
        }
        line.push_str(el);
    }
    Some(line)
}

#[inline(always)]
fn try_frames_for_pc(symbols: &HashMap<u32, Vec<String>>, pc: u32) -> Option<&[String]> {
    // Unaligned PCs are not valid instruction addresses in this VM and are
    // usually artifacts of incomplete stack data.
    if pc % 4 != 0 {
        return None;
    }

    match symbols.get(&pc) {
        Some(names) if names.is_empty() == false => Some(names),
        _ => None,
    }
}

#[inline(always)]
fn append_frames_with_overlap<'a>(buffer: &mut Vec<&'a str>, names: &'a [String]) {
    if names.is_empty() {
        return;
    }

    if buffer.is_empty() {
        buffer.extend(names.iter().map(String::as_str));
        return;
    }

    let max_overlap = buffer.len().min(names.len());
    // Keep only the non-overlapping suffix from `names` so each logical stack
    // segment appears once in the merged path.
    let overlap = (1..=max_overlap)
        .rev()
        .find(|overlap_len| {
            buffer[(buffer.len() - *overlap_len)..]
                .iter()
                .zip(names[..*overlap_len].iter())
                .all(|(a, b)| *a == b.as_str())
        })
        .unwrap_or(0);

    if overlap < names.len() {
        buffer.extend(names[overlap..].iter().map(String::as_str));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn symbols() -> HashMap<u32, Vec<String>> {
        // Leaf-first frame lists, as addr2line reports inlined frames.
        let mut symbols = HashMap::new();
        symbols.insert(0x100, vec!["leaf".to_string(), "inlined_into".to_string()]);
        symbols.insert(
            0x200,
            vec!["inlined_into".to_string(), "caller".to_string()],
        );
        symbols.insert(0x300, vec!["main".to_string()]);
        symbols.insert(0x400, Vec::new());
        symbols
    }

    #[test]
    fn collapses_and_merges_overlapping_frames() {
        let symbols = symbols();
        let mut buffer = Vec::new();
        let line = collapse_stack(&[0x100, 0x200, 0x300], &symbols, &mut buffer).unwrap();
        assert_eq!(line, "main;caller;inlined_into;leaf");
    }

    #[test]
    fn skips_unaligned_unknown_and_empty_addresses() {
        let symbols = symbols();
        let mut buffer = Vec::new();
        let line =
            collapse_stack(&[0x100, 0x102, 0x400, 0x999, 0x300], &symbols, &mut buffer).unwrap();
        assert_eq!(line, "main;inlined_into;leaf");
        assert!(collapse_stack(&[0x400, 0x102], &symbols, &mut buffer).is_none());
    }

    #[test]
    fn distinct_raw_stacks_with_the_same_path_are_merged() {
        let symbols = symbols();
        let a: &[u32] = &[0x100, 0x200, 0x300];
        // Same path once the unknown address is dropped.
        let b: &[u32] = &[0x100, 0x400, 0x200, 0x300];
        let c: &[u32] = &[0x100, 0x300];
        let mut lines = build_collapsed_stack_lines(&[(a, 3), (b, 4), (c, 5)], &symbols);
        lines.sort();
        assert_eq!(
            lines,
            vec![
                "main;caller;inlined_into;leaf 7".to_string(),
                "main;inlined_into;leaf 5".to_string()
            ]
        );
    }
}
