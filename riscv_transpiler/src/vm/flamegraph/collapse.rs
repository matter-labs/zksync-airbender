use std::collections::HashMap;

use super::symbolizer::Addr2LineContext;

/// Converts raw sampled stacks into `inferno`'s collapsed stack format.
pub(super) fn build_collapsed_stack_lines(
    frames: &[(u32, Vec<u32>)],
    symbolizer: &Addr2LineContext<'_>,
) -> Vec<String> {
    // Hot PCs appear in many samples, so we resolve symbols once per address.
    let mut symbol_cache: HashMap<u32, Vec<String>> = HashMap::new();
    let mut collapsed_line_counts: HashMap<String, usize> = HashMap::new();
    // Temporary merged stack for one sample before collapsing into a line.
    let mut buffer = Vec::with_capacity(64);

    for (pc, callsites) in frames.iter() {
        buffer.clear();

        if let Some(names) = try_frames_for_pc(symbolizer, &mut symbol_cache, *pc) {
            append_frames_with_overlap(&mut buffer, names);
        }

        // Stack unwinding and DWARF frame expansion can produce overlapping
        // frame sequences. We merge overlaps to avoid duplicate path segments.
        for callsite_pc in callsites.iter().copied().skip(1) {
            let Some(names) = try_frames_for_pc(symbolizer, &mut symbol_cache, callsite_pc) else {
                continue;
            };
            append_frames_with_overlap(&mut buffer, names);
        }

        if buffer.is_empty() {
            continue;
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

        *collapsed_line_counts.entry(line).or_default() += 1;
    }

    let mut remapped = Vec::with_capacity(collapsed_line_counts.len());
    for (line, count) in collapsed_line_counts.into_iter() {
        let mut line_with_count = line;
        line_with_count.push(' ');
        line_with_count.push_str(&count.to_string());
        remapped.push(line_with_count);
    }

    remapped
}

#[inline(always)]
fn try_frames_for_pc<'a>(
    symbolizer: &Addr2LineContext<'_>,
    symbol_cache: &'a mut HashMap<u32, Vec<String>>,
    pc: u32,
) -> Option<&'a [String]> {
    // Unaligned PCs are not valid instruction addresses in this VM and are
    // usually artifacts of incomplete stack data.
    if pc % 4 != 0 {
        return None;
    }

    if symbol_cache.contains_key(&pc) == false {
        let frames = symbolizer.collect_frames(pc);
        symbol_cache.insert(pc, frames);
    }

    let names = symbol_cache
        .get(&pc)
        .expect("symbol cache must contain a value");
    if names.is_empty() {
        None
    } else {
        Some(names)
    }
}

#[inline(always)]
fn append_frames_with_overlap(buffer: &mut Vec<String>, names: &[String]) {
    if names.is_empty() {
        return;
    }

    if buffer.is_empty() {
        buffer.extend(names.iter().cloned());
        return;
    }

    let max_overlap = buffer.len().min(names.len());
    // Keep only the non-overlapping suffix from `names` so each logical stack
    // segment appears once in the merged path.
    let overlap = (1..=max_overlap)
        .rev()
        .find(|overlap_len| buffer[(buffer.len() - *overlap_len)..] == names[..*overlap_len])
        .unwrap_or(0);

    if overlap < names.len() {
        buffer.extend(names[overlap..].iter().cloned());
    }
}
