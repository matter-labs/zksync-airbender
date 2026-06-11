//! Pinned-prefix assignment: greedy by reuse savings over ProgramView.
//! Candidates are hub leaves (repeated source reads) and hub intermediates
//! (eviction-prone multi-use values) alike — one unified cache.

use super::view::ProgramView;
use cs::gkr_compiler::codegen_ir::{Domain, ExprNode};
use std::collections::HashMap;

/// node -> prefix-relative bf-cell index (doubles as the absolute cell
/// address, since the prefix starts at 0).
pub(crate) fn assign(
    arena: &[ExprNode],
    pv: &ProgramView,
    budget_cells: usize,
) -> HashMap<usize, u16> {
    if budget_cells == 0 {
        return HashMap::new();
    }
    let mut candidates: Vec<(usize, u32, usize)> = arena
        .iter()
        .enumerate()
        .filter(|(i, n)| pv.uses[*i] >= 2 && !matches!(n, ExprNode::Constant(_)))
        .map(|(i, n)| {
            let width = match super::node_domain(n) {
                Domain::Base => 1usize,
                Domain::Ext => 4,
            };
            (i, pv.uses[i], width)
        })
        .collect();
    candidates.sort_by(|a, b| {
        let sa = (a.1 - 1) as f64 / a.2 as f64;
        let sb = (b.1 - 1) as f64 / b.2 as f64;
        sb.partial_cmp(&sa).unwrap().then(a.0.cmp(&b.0))
    });
    let mut map = HashMap::new();
    let mut next_cell = 0usize;
    for (node, _, width) in candidates {
        let aligned = if width == 4 { (next_cell + 3) & !3 } else { next_cell };
        if aligned + width > budget_cells {
            continue;
        }
        map.insert(node, aligned as u16);
        next_cell = aligned + width;
    }
    map
}
