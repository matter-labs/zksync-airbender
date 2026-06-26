//! 4-aligned fragmentation upper bound: `J_real − J_ideal` diagnostic.
//!
//! This is a CONSERVATIVE worst-case bound on first-fit fragmentation under
//! ADVERSARIAL base placement (each base ruins a distinct 4-block for exts).
//! It is a separate reported diagnostic; it NEVER enters the J-vs-E gate.
//! Precise dynamic fragmentation is deferred.

use super::driver::{OracleResult, OracleStage};
use super::instance::{NodeKind, OracleInstance, OracleNode};

/// Per-stage closed form:
///   `num_blocks = budget/4`
///   `ruined     = min(base_count, num_blocks)`
///   `usable     = num_blocks − ruined`
///   `overflow   = max(0, ext_count − usable)`
///   `repair    += 4 * overflow`
/// Σ over all stages = upper bound on `J_real − J_ideal`.
pub fn fragmentation_upper_bound(inst: &OracleInstance, j: &OracleResult) -> u64 {
    let w = |id: u32| {
        inst.nodes
            .iter()
            .find(|n| n.id == id)
            .map(|n| n.width)
            .unwrap_or(1)
    };
    let num_blocks = (inst.budget / 4) as u64;
    let mut repair = 0u64;
    for stage in &j.schedule {
        let ext = stage
            .resident_after
            .iter()
            .filter(|&&id| w(id) == 4)
            .count() as u64;
        let base = stage
            .resident_after
            .iter()
            .filter(|&&id| w(id) == 1)
            .count() as u64;
        let ruined = base.min(num_blocks);
        let usable = num_blocks.saturating_sub(ruined);
        let overflow = ext.saturating_sub(usable);
        repair += 4 * overflow;
    }
    repair
}

/// Build a synthetic `(OracleInstance, OracleResult)` with a single stage whose
/// `resident_after` holds `n_ext` width-4 nodes and `n_base` width-1 nodes.
///
/// Node ids: [0..n_ext) are ext (width 4), [n_ext..n_ext+n_base) are base (width 1).
/// The `OracleResult` has placeholder `status:"optimal"`, `traffic/instrs/bound/wall_ms` = 0.
fn stage_set(budget: usize, n_ext: u32, n_base: u32) -> (OracleInstance, OracleResult) {
    let mut nodes: Vec<OracleNode> = Vec::new();

    // Ext nodes: ids 0..n_ext, width 4
    for id in 0..n_ext {
        nodes.push(OracleNode {
            id,
            kind: NodeKind::Read,
            width: 4,
            real_dram: false,
            children: vec![],
        });
    }
    // Base nodes: ids n_ext..n_ext+n_base, width 1
    for i in 0..n_base {
        nodes.push(OracleNode {
            id: n_ext + i,
            kind: NodeKind::Read,
            width: 1,
            real_dram: false,
            children: vec![],
        });
    }

    // All node ids in resident_after
    let resident_after: Vec<u32> = (0..(n_ext + n_base)).collect();

    let inst = OracleInstance {
        budget,
        reloadable_values: vec![],
        roots: resident_after.clone(),
        nodes,
    };

    let result = OracleResult {
        status: "optimal".to_string(),
        traffic: 0,
        instrs: 0,
        bound: 0,
        wall_ms: 0,
        schedule: vec![OracleStage {
            stage: 0,
            root: 0,
            resident_after,
        }],
    };

    (inst, result)
}

#[cfg(test)]
mod tests {
    use super::*;

    // budget 8 = two 4-blocks. {ext, base}: 1 base ruins ≤1 block, the other hosts the
    // ext → 0. {ext, base, base}: 2 bases ruin both blocks → ext has nowhere → repair 4.
    #[test]
    fn one_base_does_not_fragment_two_blocks() {
        let (inst, j) = stage_set(8, /*ext*/ 1, /*base*/ 1); // helper: single-stage resident set
        assert_eq!(fragmentation_upper_bound(&inst, &j), 0);
    }

    #[test]
    fn bases_spread_across_all_blocks_squeeze_out_ext() {
        let (inst, j) = stage_set(8, /*ext*/ 1, /*base*/ 2); // ideal sum 6 ≤ 8, feasible
        assert_eq!(fragmentation_upper_bound(&inst, &j), 4);
    }
}
