//! Gap report + provisional J-vs-E gate (Task 7).
//!
//! Self-contained: no solver, no fixtures. Consumes gap numbers per instance
//! and applies the Global-Constraints cutoffs.

/// One row of gap data for a single (circuit, budget) instance.
pub struct GapRow {
    pub name: String,
    /// Contributes to the gate decision?
    pub decision_bearing: bool,
    /// §4.3-mandated full-size `prior_edges > 0` instance (bigint-L0).
    pub required_full_size: bool,
    /// Budget cells. `u64::MAX` flags a `BudgetBelowFloor` row.
    pub c: u64,
    /// Execution cost under current ordering.
    pub e: u64,
    /// Ideal execution cost under optimal ordering.
    pub j_ideal: u64,
    /// Fragmentation (slack between e and j_ideal due to packing).
    pub frag: u64,
    /// Denominator for ratio computation (e.g. total ops or d budget).
    pub d: u64,
    /// Solver status for `e`.
    pub e_status: String,
    /// Solver status for `j_ideal`.
    pub j_status: String,
}

/// Provisional gate verdict for the J-vs-E ordering question.
#[derive(Debug, PartialEq)]
pub enum Gate {
    Stop,
    CachingOnly,
    BuildBeam,
    Marginal,
    Insufficient,
}

/// Apply Global-Constraints cutoffs over the gap rows.
///
/// §4.3: cannot conclude "order doesn't matter" without a full-size
/// `prior_edges > 0` row that actually solved to optimal.
pub fn gate(rows: &[GapRow]) -> Gate {
    let optimal = |r: &GapRow| r.e_status == "optimal" && r.j_status == "optimal";
    // §4.3: cannot conclude without a full-size prior_edges>0 row solved to optimal.
    if !rows.iter().any(|r| r.required_full_size && optimal(r)) {
        return Gate::Insufficient;
    }
    let mut max_ratio = 0.0f64;
    for r in rows.iter().filter(|r| r.decision_bearing && optimal(r) && r.d > 0) {
        max_ratio = max_ratio.max((r.e as f64 - r.j_ideal as f64) / r.d as f64);
    }
    if max_ratio >= 0.15 {
        Gate::BuildBeam
    } else if max_ratio < 0.05 {
        Gate::CachingOnly
    } else {
        Gate::Marginal
    }
}

/// Format a human-readable report of the gap rows.
///
/// Prints a header + one line per row. When `c == u64::MAX` (BudgetBelowFloor),
/// the `c` column prints `"BUDGET<FLOOR"` and the joint-headroom `(c−j)/d`
/// column is omitted to avoid printing garbage.
pub fn format_report(rows: &[GapRow]) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "{:<20} {:>14} {:>10} {:>10} {:>8} {:>8} {:>12} {:>14}\n",
        "name", "c", "e", "j_ideal", "frag", "d", "order-gap%", "headroom%"
    ));
    out.push_str(&"-".repeat(100));
    out.push('\n');
    for r in rows {
        let c_str = if r.c == u64::MAX {
            "BUDGET<FLOOR".to_string()
        } else {
            r.c.to_string()
        };
        let order_gap = if r.d > 0 {
            format!("{:.2}%", (r.e as f64 - r.j_ideal as f64) / r.d as f64 * 100.0)
        } else {
            "N/A".to_string()
        };
        let headroom = if r.c != u64::MAX && r.d > 0 {
            format!("{:.2}%", (r.c as f64 - r.j_ideal as f64) / r.d as f64 * 100.0)
        } else {
            // Skip headroom when c == u64::MAX (BUDGET<FLOOR) so it never prints garbage.
            String::new()
        };
        out.push_str(&format!(
            "{:<20} {:>14} {:>10} {:>10} {:>8} {:>8} {:>12} {:>14}\n",
            r.name, c_str, r.e, r.j_ideal, r.frag, r.d, order_gap, headroom
        ));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: full-size required row, both-optimal.
    fn row(name: &str, c: u64, e: u64, j: u64, d: u64) -> GapRow {
        GapRow {
            name: name.into(),
            decision_bearing: true,
            required_full_size: true,
            c,
            e,
            j_ideal: j,
            frag: 0,
            d,
            e_status: "optimal".into(),
            j_status: "optimal".into(),
        }
    }

    #[test]
    fn gate_build_beam_when_order_gap_large() {
        // (e − j) / d = (100 − 80) / 100 = 20% ≥ 15% → BuildBeam
        assert!(matches!(gate(&[row("hard", 120, 100, 80, 100)]), Gate::BuildBeam));
    }

    #[test]
    fn gate_caching_only_when_order_gap_small() {
        // (e − j) / d = (83 − 80) / 100 = 3% < 5% → CachingOnly
        assert!(matches!(gate(&[row("hard", 110, 83, 80, 100)]), Gate::CachingOnly));
    }

    #[test]
    fn gate_marginal_in_between() {
        // (e − j) / d = (90 − 80) / 100 = 10% → Marginal
        assert!(matches!(gate(&[row("hard", 120, 90, 80, 100)]), Gate::Marginal));
    }

    #[test]
    fn gate_insufficient_when_no_full_size_row_optimal() {
        // The required full-size row only bracketed (j_status = "feasible", not "optimal")
        // → cannot conclude, must return Insufficient.
        let mut r = row("bigint-L0", 120, 83, 80, 100);
        r.j_status = "feasible".into();
        assert!(matches!(gate(&[r]), Gate::Insufficient));
    }
}
