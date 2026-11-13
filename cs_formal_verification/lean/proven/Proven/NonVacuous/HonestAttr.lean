module
public import Lean

@[expose] public section

/-- The per-column lemmas of the non-vacuity witnesses' honest assignments: `x.assignment k` is the cast of the
    honest value of column `k` (`Proven/NonVacuous/Blake2GSpan/Honest.lean`). -/
register_simp_attr honest_column
