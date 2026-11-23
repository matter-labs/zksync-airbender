module
public import Proven.NonVacuous.Blake2RoundSpan.Valid
public import Proven.NonVacuous.Blake2RoundSpan.DiagonalTrace
public import Proven.NonVacuous.Blake2RoundSpan.ColumnLookups0
public import Proven.NonVacuous.Blake2RoundSpan.ColumnLookups1
public import Proven.NonVacuous.Blake2RoundSpan.ColumnLookups2
public import Proven.NonVacuous.Blake2RoundSpan.ColumnLookups3
public import Proven.NonVacuous.Blake2RoundSpan.DiagonalLookups0
public import Proven.NonVacuous.Blake2RoundSpan.DiagonalLookups1
public import Proven.NonVacuous.Blake2RoundSpan.DiagonalLookups2
public import Proven.NonVacuous.Blake2RoundSpan.DiagonalLookups3

@[expose] public section

/-! The 128 G queries of an honest round row (imported lookups 2 to 129) hold over BabyBear: each call's trace is
    the honest G row's (`column_trace`, `diagonal_trace`), whose table facts hold (`toTrace_rows`). -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Blake2Round.Proofs

variable {p : Nat} [Fact p.Prime]

theorem g_lookups (hp : p = 2013265921) {x : RowInput} (valid : x.Valid) {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) (n : Nat)
    (hn : n < L.length) (lower : 2 ≤ n) (upper : n < 130) :
    (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  have column (k : Nat) (hk : k < 4) : (columnTrace k (x.assignment (p := 2013265921))).Rows := by
    rw [column_trace rfl x hk]
    exact toTrace_rows (by omega) (valid.colCall hk)
  have diagonal (k : Nat) (hk : k < 4) : (diagonalTrace k (x.assignment (p := 2013265921))).Rows := by
    rw [diagonal_trace rfl x hk (valid.colCall (by omega))]
    exact toTrace_rows (by omega) (valid.diagCall hk)
  by_cases h0 : n < 18
  · exact column_lookups_0 rfl _ (column 0 (by decide)) hL n hn (by omega) h0
  by_cases h1 : n < 34
  · exact column_lookups_1 rfl _ (column 1 (by decide)) hL n hn (by omega) h1
  by_cases h2 : n < 50
  · exact column_lookups_2 rfl _ (column 2 (by decide)) hL n hn (by omega) h2
  by_cases h3 : n < 66
  · exact column_lookups_3 rfl _ (column 3 (by decide)) hL n hn (by omega) h3
  by_cases h4 : n < 82
  · exact diagonal_lookups_0 rfl _ (diagonal 0 (by decide)) hL n hn (by omega) h4
  by_cases h5 : n < 98
  · exact diagonal_lookups_1 rfl _ (diagonal 1 (by decide)) hL n hn (by omega) h5
  by_cases h6 : n < 114
  · exact diagonal_lookups_2 rfl _ (diagonal 2 (by decide)) hL n hn (by omega) h6
  exact diagonal_lookups_3 rfl _ (diagonal 3 (by decide)) hL n hn (by omega) upper

end Airbender.NonVacuous.Blake2RoundSpan
