module
public import Human.Trace.Machine.CodeWindows
public import Mathlib.Data.Bool.Basic

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Delegation
set_option warningAsError true
variable {α : Type}

/-- A matched request retires in the CPU interval that starts its four-tick cycle. -/
theorem window_retirement_iff {window : HashWindow} {request : Requests.Request p} {clock : Nat}
    (first : window.lower % 4 = 0) (last : window.upper % 4 = 0) (aligned : clock % 4 = 0)
    (tick : requestTick request = clock + 4) :
    window.select request = true ↔ window.lower ≤ clock ∧ clock < window.upper := by
  simp only [HashWindow.select, decide_eq_true_eq, tick]
  omega

/-- A code interval with only CSR rows has exactly its native CPU-row count of caller requests. -/
theorem code_window_request_count (rows : List α) (clock : α → Nat) (selected : α → Bool)
    (request : α → Requests.Request p) (window : HashWindow)
    (first : window.lower % 4 = 0) (last : window.upper % 4 = 0)
    (aligned : ∀ row ∈ rows, clock row % 4 = 0)
    (tick : ∀ row ∈ rows, selected row = true → requestTick (request row) = clock row + 4)
    (code : ∀ row ∈ rows, window.lower ≤ clock row ∧ clock row < window.upper → selected row = true) :
    (windowRequests ((rows.filter selected).map request) window).length =
      (rows.filter fun row => decide (window.lower ≤ clock row ∧ clock row < window.upper)).length := by
  rw [windowRequests, List.filter_map, List.length_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro row member
  cases choice : selected row with
  | false =>
    have outside : ¬(window.lower ≤ clock row ∧ clock row < window.upper) := by
      intro range
      have same := code row member range
      rw [choice] at same
      cases same
    simp only [Bool.and_false, decide_eq_false outside]
  | true =>
    simp only [Bool.and_true, Function.comp_def]
    apply Bool.decide_congr
    have relation := window_retirement_iff first last (aligned row member) (tick row member choice)
    simpa only [HashWindow.select, decide_eq_true_eq] using relation

/-- Code-derived row counts and CSR identities give the public protocol-window profile. -/
theorem code_window_profile (rows : List α) (clock : α → Nat) (selected : α → Bool)
    (request : α → Requests.Request p) (windows : List HashWindow)
    (separated : windows.Pairwise (fun first second => first.upper ≤ second.lower))
    (coverage : ∀ value ∈ (rows.filter selected).map request,
      value.csr ≠ Requests.csr .bigint ↔ ∃ window ∈ windows, window.select value = true)
    (aligned : ∀ row ∈ rows, clock row % 4 = 0)
    (tick : ∀ row ∈ rows, selected row = true → requestTick (request row) = clock row + 4)
    (scopes : ∀ window ∈ windows,
      window.lower % 4 = 0 ∧ window.upper % 4 = 0 ∧
      (rows.filter fun row => decide (window.lower ≤ clock row ∧ clock row < window.upper)).length = window.protocol.kinds.length ∧
      ∀ row ∈ rows, window.lower ≤ clock row ∧ clock row < window.upper → selected row = true ∧
        (request row).csr ∈ window.protocol.kinds.map (fun kind => kind.csr.toNat)) :
    HashWindowProfile ((rows.filter selected).map request) windows := by
  refine ⟨separated, coverage, ?_, ?_⟩
  · intro window member
    have scope := scopes window member
    exact (code_window_request_count rows clock selected request window scope.1 scope.2.1 aligned tick
      (fun row included range => (scope.2.2.2 row included range).1)).trans scope.2.2.1
  · intro window member value present
    have scope := scopes window member
    obtain ⟨source, selectedWindow⟩ := List.mem_filter.mp present
    obtain ⟨row, included, rfl⟩ := List.mem_map.mp source
    have native := List.mem_of_mem_filter included
    have called := (List.mem_filter.mp included).2
    have range := (window_retirement_iff scope.1 scope.2.1 (aligned row native) (tick row native called)).mp selectedWindow
    exact (scope.2.2.2 row native range).2

end Airbender.Trace.Machine.Proofs
