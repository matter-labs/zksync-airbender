module
public import Proven.ISA.RV.Step
public import Proven.ISA.RV.Same

@[expose] public section
namespace RV
set_option warningAsError true

/-- Observable state agreement is preserved by a run of any length. -/
theorem run_same (n : Nat) {s t : State} (same : Same s t) : SameOpt (run n s) (run n t) := by
  induction n generalizing s t with
  | zero => exact same
  | succ n ih =>
    have progress := step_same same
    cases first : step s with
    | none =>
      cases last : step t with
      | none => simp [run, first, last, SameOpt]
      | some next => simp [first, last, SameOpt] at progress
    | some next =>
      cases last : step t with
      | none => simp [first, last, SameOpt] at progress
      | some other =>
        have states : Same next other := by simpa only [first, last, SameOpt] using progress
        simpa only [run, first, last, Option.bind_some] using ih states

end RV
