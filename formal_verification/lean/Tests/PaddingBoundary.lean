import Airbender.Review.Trace.Padding
import Tests.TraceMemory
import Tests.InactiveRow

namespace Tests.PaddingBoundary
open Airbender Trace
set_option warningAsError true
set_option maxRecDepth 16384

/-- The retained inactive PC/result case, with native clock/lookups populated.
    Its raw state transition and x0 write are deliberately not stuttering. -/
def assignment (column : Nat) : ZMod babyBearModulus :=
  if column = 2 ∨ column = 19 then 4
  else if column = 21 then 8
  else if column = 33 then 123
  else if column = 42 ∨ column = 43 ∨ column = 44 then 1
  else 0

def row : Trace.Row babyBearModulus := ⟨.addSub, assignment⟩

theorem constraints (rom : Table (ZMod babyBearModulus) (fields 9)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment) (row.constraints rom) := by
  change FlatOperation.ConstraintsHoldFlat (Verification.environment assignment) AddSub.clockConstraints
  simp [AddSub.clockConstraints, AddSub.importedConstraints, AddSub.importedConstraintsTimestampLookups,
    FlatOperation.ConstraintsHoldFlat, Expression.eval, Verification.environment, assignment]
  all_goals repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains; decide)
    | (apply Trace.Proofs.range_contains; decide)
    | decide

theorem raw_inactive_effect : row.assignment row.columns.execute = 0 ∧
    row.start.word.toBitVec = 0 ∧ row.finish.word.toBitVec = 4 ∧ assignment 33 = 123 := by
  decide +kernel

theorem inactive_tuples_erased (value : MemoryToken babyBearModulus) :
    Airbender.PaddingBoundary.contribution (row.assignment row.columns.execute) value = none :=
  Airbender.PaddingBoundary.Proofs.contribution_zero value

theorem zero_value_is_not_padding :
    Airbender.PaddingBoundary.contribution (1 : ZMod babyBearModulus) (0 : Nat) = some 0 := by
  rfl

theorem product_mask_is_not_tuple_matching :
    ([some (1 : Nat)].map (Airbender.PaddingBoundary.evaluate fun _ => (1 : ZMod babyBearModulus))).prod =
      ([some (2 : Nat)].map (Airbender.PaddingBoundary.evaluate fun _ => (1 : ZMod babyBearModulus))).prod ∧
    ¬ ([some (1 : Nat)] : List (Option Nat)).Perm [some 2] := by
  decide +kernel

theorem nonboolean_selector_rejected : ¬ ((2 : ZMod babyBearModulus) = 0 ∨ (2 : ZMod babyBearModulus) = 1) := by
  decide +kernel

private def forgedTerminal (rom : Table (ZMod babyBearModulus) (fields 9)) : Data babyBearModulus where
  rows := [row, row]
  rom := rom
  initial := row.start
  terminal := row.finish
  initialMemory := []
  terminalMemory := []

theorem inactive_cannot_justify_terminal_change (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ¬ Airbender.PaddingBoundary.Binding (forgedTerminal rom) := by
  intro binding
  have matching := Airbender.PaddingBoundary.Proofs.projected_states binding
  have singleton : ([row.start] : List (PCState.State babyBearModulus)).Perm [row.finish] := by
    simpa [Airbender.PaddingBoundary.active, forgedTerminal, raw_inactive_effect.1] using matching
  have same : row.start = row.finish := by simpa using List.perm_singleton.mp singleton
  have pc := congrArg (fun state => state.word.toBitVec) same
  have unequal : row.start.word.toBitVec ≠ row.finish.word.toBitVec := by decide +kernel
  exact unequal pc

end Tests.PaddingBoundary
