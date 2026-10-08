import Airbender.Review.Trace.Theorems

namespace Tests.TraceHistory
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384

-- Two reads of x0 refresh its clock from 0 to 4 to 5, then x1 is written at 6.
-- The malformed variant reads x0 at previous-clock 2: the local constraints allow
-- that bounded value, but the native memory matching has no corresponding write.
private def assignment (malformed : Bool) (v : Nat) : ZMod babyBearModulus :=
  if v = 23 then (if malformed then 2 else 0)
  else if v = 2 ∨ v = 19 ∨ v = 27 then 4
  else if v = 21 then 8
  else if v = 4 ∨ v = 7 ∨ v = 10 ∨ v = 42 ∨ v = 43 ∨ v = 44 then 1
  else 0

private def row (malformed : Bool) : Trace.Row babyBearModulus :=
  ⟨.addSub, assignment malformed⟩

private def token (register clock : Nat) : Trace.MemoryToken babyBearModulus :=
  ⟨Nat.pair 0 (Nat.pair register 0), (clock, 0), 0⟩

private def trace (rom : Table (ZMod babyBearModulus) (fields 9)) (malformed : Bool) :
    Trace.Data babyBearModulus where
  rows := [row malformed]
  rom := rom
  initial := (row malformed).start
  terminal := (row malformed).finish
  initialMemory := [token 0 0, token 1 0]
  terminalMemory := [token 0 5, token 1 6]

theorem local_satisfies (malformed : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (assignment malformed))
      AddSub.clockConstraints := by
  cases malformed <;>
    simp [AddSub.clockConstraints, AddSub.importedConstraints,
      AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
      Expression.eval, Verification.environment, assignment]
  all_goals repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, assignment, Arithmetic.limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus])
    | (apply Trace.Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, assignment, Trace.timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus])
    | norm_num [babyBearModulus]

theorem accepted (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Trace.Accepted (trace rom false) := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact local_satisfies false
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · dsimp only [trace]
    decide

private theorem boundary (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Trace.ClockBoundary (trace rom false) := by
  dsimp only [trace]
  constructor
  · change 4 < Trace.timestampBase ∧ 0 < Trace.timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro actual member
    simp at member
    rcases member with rfl | rfl <;> constructor <;> decide

/-- The fixture supplies no per-row ClockInputs. They follow from native matching. -/
theorem derived_clock (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Trace.ClockEffects (row false).columns (row false).assignment :=
  Trace.clocks (accepted rom) (boundary rom) _ (List.mem_singleton_self _)

theorem terminal_eight (rom : Table (ZMod babyBearModulus) (fields 9)) :
    (Trace.timeOfPair (trace rom false).terminal.timestamp).value = 8 := by
  have result := Trace.terminal_clock (accepted rom) (boundary rom)
  change _ = 8 at result
  exact result

theorem unmatched_previous_rejected (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ¬ Trace.Accepted (trace rom true) := by
  intro accepted
  have readMember : token 0 2 ∈ (trace rom true).rows.flatMap Trace.Row.reads := by
    dsimp only [trace]
    decide
  have matched := accepted.memory.mem_iff.mpr (List.mem_append_right _ readMember)
  have absent : token 0 2 ∉ (trace rom true).initialMemory ++
      (trace rom true).rows.flatMap Trace.Row.writes := by
    dsimp only [trace]
    decide
  exact absent matched

end Tests.TraceHistory
