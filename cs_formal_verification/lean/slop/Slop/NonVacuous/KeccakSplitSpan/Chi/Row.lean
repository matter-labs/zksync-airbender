module
public import Slop.NonVacuous.KeccakSplitSpan.Chi.Lookups
public import Slop.NonVacuous.KeccakSplitSpan.OpIndex
public import Slop.KeccakSplit.Chi5.OpIndex

@[expose] public section

/-! A chi row's honest assignment of valid inputs with its schedule's grouped read clocks satisfies its clock
    constraints (`Chi5.clockConstraints` over the exported setup, BabyBear): the 15 imported assertions (the active
    flag, the zero high limbs of x10, the six grouped read clocks at their schedule distances), the 18 imported
    lookups (`Lookups.lean`) and the two timestamp queries. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.Chi
open Arithmetic Keccak.Split Keccak.Split.SetupProofs

/-- The grouped read clocks of a chi call on plane `y`: x10 and x11 last written by the previous call, the lane
    of group `j` by theta+rho call `j`, `5 + y - j` calls before. -/
structure Clocks (x : RowInput) : Prop where
  registers : x.previous 0 + 4 = x.invocation + 2
  lane0 : x.previous 2 + 4 * (5 + plane x) = x.invocation + 2
  lane1 : x.previous 4 + 4 * (4 + plane x) = x.invocation + 2
  lane2 : x.previous 6 + 4 * (3 + plane x) = x.invocation + 2
  lane3 : x.previous 8 + 4 * (2 + plane x) = x.invocation + 2
  lane4 : x.previous 10 + 4 * (1 + plane x) = x.invocation + 2

variable {p : Nat} [Fact p.Prime]

theorem asserts (x : RowInput) (clocks : Clocks x) (setup : Table (ZMod p) (fields 11)) :
    ∀ i (h : i < (FlatOperation.constraints (Chi5.importedConstraints setup)).length),
      ((FlatOperation.constraints (Chi5.importedConstraints setup)).get ⟨i, h⟩).eval
        (Verification.environment (assignment x)) = 0 := by
  intro i h
  have size : i < 15 := by
    have count : (FlatOperation.constraints (Chi5.importedConstraints setup)).length = 15 := by rfl
    omega
  interval_cases i <;> op_index
  · simp only [Expression.eval, Verification.environment, honest_column]
    push_cast
    ring
  · simp only [Expression.eval, Verification.environment, honest_column, Nat.cast_zero]
  · simp only [Expression.eval, Verification.environment, honest_column, Nat.cast_zero]
  · cast_identity p clocks.registers
  · simp only [Expression.eval, Verification.environment, honest_column]
    ring
  · cast_identity p clocks.lane0
  · simp only [Expression.eval, Verification.environment, honest_column]
    ring
  · cast_identity p clocks.lane1
  · simp only [Expression.eval, Verification.environment, honest_column]
    ring
  · cast_identity p clocks.lane2
  · simp only [Expression.eval, Verification.environment, honest_column]
    ring
  · cast_identity p clocks.lane3
  · simp only [Expression.eval, Verification.environment, honest_column]
    ring
  · cast_identity p clocks.lane4
  · simp only [Expression.eval, Verification.environment, honest_column]
    ring

/-- The honest assignment of valid inputs satisfies the chi row's clock constraints. -/
theorem holds (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .chi5) (clocks : Clocks x)
    (hp : p = 2013265921) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (assignment x))
      (Chi5.clockConstraints (Chi5.setup (p := p))) := by
  refine Verification.holds_append (holds_of_get (asserts x clocks _) (lookups x valid kind hp))
    (holds_of_get (fun i h => ?_) fun i h => ?_)
  · have empty : FlatOperation.constraints (Chi5.importedConstraintsTimestampLookups (p := p)) = [] := rfl
    rw [empty] at h
    exact absurd h (Nat.not_lt_zero i)
  · subst hp
    have pointer := valid.pointer
    have room := valid.room
    have invocation := valid.invocation
    simp only [Word.Bounded, limbBase, Trace.timestampBase] at pointer room
    have size : i < 2 := by
      have count : (FlatOperation.lookups (Chi5.importedConstraintsTimestampLookups
        (p := 2013265921))).length = 2 := by rfl
      omega
    interval_cases i <;> op_index
    · refine range_of_eval (n := x.invocation / 4) ?_ (by simp only [Trace.timestampBase]; omega) (by decide)
      quotient 1509949441 (show x.invocation = 1 + 4 * (x.invocation / 4) by omega)
    · refine range_of_eval (n := (x.read 1).lo / 256) ?_ (by simp only [Trace.timestampBase]; omega) (by decide)
      quotient (-7864320) (show (x.read 1).lo = 256 * ((x.read 1).lo / 256) by omega)

end Airbender.NonVacuous.KeccakSplitSpan.Chi
