module
public import Slop.NonVacuous.KeccakSplitSpan.ThetaRho.Asserts
public import Slop.NonVacuous.KeccakSplitSpan.ThetaRho.Lookups
public import Slop.NonVacuous.KeccakSplitSpan.OpIndex

@[expose] public section

/-! A theta+rho row's honest assignment of valid inputs with its schedule's grouped read clocks satisfies its clock
    constraints (`ThetaRho.clockConstraints` over the exported setup, BabyBear): the imported assertions and lookups
    (`Asserts.lean`, `Lookups.lean`) and the two timestamp queries, the invocation clock (1 mod 4) and the pointer
    alignment. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
open Arithmetic Keccak.Split

variable {p : Nat} [Fact p.Prime]

/-- The honest assignment of valid inputs satisfies the theta+rho row's clock constraints. -/
theorem holds (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (clocks : Clocks x)
    (hp : p = 2013265921) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (assignment x))
      (ThetaRho.clockConstraints (ThetaRho.setup (p := p))) := by
  refine Verification.holds_append (holds_of_get (asserts x valid kind clocks _) (lookups x valid kind hp))
    (holds_of_get (fun i h => ?_) fun i h => ?_)
  · have empty : FlatOperation.constraints (ThetaRho.importedConstraintsTimestampLookups (p := p)) = [] := rfl
    rw [empty] at h
    exact absurd h (Nat.not_lt_zero i)
  · subst hp
    have pointer := valid.pointer
    have room := valid.room
    have invocation := valid.invocation
    simp only [Word.Bounded, limbBase, Trace.timestampBase] at pointer room
    have size : i < 2 := by
      have count : (FlatOperation.lookups (ThetaRho.importedConstraintsTimestampLookups
        (p := 2013265921))).length = 2 := by rfl
      omega
    interval_cases i <;> op_index
    · refine range_of_eval (n := x.invocation / 4) ?_ (by simp only [Trace.timestampBase]; omega) (by decide)
      quotient 1509949441 (show x.invocation = 1 + 4 * (x.invocation / 4) by omega)
    · refine range_of_eval (n := (x.read 1).lo / 256) ?_ (by simp only [Trace.timestampBase]; omega) (by decide)
      quotient (-7864320) (show (x.read 1).lo = 256 * ((x.read 1).lo / 256) by omega)

end Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
