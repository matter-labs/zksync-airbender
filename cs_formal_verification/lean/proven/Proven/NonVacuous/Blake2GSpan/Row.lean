module
public import Proven.NonVacuous.Blake2GSpan.Asserts
public import Proven.NonVacuous.Blake2GSpan.Lookups

@[expose] public section

/-! A G row's honest assignment of valid inputs satisfies its clock constraints (`Blake2G.clockConstraints` over
    the modeled setup, BabyBear): the imported assertions and lookups (`Asserts.lean`, `Lookups.lean`) and the 21
    timestamp queries: the invocation clock (1 mod 4), the two clock queries of each of the nine ports
    (`port_clock_contains`) and the two pointer alignments. -/

namespace Airbender.NonVacuous.Blake2GSpan
open Arithmetic Templates

variable {p : Nat} [Fact p.Prime]

theorem timestamps (x : RowInput) (valid : x.Valid) (hp : p = 2013265921) :
    ∀ i (h : i < (FlatOperation.lookups (Blake2G.importedConstraintsTimestampLookups (p := p))).length),
      ((FlatOperation.lookups (Blake2G.importedConstraintsTimestampLookups (p := p))).get ⟨i, h⟩).Contains
        (Verification.environment x.assignment) := by
  subst hp
  have sp := valid.statePointer
  have mp := valid.messagePointer
  have room := valid.room
  have invocation := valid.invocation
  simp only [Word.Bounded, limbBase, Trace.timestampBase] at sp mp room
  have port0 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[83, 84])
    (borrow := 85) (RowInput.assignment_1 x) (RowInput.assignment_2 x) (RowInput.assignment_83 x)
    (RowInput.assignment_84 x) ((RowInput.assignment_85 x).trans Nat.cast_one) (valid.previous 0)
    (by simp only [Trace.timestampBase]; omega)
  have port1 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[86, 87])
    (borrow := 88) (RowInput.assignment_1 x) (RowInput.assignment_2 x) (RowInput.assignment_86 x)
    (RowInput.assignment_87 x) ((RowInput.assignment_88 x).trans Nat.cast_one) (valid.previous 1)
    (by simp only [Trace.timestampBase]; omega)
  have port2 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[89, 90])
    (borrow := 91) (RowInput.assignment_1 x) (RowInput.assignment_2 x) (RowInput.assignment_89 x)
    (RowInput.assignment_90 x) ((RowInput.assignment_91 x).trans Nat.cast_one) (valid.previous 2)
    (by simp only [Trace.timestampBase]; omega)
  have port3 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[92, 93])
    (borrow := 94) (RowInput.assignment_1 x) (RowInput.assignment_2 x) (RowInput.assignment_92 x)
    (RowInput.assignment_93 x) ((RowInput.assignment_94 x).trans Nat.cast_one) (valid.previous 3)
    (by simp only [Trace.timestampBase]; omega)
  have port4 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[95, 96])
    (borrow := 97) (RowInput.assignment_1 x) (RowInput.assignment_2 x) (RowInput.assignment_95 x)
    (RowInput.assignment_96 x) ((RowInput.assignment_97 x).trans Nat.cast_one) (valid.previous 4)
    (by simp only [Trace.timestampBase]; omega)
  have port5 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[98, 99])
    (borrow := 100) (RowInput.assignment_1 x) (RowInput.assignment_2 x) (RowInput.assignment_98 x)
    (RowInput.assignment_99 x) ((RowInput.assignment_100 x).trans Nat.cast_one) (valid.previous 5)
    (by simp only [Trace.timestampBase]; omega)
  have port6 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[101, 102])
    (borrow := 103) (RowInput.assignment_1 x) (RowInput.assignment_2 x) (RowInput.assignment_101 x)
    (RowInput.assignment_102 x) ((RowInput.assignment_103 x).trans Nat.cast_one) (valid.previous 6)
    (by simp only [Trace.timestampBase]; omega)
  have port7 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[104, 105])
    (borrow := 106) (RowInput.assignment_1 x) (RowInput.assignment_2 x) (RowInput.assignment_104 x)
    (RowInput.assignment_105 x) ((RowInput.assignment_106 x).trans Nat.cast_one) (valid.previous 7)
    (by simp only [Trace.timestampBase]; omega)
  have port8 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[107, 108])
    (borrow := 109) (RowInput.assignment_1 x) (RowInput.assignment_2 x) (RowInput.assignment_107 x)
    (RowInput.assignment_108 x) ((RowInput.assignment_109 x).trans Nat.cast_one) (valid.previous 8)
    (by simp only [Trace.timestampBase]; omega)
  intro i h
  have size : i < 21 := by rwa [Blake2G.timestamp_count] at h
  interval_cases i <;> op_index
  · refine range_of_eval (n := x.invocation / 4) ?_ (by simp only [Trace.timestampBase]; omega) (by decide)
    quotient 1509949441 (show x.invocation = 1 + 4 * (x.invocation / 4) by omega)
  · exact port0.1
  · exact port0.2
  · exact port1.1
  · exact port1.2
  · exact port2.1
  · exact port2.2
  · exact port3.1
  · exact port3.2
  · exact port4.1
  · exact port4.2
  · exact port5.1
  · exact port5.2
  · exact port6.1
  · exact port6.2
  · exact port7.1
  · exact port7.2
  · exact port8.1
  · exact port8.2
  · refine range_of_eval (n := x.statePointer.lo / 64) ?_ (by simp only [Trace.timestampBase]; omega) (by decide)
    quotient 1981808641 (show x.statePointer.lo = 64 * (x.statePointer.lo / 64) by omega)
  · refine range_of_eval (n := x.messagePointer.lo / 64) ?_ (by simp only [Trace.timestampBase]; omega) (by decide)
    quotient 1981808641 (show x.messagePointer.lo = 64 * (x.messagePointer.lo / 64) by omega)

/-- The honest assignment of valid inputs satisfies the G row's clock constraints over the modeled setup. -/
theorem holds (x : RowInput) (valid : x.Valid) (hp : p = 2013265921) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment x.assignment)
      (Blake2G.clockConstraints (Blake2G.setupTable (p := p) Blake2G.Control.controllerRows)) := by
  refine Verification.holds_append (holds_of_get (asserts x valid _) (lookups x valid hp))
    (holds_of_get (fun i h => ?_) (timestamps x valid hp))
  have empty : FlatOperation.constraints (Blake2G.importedConstraintsTimestampLookups (p := p)) = [] := rfl
  rw [empty] at h
  exact absurd h (Nat.not_lt_zero i)

end Airbender.NonVacuous.Blake2GSpan
