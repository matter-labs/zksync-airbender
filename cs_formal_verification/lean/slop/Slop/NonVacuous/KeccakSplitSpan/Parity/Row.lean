module
public import Slop.NonVacuous.KeccakSplitSpan.Parity.Asserts
public import Slop.NonVacuous.KeccakSplitSpan.Parity.Lookups
public import Slop.NonVacuous.KeccakSplitSpan.OpIndex

@[expose] public section

/-! A column-parity row's honest assignment of valid inputs satisfies its clock constraints
    (`ColumnParity.clockConstraints` over the exported setup, BabyBear): the imported assertions and lookups
    (`Asserts.lean`, `Lookups.lean`) and the 30 timestamp queries: the invocation clock (1 mod 4), the two clock
    queries of each of the fourteen ports (`port_clock_contains`) and the pointer alignment. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.Parity
open Arithmetic Keccak.Split

variable {p : Nat} [Fact p.Prime]

theorem timestamps (x : RowInput) (valid : x.Valid) (previous : ∀ j < 14, x.previous j < x.invocation + 2)
    (hp : p = 2013265921) :
    ∀ i (h : i < (FlatOperation.lookups (ColumnParity.importedConstraintsTimestampLookups (p := p))).length),
      ((FlatOperation.lookups (ColumnParity.importedConstraintsTimestampLookups (p := p))).get ⟨i, h⟩).Contains
        (Verification.environment (assignment x)) := by
  subst hp
  have pointer := valid.pointer
  have room := valid.room
  have invocation := valid.invocation
  simp only [Word.Bounded, limbBase, Trace.timestampBase] at pointer room
  have port0 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[123, 124])
    (borrow := 125) (assignment_1 x) (assignment_2 x) (assignment_123 x) (assignment_124 x)
    ((assignment_125 x).trans Nat.cast_one) (previous 0 (by decide)) (by simp only [Trace.timestampBase]; omega)
  have port1 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[126, 127])
    (borrow := 128) (assignment_1 x) (assignment_2 x) (assignment_126 x) (assignment_127 x)
    ((assignment_128 x).trans Nat.cast_one) (previous 1 (by decide)) (by simp only [Trace.timestampBase]; omega)
  have port2 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[129, 130])
    (borrow := 131) (assignment_1 x) (assignment_2 x) (assignment_129 x) (assignment_130 x)
    ((assignment_131 x).trans Nat.cast_one) (previous 2 (by decide)) (by simp only [Trace.timestampBase]; omega)
  have port3 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[132, 133])
    (borrow := 134) (assignment_1 x) (assignment_2 x) (assignment_132 x) (assignment_133 x)
    ((assignment_134 x).trans Nat.cast_one) (previous 3 (by decide)) (by simp only [Trace.timestampBase]; omega)
  have port4 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[135, 136])
    (borrow := 137) (assignment_1 x) (assignment_2 x) (assignment_135 x) (assignment_136 x)
    ((assignment_137 x).trans Nat.cast_one) (previous 4 (by decide)) (by simp only [Trace.timestampBase]; omega)
  have port5 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[138, 139])
    (borrow := 140) (assignment_1 x) (assignment_2 x) (assignment_138 x) (assignment_139 x)
    ((assignment_140 x).trans Nat.cast_one) (previous 5 (by decide)) (by simp only [Trace.timestampBase]; omega)
  have port6 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[141, 142])
    (borrow := 143) (assignment_1 x) (assignment_2 x) (assignment_141 x) (assignment_142 x)
    ((assignment_143 x).trans Nat.cast_one) (previous 6 (by decide)) (by simp only [Trace.timestampBase]; omega)
  have port7 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[144, 145])
    (borrow := 146) (assignment_1 x) (assignment_2 x) (assignment_144 x) (assignment_145 x)
    ((assignment_146 x).trans Nat.cast_one) (previous 7 (by decide)) (by simp only [Trace.timestampBase]; omega)
  have port8 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[147, 148])
    (borrow := 149) (assignment_1 x) (assignment_2 x) (assignment_147 x) (assignment_148 x)
    ((assignment_149 x).trans Nat.cast_one) (previous 8 (by decide)) (by simp only [Trace.timestampBase]; omega)
  have port9 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[150, 151])
    (borrow := 152) (assignment_1 x) (assignment_2 x) (assignment_150 x) (assignment_151 x)
    ((assignment_152 x).trans Nat.cast_one) (previous 9 (by decide)) (by simp only [Trace.timestampBase]; omega)
  have port10 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[153, 154])
    (borrow := 155) (assignment_1 x) (assignment_2 x) (assignment_153 x) (assignment_154 x)
    ((assignment_155 x).trans Nat.cast_one) (previous 10 (by decide)) (by simp only [Trace.timestampBase]; omega)
  have port11 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[156, 157])
    (borrow := 158) (assignment_1 x) (assignment_2 x) (assignment_156 x) (assignment_157 x)
    ((assignment_158 x).trans Nat.cast_one) (previous 11 (by decide)) (by simp only [Trace.timestampBase]; omega)
  have port12 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[159, 160])
    (borrow := 161) (assignment_1 x) (assignment_2 x) (assignment_159 x) (assignment_160 x)
    ((assignment_161 x).trans Nat.cast_one) (previous 12 (by decide)) (by simp only [Trace.timestampBase]; omega)
  have port13 := port_clock_contains (p := 2013265921) (by decide) (columns := #v[162, 163])
    (borrow := 164) (assignment_1 x) (assignment_2 x) (assignment_162 x) (assignment_163 x)
    ((assignment_164 x).trans Nat.cast_one) (previous 13 (by decide)) (by simp only [Trace.timestampBase]; omega)
  intro i h
  have size : i < 30 := by
    have count : (FlatOperation.lookups (ColumnParity.importedConstraintsTimestampLookups
      (p := 2013265921))).length = 30 := by rfl
    omega
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
  · exact port9.1
  · exact port9.2
  · exact port10.1
  · exact port10.2
  · exact port11.1
  · exact port11.2
  · exact port12.1
  · exact port12.2
  · exact port13.1
  · exact port13.2
  · refine range_of_eval (n := (x.read 1).lo / 256) ?_ (by simp only [Trace.timestampBase]; omega) (by decide)
    quotient (-7864320) (show (x.read 1).lo = 256 * ((x.read 1).lo / 256) by omega)

/-- The honest assignment of valid inputs satisfies the column-parity row's clock constraints. -/
theorem holds (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .columnParity)
    (previous : ∀ j < 14, x.previous j < x.invocation + 2) (hp : p = 2013265921) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (assignment x))
      (ColumnParity.clockConstraints (ColumnParity.setup (p := p))) := by
  refine Verification.holds_append (holds_of_get (asserts x _) (lookups x valid kind hp))
    (holds_of_get (fun i h => ?_) (timestamps x valid previous hp))
  have empty : FlatOperation.constraints (ColumnParity.importedConstraintsTimestampLookups (p := p)) = [] := rfl
  rw [empty] at h
  exact absurd h (Nat.not_lt_zero i)

end Airbender.NonVacuous.KeccakSplitSpan.Parity
