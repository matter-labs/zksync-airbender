module
public import Slop.NonVacuous.Blake2RoundSpan.Honest
public import Slop.Blake2Round.DiagonalG

@[expose] public section

/-! The honest assignment at the column families the G traces read, for a symbolic call `k`: the prepared lanes,
    the scheduled message words, the allocated slots of the column and diagonal calls and the written extended
    state. -/

namespace Airbender.NonVacuous.Blake2RoundSpan.RowInput
open Arithmetic

variable {p : Nat} (x : RowInput)

theorem assignment_colSlot {k i : Nat} (hk : k < 4) (hi : i < 40) :
    x.assignment (p := p) (256 + 40 * k + i) = (x.colSlot k i : ZMod p) := by
  rw [assignment, column_columnCall x (by omega) (by omega), show (256 + 40 * k + i - 256) / 40 = k by omega,
    show (256 + 40 * k + i - 256) % 40 = i by omega]

theorem assignment_diagSlot {k i : Nat} (hk : k < 4) (hi : i < 30) :
    x.assignment (p := p) (416 + 30 * k + i) = (x.diagSlot k i : ZMod p) := by
  rw [assignment, column_diagonalCall x (by omega) (by omega), show (416 + 30 * k + i - 416) / 30 = k by omega,
    show (416 + 30 * k + i - 416) % 30 = i by omega]

theorem assignment_laneLo {m : Nat} (hm : m < 8) :
    x.assignment (p := p) (155 + 4 * m) = ((x.lane m).lo : ZMod p) := by
  rw [assignment, column_prepared x (by omega) (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
    show (155 + 4 * m - 154) / 4 = m by omega]

theorem assignment_laneHi {m : Nat} (hm : m < 8) :
    x.assignment (p := p) (157 + 4 * m) = ((x.lane m).hi : ZMod p) := by
  rw [assignment, column_prepared x (by omega) (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    show (157 + 4 * m - 154) / 4 = m by omega]

theorem assignment_laneLo' {k : Nat} (hk : k < 4) :
    x.assignment (p := p) (171 + 4 * k) = ((x.lane (4 + k)).lo : ZMod p) := by
  rw [assignment, column_prepared x (by omega) (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
    show (171 + 4 * k - 154) / 4 = 4 + k by omega]

theorem assignment_laneHi' {k : Nat} (hk : k < 4) :
    x.assignment (p := p) (173 + 4 * k) = ((x.lane (4 + k)).hi : ZMod p) := by
  rw [assignment, column_prepared x (by omega) (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    show (173 + 4 * k - 154) / 4 = 4 + k by omega]

theorem assignment_suffixLo {k : Nat} (hk : k < 4) :
    x.assignment (p := p) (186 + 2 * k) = ((x.lane (8 + k)).lo : ZMod p) := by
  rw [assignment, column_suffix x (by omega) (by omega), suffixLane, ite_eq_left (by omega),
    show 8 + (186 + 2 * k - 186) / 2 = 8 + k by omega, show (186 + 2 * k - 186) % 2 = 0 by omega]
  rfl

theorem assignment_suffixHi {k : Nat} (hk : k < 4) :
    x.assignment (p := p) (187 + 2 * k) = ((x.lane (8 + k)).hi : ZMod p) := by
  rw [assignment, column_suffix x (by omega) (by omega), suffixLane, ite_eq_left (by omega),
    show 8 + (187 + 2 * k - 186) / 2 = 8 + k by omega, show (187 + 2 * k - 186) % 2 = 1 by omega]
  rfl

theorem assignment_dLaneLo {k : Nat} (hk : k < 4) :
    x.assignment (p := p) (Blake2Round.Proofs.columnDLane k) = ((x.lane (12 + k)).lo : ZMod p) := by
  interval_cases k <;> rfl

theorem assignment_dLaneHi {k : Nat} (hk : k < 4) :
    x.assignment (p := p) (Blake2Round.Proofs.columnDLane k + 1) = ((x.lane (12 + k)).hi : ZMod p) := by
  interval_cases k <;> rfl

theorem assignment_schedLo {j : Nat} (hj : j < 16) :
    x.assignment (p := p) (224 + 2 * j) = ((x.sched j).lo : ZMod p) := by
  rw [assignment, column_scheduled x (by omega) (by omega), show (224 + 2 * j - 224) / 2 = j by omega,
    show (224 + 2 * j - 224) % 2 = 0 by omega]
  rfl

theorem assignment_schedHi {j : Nat} (hj : j < 16) :
    x.assignment (p := p) (224 + 2 * j + 1) = ((x.sched j).hi : ZMod p) := by
  rw [assignment, column_scheduled x (by omega) (by omega), show (224 + 2 * j + 1 - 224) / 2 = j by omega,
    show (224 + 2 * j + 1 - 224) % 2 = 1 by omega]
  rfl

theorem assignment_outLo {L : Nat} (hL : L < 16) :
    x.assignment (p := p) (39 + 4 * L) = ((x.out L).lo : ZMod p) := by
  rw [assignment, column_port x (by omega) (by omega), show (39 + 4 * L - 5) / 4 = 8 + L by omega,
    show (39 + 4 * L - 5) % 4 = 2 by omega, portLimb, ite_eq_right (by omega), ite_eq_right (by omega),
    show 8 + L - 8 = L by omega]
  rfl

theorem assignment_outHi {L : Nat} (hL : L < 16) :
    x.assignment (p := p) (39 + 4 * L + 1) = ((x.out L).hi : ZMod p) := by
  rw [assignment, column_port x (by omega) (by omega), show (39 + 4 * L + 1 - 5) / 4 = 8 + L by omega,
    show (39 + 4 * L + 1 - 5) % 4 = 3 by omega, portLimb, ite_eq_right (by omega), ite_eq_right (by omega),
    show 8 + L - 8 = L by omega]
  rfl

theorem assignment_portRead {i h : Nat} (hi : i < 24) (hh : h < 2) :
    x.assignment (p := p) (5 + 4 * i + h) = (x.portLimb i h : ZMod p) := by
  rw [assignment, column_port x (by omega) (by omega), show (5 + 4 * i + h - 5) / 4 = i by omega,
    show (5 + 4 * i + h - 5) % 4 = h by omega]

theorem assignment_portWrite {i h : Nat} (hi : i < 24) (hh : h < 2) :
    x.assignment (p := p) (7 + 4 * i + h) = (x.portLimb i (2 + h) : ZMod p) := by
  rw [assignment, column_port x (by omega) (by omega), show (7 + 4 * i + h - 5) / 4 = i by omega,
    show (7 + 4 * i + h - 5) % 4 = 2 + h by omega]

theorem assignment_messageRead {i h : Nat} (hi : i < 16) (hh : h < 2) :
    x.assignment (p := p) (103 + 2 * i + h) = (limb (x.message i) h : ZMod p) := by
  rw [assignment, column_message x (by omega) (by omega), show (103 + 2 * i + h - 103) / 2 = i by omega,
    show (103 + 2 * i + h - 103) % 2 = h by omega]

theorem assignment_invocation : x.assignment (p := p) 1 = (x.invocation : ZMod p) := by
  rw [assignment, column_head x (by omega)]
  rfl

theorem assignment_invocationHigh : x.assignment (p := p) 2 = ((0 : Nat) : ZMod p) := by
  rw [assignment, column_head x (by omega)]
  rfl

theorem assignment_previous {j : Nat} (hj : j < 43) :
    x.assignment (p := p) (632 + 3 * j) = (x.previous j : ZMod p) := by
  rw [assignment, column_clock x (by omega) (by omega), ite_eq_left (by omega), show (632 + 3 * j - 632) / 3 = j by omega]

theorem assignment_previousHigh {j : Nat} (hj : j < 43) :
    x.assignment (p := p) (633 + 3 * j) = ((0 : Nat) : ZMod p) := by
  rw [assignment, column_clock x (by omega) (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

theorem assignment_borrow {j : Nat} (hj : j < 43) : x.assignment (p := p) (634 + 3 * j) = 1 := by
  rw [assignment, column_clock x (by omega) (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    Nat.cast_one]

/-! The lanes after the column step and the written extended state, by call. -/

theorem mixed_a {k : Nat} (hk : k < 4) : x.mixed k = outA (x.colCall k) := by
  unfold mixed
  rw [ite_eq_left (by omega), Nat.mod_eq_of_lt hk]

theorem mixed_b {k : Nat} (hk : k < 4) : x.mixed (4 + k) = outB (x.colCall k) := by
  unfold mixed
  rw [ite_eq_right (by omega), ite_eq_left (by omega), show (4 + k) % 4 = k by omega]

theorem mixed_c {k : Nat} (hk : k < 4) : x.mixed (8 + k) = outC (x.colCall k) := by
  unfold mixed
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), show (8 + k) % 4 = k by omega]

theorem mixed_d {k : Nat} (hk : k < 4) : x.mixed (12 + k) = outD (x.colCall k) := by
  unfold mixed
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), show (12 + k) % 4 = k by omega]

theorem out_a {k : Nat} (hk : k < 4) : x.out k = outA (x.diagCall k) := by
  unfold out
  rw [ite_eq_left (by omega), Nat.mod_eq_of_lt hk]

theorem out_b {k : Nat} (hk : k < 4) : x.out (4 + (k + 1) % 4) = outB (x.diagCall k) := by
  unfold out
  rw [ite_eq_right (by omega), ite_eq_left (by omega), show ((4 + (k + 1) % 4) % 4 + 3) % 4 = k by omega]

theorem out_c {k : Nat} (hk : k < 4) : x.out (8 + (k + 2) % 4) = outC (x.diagCall k) := by
  unfold out
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), show ((8 + (k + 2) % 4) % 4 + 2) % 4 = k by omega]

theorem out_d {k : Nat} (hk : k < 4) : x.out (12 + (k + 3) % 4) = outD (x.diagCall k) := by
  unfold out
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), show ((12 + (k + 3) % 4) % 4 + 1) % 4 = k by omega]

end Airbender.NonVacuous.Blake2RoundSpan.RowInput
