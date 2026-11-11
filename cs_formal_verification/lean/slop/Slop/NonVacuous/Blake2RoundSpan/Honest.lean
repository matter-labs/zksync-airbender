module
public import Slop.NonVacuous.Blake2GSpan.Honest
public import Human.Circuits.Blake2Round.Preparation
public import Slop.Blake2Round.Schedule

@[expose] public section

/-! The honest assignment of one extended-control Blake2s round row (`Blake2Round.importedConstraints`' columns,
    numbered as the artifact numbers them) in the plain mode (no compression, no reduced rounds: x12's three
    control bits are zero): computed from the round, the two pointers, the eight state, sixteen extended-state and
    sixteen message words read, the previous (low) clocks of the 43 ports and the invocation clock. The eight G
    calls are Blake2s G rows (`Blake2GSpan.RowInput`) on the prepared lanes and the scheduled message words; every
    other column is the honest value of the imported equations. -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Arithmetic

/-- The inputs of one round row. -/
structure RowInput where
  round : Fin 10
  statePointer : Word
  messagePointer : Word
  state : Nat → Word
  extended : Nat → Word
  message : Nat → Word
  previous : Nat → Nat
  invocation : Nat

/-- A G call on six words (the G row's other inputs are unused). -/
def gCall (a b c d mx my : Word) : Blake2GSpan.RowInput := ⟨0, ⟨0, 0⟩, ⟨0, 0⟩, a, b, c, d, mx, my, fun _ => 0, 1⟩

namespace RowInput
variable (x : RowInput)

/-- The Blake2s IV word `i`. -/
def ivWord (i : Nat) : Word := Blake2Round.Preparation.iv.toList.getD i ⟨0, 0⟩

/-- Prepared lane `L`: the first round starts from the chaining state and the IV (lanes 12 and 14 kept), later
    rounds from the extended state. -/
def lane (L : Nat) : Word :=
  if x.round.val = 0 then
    (if L < 8 then x.state L else if L = 12 ∨ L = 14 then x.extended L else ivWord (L - 8))
  else x.extended L

/-- Scheduled message word `j`. -/
def sched (j : Nat) : Word := x.message (Blake2Round.Schedule.Proofs.column x.round (Fin.ofNat 16 j)).val

/-- Column G call `k`. -/
def colCall (k : Nat) : Blake2GSpan.RowInput :=
  gCall (x.lane k) (x.lane (4 + k)) (x.lane (8 + k)) (x.lane (12 + k)) (x.sched (2 * k)) (x.sched (2 * k + 1))

/-- The four written words of a G call. -/
def outA (g : Blake2GSpan.RowInput) : Word := ⟨g.a2lo, g.a2hi⟩
def outB (g : Blake2GSpan.RowInput) : Word := ⟨g.b2lo, g.b2hi⟩
def outC (g : Blake2GSpan.RowInput) : Word := ⟨g.c2lo, g.c2hi⟩
def outD (g : Blake2GSpan.RowInput) : Word := ⟨g.d2lo, g.d2hi⟩

/-- Lane `L` after the column step. -/
def mixed (L : Nat) : Word :=
  if L / 4 = 0 then outA (x.colCall (L % 4)) else if L / 4 = 1 then outB (x.colCall (L % 4))
  else if L / 4 = 2 then outC (x.colCall (L % 4)) else outD (x.colCall (L % 4))

/-- Diagonal G call `k`. -/
def diagCall (k : Nat) : Blake2GSpan.RowInput :=
  gCall (x.mixed k) (x.mixed (4 + (k + 1) % 4)) (x.mixed (8 + (k + 2) % 4)) (x.mixed (12 + (k + 3) % 4))
    (x.sched (8 + 2 * k)) (x.sched (9 + 2 * k))

/-- Extended-state word `L` after the round (written back). -/
def out (L : Nat) : Word :=
  if L / 4 = 0 then outA (x.diagCall (L % 4)) else if L / 4 = 1 then outB (x.diagCall ((L % 4 + 3) % 4))
  else if L / 4 = 2 then outC (x.diagCall ((L % 4 + 2) % 4)) else outD (x.diagCall ((L % 4 + 1) % 4))

/-- A limb of a word. -/
def limb (word : Word) (h : Nat) : Nat := if h = 0 then word.lo else word.hi

/-- Column `j` of the final XOR of limb `h` of chaining word `i`, from the diagonal calls' values. Words 0 to 3 XOR
    the chaining limb `C` with extended word `8 + i` (`E₁`, call `(i + 2) % 4`'s `c`) in 7/9-bit chunks, then with
    word `i` (`E₂`, call `i`'s `a`); words 4 to 7 with word `i` (`E₁`, call `(i + 3) % 4`'s `b`, as its 9/7-bit
    rotation chunks) and then byte-wise with word `8 + i` (`E₂`, call `(i + 1) % 4`'s `d`, as its bytes). -/
def finalSlot (i h j : Nat) : Nat :=
  let C := limb (x.state i) h
  if i < 4 then
    let g₁ := x.diagCall ((i + 2) % 4)
    let g₂ := x.diagCall i
    let E₁ := if h = 0 then g₁.c2lo else g₁.c2hi
    let E₂ := if h = 0 then g₂.a2lo else g₂.a2hi
    let s₁ := C % 128 ^^^ E₁ % 128
    let s₂ := C / 128 ^^^ E₁ / 128
    if j = 0 then C % 128 else if j = 1 then s₁ else if j = 2 then s₂ else if j = 3 then E₂ % 256 / 128
    else if j = 4 then s₁ ^^^ E₂ % 128 else s₂ ^^^ E₂ / 128
  else
    let g₁ := x.diagCall ((i + 3) % 4)
    let g₂ := x.diagCall ((i + 1) % 4)
    let low₁ := if h = 0 then g₁.xf1 else g₁.xf3
    let high₁ := if h = 0 then g₁.xf2 else g₁.xf0
    let low₂ := if h = 0 then g₂.xe1 else g₂.xe3
    let high₂ := if h = 0 then g₂.xe2 else g₂.xe0
    let s₁ := low₁ ^^^ C % 512
    let s₂ := high₁ ^^^ C / 512
    if j = 0 then C % 512 else if j = 1 then s₁ else if j = 2 then s₂ else if j = 3 then s₁ / 256
    else if j = 4 then low₂ ^^^ s₁ % 256 else high₂ ^^^ (s₁ / 256 + 2 * s₂)

/-- The round's final flag: round 10. -/
def final : Bool := x.round.val = 9

/-- Limb `h` of the written chaining word `i`: the final XOR in the last round, the read limb otherwise. -/
def finalLimb (i h : Nat) : Nat :=
  if x.final then x.finalSlot i h 4 + (if i < 4 then 128 else 256) * x.finalSlot i h 5 else limb (x.state i) h

/-- Read limb `j % 2` (`j < 2`) or written limb (`j ≥ 2`) of state port word `i` (8 chaining, 16 extended). -/
def portLimb (i j : Nat) : Nat :=
  if i < 8 then (if j < 2 then limb (x.state i) j else x.finalLimb i (j - 2))
  else (if j < 2 then limb (x.extended (i - 8)) j else limb (x.out (i - 8)) (j - 2))

/-- The control word's high limb: the round bit `3 + round`. -/
def control : Nat := 8 * 2 ^ x.round.val

/-- Slot `i` of column G call `k` (columns `256 + 40 k + i`). -/
def colSlot (k i : Nat) : Nat :=
  let g := x.colCall k
  match i with
  | 0 => g.a1lo % 256 | 1 => g.carryA0 | 2 => g.a1hi % 256 | 3 => g.carryA1
  | 4 => g.d.lo % 256 | 5 => g.d.hi % 256 | 6 => g.xd0 | 7 => g.xd1 | 8 => g.xd2 | 9 => g.xd3
  | 10 => g.c1lo % 8 | 11 => g.c1lo / 8 % 512 | 12 => g.carryC0
  | 13 => g.c1hi % 8 | 14 => g.c1hi / 8 % 512 | 15 => g.carryC1
  | 16 => g.b.lo % 8 | 17 => g.b.lo / 8 % 512 | 18 => g.b.hi % 8 | 19 => g.b.hi / 8 % 512
  | 20 => g.xb1 | 21 => g.xb4 | 22 => g.xb2 + 16 * g.xb3 | 23 => g.xb5 + 16 * g.xb0
  | 24 => g.a2lo % 256 | 25 => g.carryA2 | 26 => g.a2hi % 256 | 27 => g.carryA3
  | 28 => g.xe1 | 29 => g.xe3 | 30 => g.xe0 | 31 => g.xe2
  | 32 => g.c2lo % 128 | 33 => g.carryC2 | 34 => g.c2hi % 128 | 35 => g.carryC3
  | 36 => g.xf1 | 37 => g.xf3 | 38 => g.xf0 | _ => g.xf2

/-- Slot `i` of diagonal G call `k` (columns `416 + 30 k + i`). -/
def diagSlot (k i : Nat) : Nat :=
  let g := x.diagCall k
  match i with
  | 0 => g.a1lo % 256 | 1 => g.carryA0 | 2 => g.a1hi % 256 | 3 => g.carryA1
  | 4 => g.xd0 | 5 => g.xd1 | 6 => g.xd2 | 7 => g.xd3
  | 8 => g.c1lo % 8 | 9 => g.c1lo / 8 % 512 | 10 => g.carryC0
  | 11 => g.c1hi % 8 | 12 => g.c1hi / 8 % 512 | 13 => g.carryC1
  | 14 => g.b.lo % 8 | 15 => g.b.lo / 8 % 512 | 16 => g.b.hi % 8 | 17 => g.b.hi / 8 % 512
  | 18 => g.xb1 | 19 => g.xb4 | 20 => g.xb2 + 16 * g.xb3 | 21 => g.xb5 + 16 * g.xb0
  | 22 => g.a2lo % 256 | 23 => g.a2hi % 256 | 24 => g.xe1 | 25 => g.xe3
  | 26 => g.c2lo % 128 | 27 => g.c2hi % 128 | 28 => g.xf1 | _ => g.xf3

/-- The prepared-lane columns 186 to 201: lanes 8 to 11, then 13, 15, 12, 14. -/
def suffixLane (n : Nat) : Nat :=
  if n < 8 then 8 + n / 2 else if n < 10 then 13 else if n < 12 then 15 else if n < 14 then 12 else 14

/-- The honest value of every column. -/
def column (n : Nat) : Nat :=
  if n < 5 then
    (if n = 0 then 1 else if n = 1 then x.invocation else if n = 2 then 0 else if n = 3 then x.statePointer.lo
      else x.statePointer.hi)
  else if n < 101 then x.portLimb ((n - 5) / 4) ((n - 5) % 4)
  else if n < 103 then (if n = 101 then x.messagePointer.lo else x.messagePointer.hi)
  else if n < 135 then limb (x.message ((n - 103) / 2)) ((n - 103) % 2)
  else if n < 139 then
    (if n = 136 then x.control else if n = 138 then 16 * (2 ^ x.round.val % 512) else 0)
  else if n < 152 then (if n = 142 + x.round.val then 1 else 0)
  else if n < 154 then (if n = 152 then (if x.final then 1 else 0) else if x.round.val = 0 then 1 else 0)
  else if n < 186 then
    (if (n - 154) % 4 = 0 then (x.state ((n - 154) / 4)).lo
      else if (n - 154) % 4 = 1 then (x.lane ((n - 154) / 4)).lo
      else if (n - 154) % 4 = 2 then (x.state ((n - 154) / 4)).hi else (x.lane ((n - 154) / 4)).hi)
  else if n < 202 then limb (x.lane (suffixLane (n - 186))) ((n - 186) % 2)
  else if n < 224 then 0
  else if n < 256 then limb (x.sched ((n - 224) / 2)) ((n - 224) % 2)
  else if n < 416 then x.colSlot ((n - 256) / 40) ((n - 256) % 40)
  else if n < 536 then x.diagSlot ((n - 416) / 30) ((n - 416) % 30)
  else if n < 632 then x.finalSlot ((n - 536) / 12) ((n - 536) / 6 % 2) ((n - 536) % 6)
  else if n < 761 then
    (if (n - 632) % 3 = 0 then x.previous ((n - 632) / 3) else if (n - 632) % 3 = 1 then 0 else 1)
  else 0

/-! The column definition on each of its ranges. -/

theorem column_head {n : Nat} (high : n < 5) :
    x.column n = (if n = 0 then 1 else if n = 1 then x.invocation else if n = 2 then 0 else if n = 3 then x.statePointer.lo
      else x.statePointer.hi) := by
  unfold column
  rw [ite_eq_left (by omega)]

theorem column_port {n : Nat} (low : 5 ≤ n) (high : n < 101) :
    x.column n = x.portLimb ((n - 5) / 4) ((n - 5) % 4) := by
  unfold column
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]

theorem column_messagePointer {n : Nat} (low : 101 ≤ n) (high : n < 103) :
    x.column n = (if n = 101 then x.messagePointer.lo else x.messagePointer.hi) := by
  unfold column
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

theorem column_message {n : Nat} (low : 103 ≤ n) (high : n < 135) :
    x.column n = limb (x.message ((n - 103) / 2)) ((n - 103) % 2) := by
  unfold column
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

theorem column_control {n : Nat} (low : 135 ≤ n) (high : n < 139) :
    x.column n = (if n = 136 then x.control else if n = 138 then 16 * (2 ^ x.round.val % 512) else 0) := by
  unfold column
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

theorem column_bits {n : Nat} (low : 139 ≤ n) (high : n < 152) :
    x.column n = (if n = 142 + x.round.val then 1 else 0) := by
  unfold column
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

theorem column_flags {n : Nat} (low : 152 ≤ n) (high : n < 154) :
    x.column n = (if n = 152 then (if x.final then 1 else 0) else if x.round.val = 0 then 1 else 0) := by
  unfold column
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

theorem column_prepared {n : Nat} (low : 154 ≤ n) (high : n < 186) :
    x.column n = (if (n - 154) % 4 = 0 then (x.state ((n - 154) / 4)).lo
      else if (n - 154) % 4 = 1 then (x.lane ((n - 154) / 4)).lo
      else if (n - 154) % 4 = 2 then (x.state ((n - 154) / 4)).hi else (x.lane ((n - 154) / 4)).hi) := by
  unfold column
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

theorem column_suffix {n : Nat} (low : 186 ≤ n) (high : n < 202) :
    x.column n = limb (x.lane (suffixLane (n - 186))) ((n - 186) % 2) := by
  unfold column
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

theorem column_products {n : Nat} (low : 202 ≤ n) (high : n < 224) :
    x.column n = 0 := by
  unfold column
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

theorem column_scheduled {n : Nat} (low : 224 ≤ n) (high : n < 256) :
    x.column n = limb (x.sched ((n - 224) / 2)) ((n - 224) % 2) := by
  unfold column
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

theorem column_columnCall {n : Nat} (low : 256 ≤ n) (high : n < 416) :
    x.column n = x.colSlot ((n - 256) / 40) ((n - 256) % 40) := by
  unfold column
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

theorem column_diagonalCall {n : Nat} (low : 416 ≤ n) (high : n < 536) :
    x.column n = x.diagSlot ((n - 416) / 30) ((n - 416) % 30) := by
  unfold column
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

theorem column_finalXor {n : Nat} (low : 536 ≤ n) (high : n < 632) :
    x.column n = x.finalSlot ((n - 536) / 12) ((n - 536) / 6 % 2) ((n - 536) % 6) := by
  unfold column
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

theorem column_clock {n : Nat} (low : 632 ≤ n) (high : n < 761) :
    x.column n = (if (n - 632) % 3 = 0 then x.previous ((n - 632) / 3) else if (n - 632) % 3 = 1 then 0 else 1) := by
  unfold column
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

end RowInput

/-- The row's assignment over the field. -/
def RowInput.assignment {p : Nat} (x : RowInput) (i : Nat) : ZMod p := (x.column i : ZMod p)

end Airbender.NonVacuous.Blake2RoundSpan
