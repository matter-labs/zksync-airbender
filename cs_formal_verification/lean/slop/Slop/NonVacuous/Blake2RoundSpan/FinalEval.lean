module
public import Slop.NonVacuous.Blake2RoundSpan.Valid
public import Slop.NonVacuous.Blake2RoundSpan.Queries
public import Slop.NonVacuous.Blake2RoundSpan.ColumnTrace
public import Slop.Eval

@[expose] public section

/-! Tactics for the honest round row's non-G queries and equations: evaluating an imported entry at the honest
    assignment (a column's range lemma, then its definition), unfolding the final-XOR slots, and the bounds a
    final-XOR limb needs. -/

namespace Airbender.NonVacuous.Blake2RoundSpan.RowInput
open Arithmetic

/-- The chunk widths of the final-XOR slots: 7/9-bit chunks for words 0 to 3, 9/7-bit chunks and bytes for words
    4 to 7. -/
theorem Valid.finalSlot_bounds {x : RowInput} (valid : x.Valid) {i h : Nat} (hi : i < 8) :
    (i < 4 → x.finalSlot i h 0 < 128 ∧ x.finalSlot i h 1 < 128 ∧ x.finalSlot i h 2 < 512 ∧
      x.finalSlot i h 3 ≤ 1 ∧ x.finalSlot i h 4 < 128 ∧ x.finalSlot i h 5 < 512) ∧
    (4 ≤ i → x.finalSlot i h 0 < 512 ∧ x.finalSlot i h 1 < 512 ∧ x.finalSlot i h 2 < 128 ∧
      x.finalSlot i h 3 ≤ 1 ∧ x.finalSlot i h 4 < 256 ∧ x.finalSlot i h 5 < 256) := by
  have C : limb (x.state i) h < 65536 := by
    have := valid.state i hi
    simp only [Word.Bounded, limbBase] at this
    unfold limb
    split_ifs <;> omega
  have xor {k m n : Nat} (hm : m < 2 ^ k) (hn : n < 2 ^ k) : m ^^^ n < 2 ^ k := Nat.xor_lt_two_pow hm hn
  constructor
  · intro low
    have o1 := (valid.diagCall (k := (i + 2) % 4) (by omega)).outputs
    have o2 := (valid.diagCall (k := i) low).outputs
    unfold finalSlot
    simp only [low, ↓reduceIte, Nat.reduceEqDiff]
    generalize limb (x.state i) h = c at C
    generalize hE1 : (if h = 0 then (x.diagCall ((i + 2) % 4)).c2lo else (x.diagCall ((i + 2) % 4)).c2hi) = E1
    generalize hE2 : (if h = 0 then (x.diagCall i).a2lo else (x.diagCall i).a2hi) = E2
    have e1 : E1 < 65536 := by rw [← hE1]; split_ifs <;> omega
    have e2 : E2 < 65536 := by rw [← hE2]; split_ifs <;> omega
    have s1 : c % 128 ^^^ E1 % 128 < 128 := xor (k := 7) (by omega) (by omega)
    have s2 : c / 128 ^^^ E1 / 128 < 512 := xor (k := 9) (by omega) (by omega)
    exact ⟨by omega, s1, s2, by omega, xor (k := 7) s1 (by omega), xor (k := 9) s2 (by omega)⟩
  · intro high
    have g1 := (valid.diagCall (k := (i + 3) % 4) (by omega)).xors
    have g2 := (valid.diagCall (k := (i + 1) % 4) (by omega)).xors
    unfold finalSlot
    simp only [show ¬ i < 4 by omega, ↓reduceIte, Nat.reduceEqDiff]
    generalize limb (x.state i) h = c at C
    generalize hl1 : (if h = 0 then (x.diagCall ((i + 3) % 4)).xf1 else (x.diagCall ((i + 3) % 4)).xf3) = l1
    generalize hh1 : (if h = 0 then (x.diagCall ((i + 3) % 4)).xf2 else (x.diagCall ((i + 3) % 4)).xf0) = h1
    generalize hl2 : (if h = 0 then (x.diagCall ((i + 1) % 4)).xe1 else (x.diagCall ((i + 1) % 4)).xe3) = l2
    generalize hh2 : (if h = 0 then (x.diagCall ((i + 1) % 4)).xe2 else (x.diagCall ((i + 1) % 4)).xe0) = h2
    have b1 : l1 < 512 := by rw [← hl1]; split_ifs <;> omega
    have b2 : h1 < 128 := by rw [← hh1]; split_ifs <;> omega
    have b3 : l2 < 256 := by rw [← hl2]; split_ifs <;> omega
    have b4 : h2 < 256 := by rw [← hh2]; split_ifs <;> omega
    have s1 : l1 ^^^ c % 512 < 512 := xor (k := 9) b1 (by omega)
    have s2 : h1 ^^^ c / 512 < 128 := xor (k := 7) b2 (by omega)
    exact ⟨by omega, s1, s2, by omega, xor (k := 8) b3 (by omega), xor (k := 8) b4 (by omega)⟩

end Airbender.NonVacuous.Blake2RoundSpan.RowInput

namespace Airbender.NonVacuous.Blake2RoundSpan

/-- Evaluate an entry of the honest round row: each column by its range (`RowInput.column_*`), the ports and the
    diagonal slots by definition. -/
scoped macro "honest_entry" : tactic => `(tactic| (
  eval_entry [Airbender.NonVacuous.Blake2RoundSpan.RowInput.assignment]
  try simp (disch := decide) only [Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_prepared,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_port,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_diagonalCall,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_finalXor,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.portLimb, Airbender.NonVacuous.Blake2RoundSpan.RowInput.out,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.outA, Airbender.NonVacuous.Blake2RoundSpan.RowInput.outB,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.outC, Airbender.NonVacuous.Blake2RoundSpan.RowInput.outD,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.limb, Airbender.NonVacuous.Blake2RoundSpan.RowInput.diagSlot,
    ↓reduceIte, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv,
    Nat.reduceMod]))

/-- A bound or identity of the final-XOR slots at literal indices: from the slot bounds in context, else by unfolding
    the slots, then arithmetic. -/
scoped macro "final_unfold" : tactic => `(tactic| first | omega | (
  (try simp only [Airbender.NonVacuous.Blake2RoundSpan.RowInput.finalSlot,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.limb, ↓reduceIte, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceAdd,
    Nat.reduceMod]) <;> omega))

/-- The bounds of a final-XOR limb of chaining word `i < 4`: its slots, its chaining word and the outputs of the two
    diagonal calls it reads. -/
scoped macro "final_bounds_low " valid:term:max i:num h:num a:num b:num : tactic => `(tactic| (
  have slots := (Airbender.NonVacuous.Blake2RoundSpan.RowInput.Valid.finalSlot_bounds $valid (i := $i) (h := $h)
    (by decide)).1 (by decide)
  have state := ($valid).state $i (by decide)
  simp only [Airbender.Arithmetic.Word.Bounded, Airbender.Arithmetic.limbBase] at state
  have outputsA := (($valid).diagCall (k := $a) (by decide)).outputs
  have outputsB := (($valid).diagCall (k := $b) (by decide)).outputs))

/-- The bounds of a final-XOR limb of chaining word `i ≥ 4`: its slots, its chaining word and the XOR chunks of the
    two diagonal calls it reads. -/
scoped macro "final_bounds_high " valid:term:max i:num h:num a:num b:num : tactic => `(tactic| (
  have slots := (Airbender.NonVacuous.Blake2RoundSpan.RowInput.Valid.finalSlot_bounds $valid (i := $i) (h := $h)
    (by decide)).2 (by decide)
  have state := ($valid).state $i (by decide)
  simp only [Airbender.Arithmetic.Word.Bounded, Airbender.Arithmetic.limbBase] at state
  have xorsA := (($valid).diagCall (k := $a) (by decide)).xors
  have xorsB := (($valid).diagCall (k := $b) (by decide)).xors))

end Airbender.NonVacuous.Blake2RoundSpan
