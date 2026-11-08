module
public import Slop.Blake2Round.GTrace
public import Slop.Blake2Round.Lookups
public import Slop.Blake2Round.OpIndex
public import Slop.Eval
public import Mathlib.Tactic.ReduceModChar

@[expose] public section

set_option warningAsError true

/-!
From one evaluated table row (`RowFacts`) to the chunk fact of a `GTrace` field.
Each conversion takes the equalities between the evaluated query columns and the
trace fields; the per-call modules prove them by unfolding and field arithmetic.
-/

namespace Airbender.Blake2Round.Proofs

set_option maxHeartbeats 2000000

/-- Equality of linear forms over BabyBear, with coefficients reduced modulo the prime. -/
macro "mod_ring" : tactic => `(tactic| (rw [← sub_eq_zero]; ring_nf; try reduce_mod_char))

variable {p : Nat}

theorem rows_of_4 {a b c a' b' c' : ZMod p} {d e : Nat}
    (h : RowFacts 4 a.val b.val c.val d e) (ha : a = a') (hb : b = b') (hc : c = c') :
    ChunkXor 8 a'.val b'.val c'.val := by
  subst ha hb hc
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem rows_of_19 {a b c a' b' c' : ZMod p} {d e : Nat}
    (h : RowFacts 19 a.val b.val c.val d e) (ha : a = a') (hb : b = b') (hc : c = c') :
    ChunkXor 7 a'.val b'.val c'.val := by
  subst ha hb hc
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem rows_of_20 {a b c a' b' c' : ZMod p} {d e : Nat}
    (h : RowFacts 20 a.val b.val c.val d e) (ha : a = a') (hb : b = b') (hc : c = c') :
    ChunkXor 9 a'.val b'.val c'.val := by
  subst ha hb hc
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem rows_of_55 {a b c d a' b' c' d' : ZMod p} {e : Nat}
    (h : RowFacts 55 a.val b.val c.val d.val e) (ha : a = a') (hb : b = b') (hc : c = c')
    (hd : d = d') : ChunkXor 8 a'.val b'.val d'.val ∧ c'.val < 3 := by
  subst ha hb hc hd
  exact ⟨⟨h.1, h.2.1, h.2.2.2.1⟩, h.2.2.1⟩

theorem rows_of_56 {a b c d a' b' c' d' : ZMod p} {e : Nat}
    (h : RowFacts 56 a.val b.val c.val d.val e) (ha : a = a') (hb : b = b') (hc : c = c')
    (hd : d = d') : ChunkXor 7 a'.val b'.val d'.val ∧ c'.val < 3 := by
  subst ha hb hc hd
  exact ⟨⟨h.1, h.2.1, h.2.2.2.1⟩, h.2.2.1⟩

theorem rows_of_57 {a b c d e a' b' c' d' e' : ZMod p}
    (h : RowFacts 57 a.val b.val c.val d.val e.val) (ha : a = a') (hb : b = b') (hc : c = c')
    (hd : d = d') (he : e = e') : SplitXor a'.val b'.val c'.val d'.val e'.val := by
  subst ha hb hc hd he
  exact h

/-- A Boolean column is a carry below 3. -/
theorem carry_of_flag [Fact p.Prime] {x x' : ZMod p} (h : x * (x + -1) = 0) (e : x = x') : x'.val < 3 := by
  subst e
  have flag : x = 0 ∨ x = 1 := by
    rcases mul_eq_zero.mp h with zero | one
    · exact Or.inl zero
    · exact Or.inr (by linear_combination one)
  have := Arithmetic.boolean_val flag
  omega

end Airbender.Blake2Round.Proofs
