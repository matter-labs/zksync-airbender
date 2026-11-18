module
public import Human.Import.SetupBlocks
public import Mathlib.Tactic.Ring

@[expose] public section

/- Row meaning of compressed setup columns without expanding them: a block agrees with a row formula on the rows it
   covers (`BlockOk`, `Matches`), and then the decoded column is the formula on those rows (`decode_of_matches`). The
   kernel scans of `Proven.Setup.Scan` establish `Matches`. -/

namespace Airbender.Import.Setup.Proofs

open Airbender.Import.Setup

/-- Total number of rows covered by a block list. -/
def total : List Block → Nat
  | [] => 0
  | b :: bs => b.len + total bs

/-- A block agrees with `spec` on the rows it covers, starting at row `s`. -/
def BlockOk (spec : Nat → Int) (s : Nat) (b : Block) : Prop :=
  ∀ i < b.len, b.valueAt i = spec (s + i)

/-- Every block of a list agrees with `spec`, the list starting at row `s`. -/
def Matches (spec : Nat → Int) : Nat → List Block → Prop
  | _, [] => True
  | s, b :: bs => BlockOk spec s b ∧ Matches spec (s + b.len) bs

theorem decode_of_matches {spec : Nat → Int} {s : Nat} {bs : List Block}
    (h : Matches spec s bs) : ∀ n < total bs, decode bs n = spec (s + n) := by
  induction bs generalizing s with
  | nil => intro n hn; simp [total] at hn
  | cons b bs ih =>
    intro n hn
    simp only [total] at hn
    obtain ⟨hb, hbs⟩ := h
    simp only [decode]
    split
    · exact hb n ‹_›
    · rw [ih hbs (n - b.len) (by omega)]
      congr 1
      omega

private theorem array_getD (vs : Array Int) (j : Nat) (hj : j < vs.toList.length) :
    vs.getD j 0 = vs.toList[j] := by
  simp only [Array.length_toList] at hj
  simp [Array.getD, hj]

theorem periodic_ok {spec : Nat → Int} {s r : Nat} {stride : Int} {vs : Array Int}
    (h : ∀ q < r, ∀ j (hj : j < vs.toList.length),
      vs.toList[j] + stride * q = spec (s + q * vs.toList.length + j)) :
    BlockOk spec s (.periodic r stride vs) := by
  intro i hi
  simp only [Block.len] at hi
  have pos : 0 < vs.size := by
    rcases Nat.eq_zero_or_pos vs.size with z | p
    · simp [z] at hi
    · exact p
  have hj : i % vs.size < vs.toList.length := by simpa using Nat.mod_lt i pos
  have hq : i / vs.size < r := by
    rw [Nat.div_lt_iff_lt_mul pos]; exact hi
  have := h (i / vs.size) hq (i % vs.size) hj
  simp only [Block.valueAt, array_getD vs _ hj]
  rw [← Int.natCast_div, this, Array.length_toList, Nat.add_assoc, Nat.div_add_mod' i vs.size]

end Airbender.Import.Setup.Proofs

/-- Closes `lhs = rhs` where both sides apply the same operations to digits of the row
    index: `omega` on the digits, congruence through the operations both sides share
    (`omega` treats xor/and/or/shift terms as atoms). -/
syntax "digits_eq" : tactic
macro_rules
  | `(tactic| digits_eq) => `(tactic| first
      | omega
      | (refine congrArg₂ (· ^^^ ·) ?_ ?_ <;> digits_eq)
      | (refine congrArg₂ (· &&& ·) ?_ ?_ <;> digits_eq)
      | (refine congrArg₂ (· ||| ·) ?_ ?_ <;> digits_eq)
      | (refine congrArg₂ (· <<< ·) ?_ ?_ <;> digits_eq)
      | (refine congrArg₂ (· % ·) ?_ ?_ <;> digits_eq)
      | (refine congrArg₂ (· * ·) ?_ ?_ <;> digits_eq)
      | (refine congrArg₂ (· / ·) ?_ ?_ <;> digits_eq)
      | (refine congrArg₂ (· ^ ·) ?_ ?_ <;> digits_eq))
