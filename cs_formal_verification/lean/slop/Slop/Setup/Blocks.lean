import Human.Import.SetupBlocks
import Mathlib.Tactic.Ring

/- Row meaning of compressed setup columns without expanding them. A Boolean scan (run by
   the kernel) checks short blocks row by row; long blocks (the import's grid blocks, long
   affine runs) are matched against a listed shape whose agreement with the row formula is
   proved algebraically. -/

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

/-- Blocks with their starting rows. -/
def placed : Nat → List Block → List (Nat × Block)
  | _, [] => []
  | s, b :: bs => (s, b) :: placed (s + b.len) bs

theorem matches_of_placed {spec : Nat → Int} {s : Nat} {bs : List Block}
    (h : ∀ p ∈ placed s bs, BlockOk spec p.1 p.2) : Matches spec s bs := by
  induction bs generalizing s with
  | nil => trivial
  | cons b bs ih =>
    refine ⟨h (s, b) (by simp [placed]), ih fun p hp => h p ?_⟩
    simp [placed, hp]

/-! Boolean row checks for short blocks. -/

/-- `values[j] + offset = spec (s + j)` for every `j`. -/
def checkVals (spec : Nat → Int) : Nat → Int → List Int → Bool
  | _, _, [] => true
  | s, off, v :: vs => (v + off == spec s) && checkVals spec (s + 1) off vs

/-- `value + step * j = spec (s + j)` for `j < n`. -/
def checkAffine (spec : Nat → Int) (step : Int) : Nat → Nat → Int → Bool
  | 0, _, _ => true
  | n + 1, s, v => (v == spec s) && checkAffine spec step n (s + 1) (v + step)

/-- `n` repetitions of `values`, the `q`-th shifted by `offset + stride * q`. -/
def checkPeriodic (spec : Nat → Int) (stride : Int) (vs : List Int) : Nat → Nat → Int → Bool
  | 0, _, _ => true
  | n + 1, s, off => checkVals spec s off vs && checkPeriodic spec stride vs n (s + vs.length) (off + stride)

/-- Row-by-row check of a short block; grid blocks are only matched by shape. -/
def checkBlock (spec : Nat → Int) (s : Nat) : Block → Bool
  | .affine n first step => checkAffine spec step n s first
  | .dense vs => checkVals spec s 0 vs.toList
  | .periodic r stride vs => checkPeriodic spec stride vs.toList r s 0
  | .grid _ _ => false

theorem checkVals_sound {spec : Nat → Int} {s : Nat} {off : Int} {vs : List Int}
    (h : checkVals spec s off vs = true) : ∀ j (hj : j < vs.length), vs[j] + off = spec (s + j) := by
  induction vs generalizing s with
  | nil => intro j hj; simp at hj
  | cons v vs ih =>
    simp only [checkVals, Bool.and_eq_true, beq_iff_eq] at h
    intro j hj
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := ih h.2 j (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

theorem checkAffine_sound {spec : Nat → Int} {step : Int} {n s : Nat} {v : Int}
    (h : checkAffine spec step n s v = true) : ∀ j < n, v + step * j = spec (s + j) := by
  induction n generalizing s v with
  | zero => intro j hj; omega
  | succ n ih =>
    simp only [checkAffine, Bool.and_eq_true, beq_iff_eq] at h
    intro j hj
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := ih h.2 j (by omega)
      rw [show s + (j + 1) = s + 1 + j by omega, ← this]
      push_cast
      ring

theorem checkPeriodic_sound {spec : Nat → Int} {stride : Int} {vs : List Int} {r s : Nat}
    {off : Int} (h : checkPeriodic spec stride vs r s off = true) :
    ∀ q < r, ∀ j (hj : j < vs.length), vs[j] + (off + stride * q) = spec (s + q * vs.length + j) := by
  induction r generalizing s off with
  | zero => intro q hq; omega
  | succ r ih =>
    simp only [checkPeriodic, Bool.and_eq_true] at h
    intro q hq j hj
    cases q with
    | zero => simpa using checkVals_sound h.1 j hj
    | succ q =>
      have := ih h.2 q (by omega) j hj
      rw [show s + (q + 1) * vs.length + j = s + vs.length + q * vs.length + j by ring, ← this]
      push_cast
      ring

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

theorem checkBlock_sound {spec : Nat → Int} {s : Nat} {b : Block}
    (h : checkBlock spec s b = true) : BlockOk spec s b := by
  cases b with
  | affine n first step =>
    intro i hi
    simpa [Block.valueAt] using checkAffine_sound h i hi
  | dense vs =>
    intro i hi
    simp only [Block.len] at hi
    have hj : i < vs.toList.length := by simpa using hi
    simpa [Block.valueAt, array_getD vs i hj] using checkVals_sound h i hj
  | periodic r stride vs =>
    apply periodic_ok
    intro q hq j hj
    simpa using checkPeriodic_sound h q hq j hj
  | grid n f => simp [checkBlock] at h

/-! Long blocks: a shape compared as data, plus an algebraic agreement proof. -/

inductive Shape where
  | affine (n : Nat) (first step : Int)
  | grid (n : Nat) (f : GridFn)
  deriving DecidableEq

/-- The block has this shape. -/
def Shape.check : Shape → Block → Bool
  | .affine n first step, .affine n' first' step' => n == n' && first == first' && step == step'
  | .grid n f, .grid n' f' => n == n' && f == f'
  | _, _ => false

/-- Algebraic agreement of a shape with `spec`, without reference to the data. -/
def Shape.Ok (spec : Nat → Int) (s : Nat) : Shape → Prop
  | .affine n first step => ∀ i < n, first + step * i = spec (s + i)
  | .grid n f => ∀ i < n, (f.eval i : Int) = spec (s + i)

theorem Shape.sound {spec : Nat → Int} {s : Nat} {sh : Shape} {b : Block}
    (hc : sh.check b = true) (ho : sh.Ok spec s) : BlockOk spec s b := by
  cases sh <;> cases b <;> simp only [Shape.check, Bool.and_eq_true, beq_iff_eq,
    Bool.false_eq_true] at hc
  · obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
    intro i hi
    exact ho i hi
  · obtain ⟨rfl, rfl⟩ := hc
    intro i hi
    exact ho i hi

theorem lookup_mem {k : Nat} {v : Shape} :
    ∀ {l : List (Nat × Shape)}, l.lookup k = some v → (k, v) ∈ l
  | [], h => by simp [List.lookup] at h
  | (a, b) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      simp only [beq_iff_eq] at hk
      cases h; subst hk; simp
    · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- A column agrees with `spec` on all its rows. -/
theorem decode_eq {spec : Nat → Int} {bs : List Block}
    (h : ∀ p ∈ placed 0 bs, BlockOk spec p.1 p.2) :
    ∀ n < total bs, decode bs n = spec n := by
  intro n hn
  simpa using decode_of_matches (matches_of_placed h) n hn

end Airbender.Import.Setup.Proofs

namespace Airbender.Import.Setup.Proofs

/-- Every block of the list (placed from row `s`): one listed in `longs` at its first row is
    matched by its shape, any other is checked row by row. -/
def scan (spec : Nat → Int) (longs : List (Nat × Shape)) : Nat → List Block → Bool
  | _, [] => true
  | s, b :: bs =>
    (match longs.lookup s with
     | some sh => sh.check b
     | none => checkBlock spec s b) && scan spec longs (s + b.len) bs

theorem scan_sound {spec : Nat → Int} {longs : List (Nat × Shape)}
    (ok : ∀ p ∈ longs, p.2.Ok spec p.1) {s : Nat} {bs : List Block}
    (h : scan spec longs s bs = true) : ∀ p ∈ placed s bs, BlockOk spec p.1 p.2 := by
  induction bs generalizing s with
  | nil => intro p hp; simp [placed] at hp
  | cons b bs ih =>
    intro p hp
    simp only [scan, Bool.and_eq_true] at h
    simp only [placed, List.mem_cons] at hp
    rcases hp with rfl | hp
    · have h1 := h.1
      split at h1
      · rename_i sh hsh
        exact Shape.sound h1 (ok (s, sh) (lookup_mem hsh))
      · exact checkBlock_sound h1
    · exact ih h.2 p hp

/-- A column of `N` rows agrees with `spec` on all its rows, by a scan. -/
theorem rows_of_scan {spec : Nat → Int} {longs : List (Nat × Shape)} {N : Nat} (bs : List Block)
    (ok : ∀ p ∈ longs, p.2.Ok spec p.1) (h : scan spec longs 0 bs = true) (ht : total bs = N) :
    ∀ n < N, decode bs n = spec n :=
  ht ▸ decode_eq (scan_sound ok h)

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
