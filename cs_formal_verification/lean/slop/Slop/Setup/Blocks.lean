import Human.Import.SetupBlocks
import Mathlib.Tactic.Ring

/- Row meaning of compressed setup columns without expanding them.
   Short blocks are checked row by row by a Boolean walk (run by the kernel in
   separate modules); long blocks are matched against an affine or periodic shape
   whose agreement with the row formula is proved algebraically. -/

namespace Airbender.Import.Setup.Proofs

open Airbender.Import.Setup

/-- Total number of rows covered by a block list. -/
def total : List Block → Nat
  | [] => 0
  | b :: bs => b.len + total bs

theorem decode_append (xs ys : List Block) (n : Nat) :
    decode (xs ++ ys) n = if n < total xs then decode xs n else decode ys (n - total xs) := by
  induction xs generalizing n with
  | nil => simp [total]
  | cons b bs ih =>
    simp only [List.cons_append, decode, total]
    by_cases h : n < b.len
    · simp [h, show n < b.len + total bs by omega]
    · simp only [h, ite_false]; rw [ih]
      by_cases h' : n - b.len < total bs
      · simp [h', show n < b.len + total bs by omega]
      · simp [h', show ¬ n < b.len + total bs by omega, Nat.sub_sub]

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

def checkBlock (spec : Nat → Int) (s : Nat) : Block → Bool
  | .affine n first step => checkAffine spec step n s first
  | .dense vs => checkVals spec s 0 vs.toList
  | .periodic r stride vs => checkPeriodic spec stride vs.toList r s 0

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

/-! Long blocks: a shape checked syntactically, plus an algebraic agreement proof. -/

inductive Shape where
  | affine (n : Nat) (first step : Int)
  | periodic (r : Nat) (stride : Int) (size : Nat)
  deriving DecidableEq

/-- The block has this shape; for a periodic block, its first period matches `spec`. -/
def Shape.check (spec : Nat → Int) (s : Nat) : Shape → Block → Bool
  | .affine n first step, .affine n' first' step' => n == n' && first == first' && step == step'
  | .periodic r stride size, .periodic r' stride' vs =>
      r == r' && stride == stride' && vs.size == size && checkVals spec s 0 vs.toList
  | _, _ => false

/-- Algebraic agreement of a shape with `spec`, without reference to the data. -/
def Shape.Ok (spec : Nat → Int) (s : Nat) : Shape → Prop
  | .affine n first step => ∀ i < n, first + step * i = spec (s + i)
  | .periodic r stride size =>
      ∀ q < r, ∀ j < size, spec (s + q * size + j) = spec (s + j) + stride * q

theorem Shape.sound {spec : Nat → Int} {s : Nat} {sh : Shape} {b : Block}
    (hc : sh.check spec s b = true) (ho : sh.Ok spec s) : BlockOk spec s b := by
  cases sh <;> cases b <;> simp only [Shape.check, Bool.and_eq_true, beq_iff_eq,
    Bool.false_eq_true] at hc
  · obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
    intro i hi
    exact ho i hi
  · obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hv⟩ := hc
    apply periodic_ok
    intro q hq j hj
    have first := checkVals_sound hv j hj
    simp only [add_zero, Array.length_toList] at first ⊢
    rw [ho q hq j (by simpa using hj), ← first]

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

/-- Rows `[lo, hi)`: short blocks starting there are checked row by row; a long
    block starting there must be listed in `longs` with a matching shape. -/
def walk (spec : Nat → Int) (lo hi : Nat) (longs : List (Nat × Shape)) : Nat → List Block → Bool
  | _, [] => true
  | s, b :: bs =>
    (if lo ≤ s && s < hi then
      (if b.len ≤ 512 then checkBlock spec s b
       else match longs.lookup s with
         | some sh => sh.check spec s b
         | none => false)
     else true) && walk spec lo hi longs (s + b.len) bs

theorem walk_sound {spec : Nat → Int} {lo hi : Nat} {longs : List (Nat × Shape)}
    (ok : ∀ p ∈ longs, p.2.Ok spec p.1) {s : Nat} {bs : List Block}
    (h : walk spec lo hi longs s bs = true) :
    ∀ p ∈ placed s bs, lo ≤ p.1 → p.1 < hi → BlockOk spec p.1 p.2 := by
  induction bs generalizing s with
  | nil => intro p hp; simp [placed] at hp
  | cons b bs ih =>
    simp only [walk, Bool.and_eq_true] at h
    intro p hp hlo hhi
    simp only [placed, List.mem_cons] at hp
    rcases hp with rfl | hp
    · have h1 := h.1
      split at h1
      swap
      · rename_i hn; simp [hlo, hhi] at hn
      split at h1
      · exact checkBlock_sound h1
      · split at h1
        · rename_i sh hsh
          exact Shape.sound h1 (ok (s, sh) (lookup_mem hsh))
        · simp at h1
    · exact ih h.2 p hp hlo hhi

/-- A column agrees with `spec` on all its rows. -/
theorem decode_eq {spec : Nat → Int} {bs : List Block}
    (h : ∀ p ∈ placed 0 bs, BlockOk spec p.1 p.2) :
    ∀ n < total bs, decode bs n = spec n := by
  intro n hn
  simpa using decode_of_matches (matches_of_placed h) n hn

end Airbender.Import.Setup.Proofs

namespace Airbender.Import.Setup.Proofs

theorem placed_le {s : Nat} {bs : List Block} :
    ∀ p ∈ placed s bs, p.1 ≤ s + total bs := by
  induction bs generalizing s with
  | nil => intro p hp; simp [placed] at hp
  | cons b bs ih =>
    intro p hp
    simp only [placed, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp
    · have := ih p hp; simp only [total]; omega

end Airbender.Import.Setup.Proofs

namespace Airbender.Import.Setup.Proofs

theorem placed_ge {s : Nat} {bs : List Block} : ∀ p ∈ placed s bs, s ≤ p.1 := by
  induction bs generalizing s with
  | nil => intro p hp; simp [placed] at hp
  | cons b bs ih =>
    intro p hp
    simp only [placed, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact le_refl _
    · have := ih p hp; omega

/-- A walk with a chosen size limit that stops at row `hi`: a block whose start is
    listed in `longs` is matched by its shape, any other block of at most `limit` rows
    is checked row by row. -/
def walkUpTo (limit : Nat) (spec : Nat → Int) (lo hi : Nat) (longs : List (Nat × Shape)) :
    Nat → List Block → Bool
  | _, [] => true
  | s, b :: bs =>
    if hi ≤ s then true
    else
      (if lo ≤ s then
        (match longs.lookup s with
         | some sh => sh.check spec s b
         | none => decide (b.len ≤ limit) && checkBlock spec s b)
       else true) && walkUpTo limit spec lo hi longs (s + b.len) bs

theorem walkUpTo_sound {limit : Nat} {spec : Nat → Int} {lo hi : Nat}
    {longs : List (Nat × Shape)} (ok : ∀ p ∈ longs, p.2.Ok spec p.1) {s : Nat} {bs : List Block}
    (h : walkUpTo limit spec lo hi longs s bs = true) :
    ∀ p ∈ placed s bs, lo ≤ p.1 → p.1 < hi → BlockOk spec p.1 p.2 := by
  induction bs generalizing s with
  | nil => intro p hp; simp [placed] at hp
  | cons b bs ih =>
    intro p hp hlo hhi
    have ge := placed_ge p hp
    simp only [walkUpTo] at h
    split at h
    · exfalso; omega
    simp only [Bool.and_eq_true] at h
    simp only [placed, List.mem_cons] at hp
    rcases hp with rfl | hp
    · have h1 := h.1
      split at h1
      swap
      · rename_i hn; exact absurd hlo hn
      split at h1
      · rename_i sh hsh
        exact Shape.sound h1 (ok (s, sh) (lookup_mem hsh))
      · simp only [Bool.and_eq_true] at h1
        exact checkBlock_sound h1.2
    · exact ih h.2 p hp hlo hhi

end Airbender.Import.Setup.Proofs
