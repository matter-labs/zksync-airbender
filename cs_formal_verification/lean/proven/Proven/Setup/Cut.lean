module
public import Proven.Setup.Scan

@[expose] public section

/- Blocks cut into pieces that cover the same rows with the same values. A long block that crosses a region bound of
   the column formula is cut at the bound: each piece then lies in one region, and `long_ok` proves it with the
   formula of that region. The scan checks the pieces, and `decode_cutColumn` gives the rows of the imported
   blocks. -/

namespace Airbender.Import.Setup.Scan

open Airbender.Import.Setup Airbender.Import.Setup.Proofs

/-- The first `k` rows of a block and the rows after them, when `k` is strictly inside the block (on a period bound
    for a periodic block); otherwise `none`. -/
def cutBlock (k : Nat) : Block → Option (Block × Block)
  | .affine count first step =>
    if 0 < k ∧ k < count then some (.affine k first step, .affine (count - k) (first + step * k) step) else none
  | .periodic reps stride values =>
    if 0 < values.size ∧ k % values.size = 0 ∧ k / values.size < reps then
      some (.periodic (k / values.size) stride values,
        .periodic (reps - k / values.size) stride
          ⟨values.toList.map (· + stride * ((k / values.size : Nat) : Int))⟩)
    else none
  | .dense _ => none

/-- The block cut after each of `lengths` rows in turn: pieces of these lengths, then the rest. A length that does not
    cut the rest leaves the rest whole. -/
def cutMany : List Nat → Block → List Block
  | [], block => [block]
  | length :: lengths, block =>
    match cutBlock length block with
    | some (front, rest) => front :: cutMany lengths rest
    | none => [block]

/-- For each entry `(skip, lengths)` in turn: the next `skip` blocks stay whole, and the block after them is cut after
    `lengths` (`cutMany`). The blocks after the last entry stay whole. -/
def cutColumn : List (Nat × List Nat) → List Block → List Block
  | [], blocks => blocks
  | (skip, lengths) :: cuts, blocks =>
    blocks.take skip ++ match blocks.drop skip with
      | [] => []
      | block :: rest => cutMany lengths block ++ cutColumn cuts rest

/-- `pieces` cover the rows of `block` with its values, before any blocks. -/
def SameRows (pieces : List Block) (block : Block) : Prop :=
  total pieces = block.len ∧ ∀ rest n, decode (pieces ++ rest) n = decode (block :: rest) n

theorem sameRows_self (block : Block) : SameRows [block] block :=
  ⟨by simp [total], fun _ _ => rfl⟩

/-- A front piece, then pieces that cover the rest of the block. -/
theorem sameRows_cons {front rest block : Block} {pieces : List Block}
    (cut : SameRows [front, rest] block) (tail : SameRows pieces rest) : SameRows (front :: pieces) block := by
  obtain ⟨cutTotal, cutRows⟩ := cut
  obtain ⟨tailTotal, tailRows⟩ := tail
  refine ⟨by simp only [total] at cutTotal ⊢; omega, fun others n => ?_⟩
  rw [← cutRows others n]
  simp only [List.cons_append, decode, List.nil_append]
  split
  · rfl
  · exact tailRows others _

theorem cutBlock_sameRows {k : Nat} {block front rest : Block} (h : cutBlock k block = some (front, rest)) :
    SameRows [front, rest] block := by
  cases block with
  | affine count first step =>
    simp only [cutBlock] at h
    split at h
    · rename_i inside
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp only [total, Block.len]; omega, fun others n => ?_⟩
      simp only [List.cons_append, List.nil_append, decode, Block.len, Block.valueAt]
      by_cases low : n < k
      · simp [low, show n < count by omega]
      · simp only [low, ↓reduceIte]
        by_cases high : n - k < count - k
        · simp only [high, ↓reduceIte, show n < count by omega]
          rw [Int.natCast_sub (by omega)]
          ring
        · simp only [high, ↓reduceIte, show ¬n < count by omega]
          congr 1
          omega
    · simp at h
  | dense values => simp [cutBlock] at h
  | periodic reps stride values =>
    simp only [cutBlock] at h
    split at h
    · rename_i inside
      obtain ⟨positive, aligned, room⟩ := inside
      obtain ⟨p, rfl⟩ : ∃ p, k = p * values.size :=
        ⟨k / values.size, by have := Nat.div_add_mod k values.size; rw [aligned] at this; rw [Nat.mul_comm]; omega⟩
      simp only [Nat.mul_div_cancel p positive] at h room
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have shiftedSize : (⟨values.toList.map (· + stride * (p : Int))⟩ : Array Int).size = values.size := by simp
      have whole : p * values.size + (reps - p) * values.size = reps * values.size := by
        rw [← Nat.add_mul]; congr 1; omega
      refine ⟨by simp only [total, Block.len, shiftedSize, Nat.add_zero]; exact whole, fun others n => ?_⟩
      simp only [List.cons_append, List.nil_append, decode, Block.len, shiftedSize]
      by_cases low : n < p * values.size
      · simp only [low, ↓reduceIte, show n < reps * values.size by omega]
        rfl
      · simp only [low, ↓reduceIte]
        obtain ⟨m, rfl⟩ : ∃ m, n = p * values.size + m := ⟨n - p * values.size, by omega⟩
        rw [Nat.add_sub_cancel_left]
        by_cases high : m < (reps - p) * values.size
        · simp only [high, ↓reduceIte, show p * values.size + m < reps * values.size by omega, Block.valueAt,
            shiftedSize]
          have get : (⟨values.toList.map (· + stride * (p : Int))⟩ : Array Int).getD (m % values.size) 0 =
              values.getD (m % values.size) 0 + stride * p := by
            simp [Array.getD, Nat.mod_lt m positive]
          rw [get, ← Int.natCast_div, ← Int.natCast_div, Nat.add_comm (p * values.size) m,
            Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ positive]
          push_cast
          ring
        · simp only [high, ↓reduceIte, show ¬p * values.size + m < reps * values.size by omega]
          congr 1
          rw [← whole]
          omega
    · simp at h

theorem cutMany_sameRows (lengths : List Nat) (block : Block) : SameRows (cutMany lengths block) block := by
  induction lengths generalizing block with
  | nil => exact sameRows_self block
  | cons length lengths ih =>
    simp only [cutMany]
    split
    · rename_i front rest cut
      exact sameRows_cons (cutBlock_sameRows cut) (ih rest)
    · exact sameRows_self block

/-- The cut blocks decode to the same rows as the blocks. -/
theorem decode_cutColumn (cuts : List (Nat × List Nat)) (blocks : List Block) (n : Nat) :
    decode (cutColumn cuts blocks) n = decode blocks n := by
  induction cuts generalizing blocks n with
  | nil => rfl
  | cons entry cuts ih =>
    obtain ⟨skip, lengths⟩ := entry
    simp only [cutColumn]
    conv => rhs; rw [← List.take_append_drop skip blocks]
    rw [decode_append, decode_append]
    split
    · rfl
    · split
      · rename_i empty
        rw [empty]
      · rename_i block rest after
        rw [after, (cutMany_sameRows lengths block).2]
        simp only [decode]
        split
        · rfl
        · exact ih rest _

end Airbender.Import.Setup.Scan
