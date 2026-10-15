import Airbender.Import.SetupEmbed
import Mathlib.Data.Nat.Bitwise
namespace Airbender.Setup.Proofs

set_option warningAsError true

/-- A finite certificate over each imported block at its accumulated native index. -/
def checkBlocks (f : Nat → Nat) : Nat → List Block → Bool
  | _, [] => true
  | 0, b :: bs =>
      (List.finRange b.length).all (fun i => b.get? i.val == some (f i.val)) &&
      checkBlocks f b.length bs
  | s + 1, b :: bs =>
      (List.finRange b.length).all (fun i => b.get? i.val == some (f (s + 1 + i.val))) &&
      checkBlocks f (s + 1 + b.length) bs

private theorem checkBlocks_cons (f : Nat → Nat) (start : Nat) (b : Block) (bs : List Block) :
    checkBlocks f start (b :: bs) =
      ((List.finRange b.length).all (fun i => b.get? i.val == some (f (start + i.val))) &&
        checkBlocks f (start + b.length) bs) := by
  cases start with
  | zero => simp only [checkBlocks, Nat.zero_add]
  | succ s => rfl

theorem checkBlocks_cons_iff (f : Nat → Nat) (start : Nat) (b : Block) (bs : List Block) :
    checkBlocks f start (b :: bs) = true ↔
      (∀ i : Fin b.length, b.get? i.val = some (f (start + i.val))) ∧
        checkBlocks f (start + b.length) bs = true := by
  rw [checkBlocks_cons, Bool.and_eq_true]
  simp only [List.all_eq_true, List.mem_finRange, forall_true_left, beq_iff_eq]

theorem checkBlocks_nil (f : Nat → Nat) (start : Nat) : checkBlocks f start [] = true := rfl

theorem checkBlocks_sound (f : Nat → Nat) (blocks : List Block) (start n : Nat)
    (h : checkBlocks f start blocks = true)
    (hn : n < (blocks.map Block.length).sum) :
    getFromBlocks blocks n = some (f (start + n)) := by
  induction blocks generalizing start n with
  | nil => simp at hn
  | cons b bs ih =>
    simp only [checkBlocks_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, List.sum_cons] at hn
    simp only [getFromBlocks]
    split
    next bound =>
      have values := List.all_eq_true.mp h.1 ⟨n, bound⟩ (by simp)
      simpa only [beq_iff_eq] using values
    next bound =>
      have eqn := ih (start + b.length) (n - b.length) h.2 (by omega)
      rw [show start + b.length + (n - b.length) = start + n by omega] at eqn
      exact eqn

theorem checkBlocks_append_iff (f : Nat → Nat) (start : Nat) (left right : List Block) :
    checkBlocks f start (left ++ right) = true ↔
      checkBlocks f start left = true ∧
        checkBlocks f (start + (left.map Block.length).sum) right = true := by
  induction left generalizing start with
  | nil => simp [checkBlocks_nil]
  | cons b bs ih =>
    simp only [List.cons_append, checkBlocks_cons_iff, ih, List.map_cons, List.sum_cons]
    simp only [and_assoc, Nat.add_assoc]

/-- Raw append spelling used by the literal-data emitter. -/
theorem raw_toList_append {α : Type*} (left right : Array α) :
    (Array.append left right).toList = left.toList ++ right.toList := by
  exact Array.toList_append

theorem raw_size_append {α : Type*} (left right : Array α) :
    (Array.append left right).size = left.size + right.size := by
  exact Array.size_append

theorem raw_get_append {α : Type*} (left right : Array α) (i : Nat) :
    (Array.append left right)[i]? =
      if i < left.size then left[i]? else right[i - left.size]? := by
  exact Array.getElem?_append

end Airbender.Setup.Proofs
