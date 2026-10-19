import Airbender.Proofs.Tables.ImportedBlocks

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

theorem checkBlocks_complete (f : Nat → Nat) (blocks : List Block) (start : Nat)
    (reads : ∀ n : Fin (blocks.map Block.length).sum,
      getFromBlocks blocks n.val = some (f (start + n.val))) :
    checkBlocks f start blocks = true := by
  induction blocks generalizing start with
  | nil => exact checkBlocks_nil _ _
  | cons b bs ih =>
    rw [checkBlocks_cons_iff]
    constructor
    · intro i
      have result := reads ⟨i.val,by simp only [List.map_cons,List.sum_cons]; omega⟩
      simpa only [getFromBlocks,if_pos i.isLt] using result
    · apply ih
      intro i
      have result := reads ⟨b.length + i.val,by simp only [List.map_cons,List.sum_cons]; omega⟩
      have outside : ¬ b.length + i.val < b.length := by omega
      simpa only [getFromBlocks,if_neg outside,Nat.add_sub_cancel_left,Nat.add_assoc] using result

theorem checkBlocks_transfer (f g : Nat → Nat) (blocks : List Block) (source target : Nat)
    (checked : checkBlocks f source blocks = true)
    (same : ∀ n : Fin (blocks.map Block.length).sum, g (target + n.val) = f (source + n.val)) :
    checkBlocks g target blocks = true := by
  apply checkBlocks_complete
  intro n
  rw [same n]
  exact checkBlocks_sound f blocks source n.val checked n.isLt

end Airbender.Setup.Proofs
