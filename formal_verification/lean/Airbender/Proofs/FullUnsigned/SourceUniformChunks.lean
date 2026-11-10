import Airbender.Proofs.FullUnsigned.SourceColumnRanges

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Equal positive block lengths give a direct source block coordinate. -/
theorem uniform_blocks_get (blocks : List Block) (length : Nat) (positive : 0 < length)
    (shape : ∀ block ∈ blocks, block.length = length) (n : Nat) :
    getFromBlocks blocks n =
      (blocks[n / length]?).bind (fun block => block.get? (n % length)) := by
  induction blocks generalizing n with
  | nil => rfl
  | cons block rest ih =>
    have head := shape block (by simp)
    have tail : ∀ b ∈ rest, b.length = length := fun b member => shape b (by simp [member])
    by_cases inside : n < length
    · rw [getFromBlocks, head, if_pos inside]
      simp only [Nat.div_eq_of_lt inside, Nat.mod_eq_of_lt inside,
        List.getElem?_cons_zero, Option.bind_some]
    · have quot : n / length = (n - length) / length + 1 := by
        have shifted : n = length + (n - length) := by omega
        conv_lhs => rw [shifted, Nat.add_div_left _ positive]
      have residue : n % length = (n - length) % length := Nat.mod_eq_sub_mod (by omega)
      rw [getFromBlocks, head, if_neg inside, ih tail (n - length), quot,
        List.getElem?_cons_succ, residue]

end Airbender.Setup.Proofs
