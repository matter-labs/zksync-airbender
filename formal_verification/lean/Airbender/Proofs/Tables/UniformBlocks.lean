import Airbender.Import.SetupEmbed

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

theorem uniform4096_get (blocks : List Block)
    (shape : ∀ block ∈ blocks, block.length = 4096) (n : Nat) :
    getFromBlocks blocks n =
      (blocks[n / 4096]?).bind (fun block => block.get? (n % 4096)) := by
  induction blocks generalizing n with
  | nil => rfl
  | cons block rest ih =>
    have head := shape block (by simp)
    have tail : ∀ b ∈ rest, b.length = 4096 := fun b member => shape b (by simp [member])
    by_cases inside : n < 4096
    · rw [getFromBlocks, head, if_pos inside]
      simp only [Nat.div_eq_of_lt inside, Nat.mod_eq_of_lt inside,
        List.getElem?_cons_zero, Option.bind_some]
    · have quot : n / 4096 = (n - 4096) / 4096 + 1 := by omega
      have residue : n % 4096 = (n - 4096) % 4096 := by omega
      rw [getFromBlocks, head, if_neg inside, ih tail (n - 4096), quot,
        List.getElem?_cons_succ, residue]

end Airbender.Setup.Proofs
