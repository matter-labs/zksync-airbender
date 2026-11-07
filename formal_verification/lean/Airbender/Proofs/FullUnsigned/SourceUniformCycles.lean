import Airbender.Proofs.FullUnsigned.SourceBlockCycles
import Airbender.Proofs.Tables.PeriodicColumns

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

theorem uniform256_get (blocks : List Block)
    (shape : ∀ block ∈ blocks, block.length = 256) (index : Nat) :
    getFromBlocks blocks index =
      (blocks[index / 256]?).bind (fun block => block.get? (index % 256)) := by
  induction blocks generalizing index with
  | nil => rfl
  | cons block rest ih =>
    have head := shape block (by simp)
    have tail : ∀ b ∈ rest, b.length = 256 := fun b member => shape b (by simp [member])
    by_cases inside : index < 256
    · rw [getFromBlocks, head, if_pos inside]
      simp only [Nat.div_eq_of_lt inside, Nat.mod_eq_of_lt inside,
        List.getElem?_cons_zero, Option.bind_some]
    · have quotient : index / 256 = (index - 256) / 256 + 1 := by omega
      have residue : index % 256 = (index - 256) % 256 := by omega
      rw [getFromBlocks, head, if_neg inside, ih tail (index - 256), quotient,
        List.getElem?_cons_succ, residue]

theorem periodic_zero_get_mod (values : Array Nat) (count index : Nat)
    (positive : 0 < values.size) (cycles : 0 < count) (bound : index < count * values.size) :
    (Block.periodic count 0 values).get? index =
      (Block.periodic count 0 values).get? (index % values.size) := by
  have first : values.size ≤ count * values.size := by nlinarith
  have within := lt_of_lt_of_le (Nat.mod_lt index positive) first
  have a := periodic_get values count 0 index positive bound
  have b := periodic_get values count 0 (index % values.size) positive within
  simp only [Nat.zero_mul, Nat.add_zero, Nat.mod_mod, Int.natCast_zero] at a b
  exact a.trans b.symm

end Airbender.Setup.Proofs
