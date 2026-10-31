import Airbender.Proofs.FullUnsigned.SetupSourceRLE

namespace Airbender.Setup.SourceDecoding
set_option warningAsError true
set_option Elab.async false

/-- Equal source-node indices give equal decoded blocks. This uses the
proved decoder facts and does not normalize the stored block payloads. -/
theorem blocks_equal_of_nodes (strings : Nat → String) (tokens : Nat → SourceData.NumberToken)
    (bank : SourceBank.Bank) (fuel : Nat) (leftNodes rightNodes : Nat → Nat)
    (leftBlocks rightBlocks : Nat → Block) (left right : List Nat)
    (leftValid : ∀ index, BlockAt strings tokens bank fuel (leftNodes index) (leftBlocks index))
    (rightValid : ∀ index, BlockAt strings tokens bank fuel (rightNodes index) (rightBlocks index))
    (sameNodes : left.map leftNodes = right.map rightNodes) :
    left.map leftBlocks = right.map rightBlocks := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons head rest => cases sameNodes
  | cons head rest ih =>
    cases right with
    | nil => cases sameNodes
    | cons other tail =>
      simp only [List.map_cons] at sameNodes ⊢
      obtain ⟨sameHead, sameTail⟩ := List.cons.inj sameNodes
      have a := (leftValid head).decode
      have b := (rightValid other).decode
      rw [sameHead] at a
      have sameBlock : leftBlocks head = rightBlocks other := Except.ok.inj (a.symm.trans b)
      rw [sameBlock, ih tail sameTail]

end Airbender.Setup.SourceDecoding
