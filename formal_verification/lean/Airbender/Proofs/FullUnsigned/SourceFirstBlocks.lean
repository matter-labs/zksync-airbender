import Airbender.Proofs.FullUnsigned.SourceColumnRanges

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

/-- A row inside the first stored block does not inspect later source data. -/
theorem getFromBlocks_first (blocks : List Block) (block : Block) (index : Nat)
    (first : blocks.head? = some block) (bound : index < block.length) :
    getFromBlocks blocks index = block.get? index := by
  cases blocks with
  | nil => simp at first
  | cons head rest =>
    have same : head = block := Option.some.inj first
    subst head
    rw [getFromBlocks, if_pos bound]

end Airbender.Setup.Proofs
