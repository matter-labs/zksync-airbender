import GKRProtocol.BlockSpans

namespace Airbender.Compiler
open Airbender
set_option warningAsError true

def blockChunkAgreement (left right : List Setup.Block) : Prop :=
  (left.map Setup.Block.length).sum = (right.map Setup.Block.length).sum ∧
    ∀ index, Setup.getFromBlocks left index = Setup.getFromBlocks right index

theorem block_chunks_agree (left right : List (List Setup.Block))
    (checked : List.Forall₂ blockChunkAgreement left right) (index : Nat) :
    Setup.getFromBlocks left.flatten index = Setup.getFromBlocks right.flatten index := by
  induction checked generalizing index with
  | nil => rfl
  | @cons first second rest tail agreement remaining ih =>
    change (first.map Setup.Block.length).sum = (second.map Setup.Block.length).sum ∧ _ at agreement
    simp only [List.flatten_cons]
    rw [getFromBlocks_append first rest.flatten index, getFromBlocks_append second tail.flatten index,
      agreement.1]
    split
    · exact agreement.2 index
    · exact ih _

end Airbender.Compiler
