import Airbender.Import.SetupEmbed

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

theorem skip_blocks (front back : List Block) (n : Nat) :
    getFromBlocks (front ++ back) ((front.map Block.length).sum + n) =
      getFromBlocks back n := by
  induction front with
  | nil => simp only [List.nil_append, List.map_nil, List.sum_nil, Nat.zero_add]
  | cons block rest ih =>
    simp only [List.cons_append, List.map_cons, List.sum_cons]
    have outside : ¬ block.length + (rest.map Block.length).sum + n < block.length := by omega
    rw [getFromBlocks, if_neg outside]
    have offset : block.length + (rest.map Block.length).sum + n - block.length =
        (rest.map Block.length).sum + n := by omega
    rw [offset, ih]

theorem selected_block (front back : List Block) (block : Block) (n : Nat)
    (bound : n < block.length) :
    getFromBlocks (front ++ block :: back) ((front.map Block.length).sum + n) =
      block.get? n := by
  rw [skip_blocks, getFromBlocks, if_pos bound]

theorem selected_at (front back : List Block) (block : Block) (base n : Nat)
    (offset : (front.map Block.length).sum = base) (lower : base ≤ n)
    (bound : n - base < block.length) :
    getFromBlocks (front ++ block :: back) n = block.get? (n - base) := by
  have index : n = (front.map Block.length).sum + (n - base) := by rw [offset]; omega
  exact (congrArg (getFromBlocks (front ++ block :: back)) index).trans
    (selected_block front back block (n - base) bound)

end Airbender.Setup.Proofs
