import Airbender.Proofs.GKRProtocol.BlockTail

namespace Airbender.Compiler
set_option warningAsError true

def tinyAffineBlock (block : Setup.Block) : Setup.Block :=
  .affine block.length ((block.get? 0).getD 0) 0

def normalizeTinyBlock (block : Setup.Block) : Setup.Block :=
  if decide (block.length ≤ 4) &&
      finiteBlockSpanRangeCheck block (tinyAffineBlock block) 0 0 block.length then
    tinyAffineBlock block else block

theorem block_value_outside (block : Setup.Block) (index : Nat) (bound : block.length ≤ index) :
    block.get? index = none := by
  cases block <;> simp_all [Setup.Block.get?, Setup.Block.length]

theorem normalize_tiny_block_length (block : Setup.Block) :
    (normalizeTinyBlock block).length = block.length := by
  unfold normalizeTinyBlock
  split <;> rfl

theorem normalize_tiny_block_value (block : Setup.Block) (index : Nat) :
    (normalizeTinyBlock block).get? index = block.get? index := by
  unfold normalizeTinyBlock
  split
  · rename_i checked
    have clauses : decide (block.length ≤ 4) = true ∧
        finiteBlockSpanRangeCheck block (tinyAffineBlock block) 0 0 block.length = true := by
      simpa only [Bool.and_eq_true] using checked
    by_cases inside : index < block.length
    · have actual := finite_block_span_range_sound block (tinyAffineBlock block) 0 0 block.length
        clauses.2 index (Nat.zero_le _) (by omega)
      simpa only [Nat.zero_add] using actual.symm
    · rw [block_value_outside block index (by omega),
        block_value_outside (tinyAffineBlock block) index (by change block.length ≤ index; omega)]
  · rfl

theorem normalize_tiny_blocks_value (blocks : List Setup.Block) (index : Nat) :
    Setup.getFromBlocks (blocks.map normalizeTinyBlock) index = Setup.getFromBlocks blocks index := by
  induction blocks generalizing index with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.map_cons, Setup.getFromBlocks, normalize_tiny_block_length]
    split
    · exact normalize_tiny_block_value first index
    · exact ih _

def normalizeDecoderTail (blocks : List Setup.Block) : List Setup.Block :=
  normalizeSetupBlocks (blocks.map normalizeTinyBlock)

theorem normalize_decoder_tail_sound (blocks : List Setup.Block) (index : Nat) :
    Setup.getFromBlocks (normalizeDecoderTail blocks) index = Setup.getFromBlocks blocks index :=
  (normalizeSetupBlocks_sound (blocks.map normalizeTinyBlock) index).trans
    (normalize_tiny_blocks_value blocks index)

end Airbender.Compiler
