import Airbender.Proofs.GKRProtocol.UnifiedPackedEquality.Column6.Bindings

namespace Airbender.Compiler.UnifiedPackedEquality.Column6
open Airbender Airbender.Compiler.PackedSetupEquality
set_option warningAsError true
-- The single kernel result compares all 24,064 records and their 188 row counts.
set_option maxRecDepth 131072

theorem ok : PackedSetupEquality.checkTreeWithChunks sourceTree targetTree lengthChecks = true := by
  decide +kernel

theorem tree_ok : PackedSetupEquality.checkTree sourceTree targetTree lengthChecks = true :=
  PackedSetupEquality.checkTreeWithChunks_base _ _ _ ok

theorem checked_facts :
    sourceCode.map BlockCode.decode = targetCode.map BlockCode.decode ∧
    ∀ item ∈ lengthChecks,
      ((((sourceCode.map BlockCode.decode).drop item.first).take item.count).map Setup.Block.length).sum = item.expected := by
  have facts := PackedSetupEquality.checkTree_sound _ _ _ tree_ok
  rw [source_tree_binding, target_tree_binding] at facts
  exact facts

def sourceBlocks : List Setup.Block := sourceCode.map BlockCode.decode
def targetBlocks : List Setup.Block := targetCode.map BlockCode.decode

theorem blocks_eq : sourceBlocks = targetBlocks :=
  checked_facts.1

theorem slice_eq (first count : Nat) :
    (sourceBlocks.drop first).take count = (targetBlocks.drop first).take count :=
  congrArg (fun values : List Setup.Block => (values.drop first).take count) blocks_eq

theorem length_at (index : Fin lengthChecks.length) :
    (((sourceBlocks.drop lengthChecks[index].first).take lengthChecks[index].count).map Setup.Block.length).sum =
      lengthChecks[index].expected :=
  checked_facts.2 _ (List.getElem_mem index.isLt)

def sourceChunk (first : Nat) : List Setup.Block :=
  (sourceTree.chunk first).map BlockCode.decode
def targetChunk (first : Nat) : List Setup.Block :=
  (targetTree.chunk first).map BlockCode.decode

theorem chunk_eq (first : Nat) : sourceChunk first = targetChunk first :=
  congrArg (fun tree : CodeTree => (tree.chunk first).map BlockCode.decode)
    (PackedSetupEquality.checkTree_codes_eq _ _ _ tree_ok)

theorem tree_rows_at (index : Fin lengthChecks.length) :
    sourceTree.rowCount lengthChecks[index.val].first lengthChecks[index.val].count = lengthChecks[index.val].expected :=
  PackedSetupEquality.checkTree_rows _ _ _ tree_ok index

theorem chunk_length_at (index : Fin lengthChecks.length) :
    ((sourceChunk lengthChecks[index.val].first).map Setup.Block.length).sum = lengthChecks[index.val].expected :=
  PackedSetupEquality.checkTreeWithChunks_chunk_length _ _ _ ok index

theorem fixed_column_blocks : (Data.GKRSetup.Unified.setupColumn6.blocks.toList.drop 128).take 24064 = ((UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]).blocks.toList.drop 128).take 24064 := by
  rw [source_binding, target_binding]
  exact blocks_eq

theorem row_counts (item : LengthCheck) (member : item ∈ lengthChecks) :
    (((((Data.GKRSetup.Unified.setupColumn6.blocks.toList.drop 128).take 24064).drop item.first).take item.count).map Setup.Block.length).sum = item.expected := by
  rw [source_binding]
  exact checked_facts.2 item member

end Airbender.Compiler.UnifiedPackedEquality.Column6
