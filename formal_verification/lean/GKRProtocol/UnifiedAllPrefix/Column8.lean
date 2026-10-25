import GKRProtocol.UnifiedSpecialNative.Column8.Chunk0
import GKRProtocol.UnifiedSpecialLengths.Column8.Chunk0
import GKRProtocol.BlockCoverageImport
import GKRProtocol.ChunkSpans

namespace Airbender.Compiler.UnifiedAllPrefix.Column8
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

column_blocks_part suffix from Data.GKRSetup.Unified.setupColumn8 start 1 stop 4

noncomputable def originals : List (List Setup.Block) := [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.original]

noncomputable def targets : List (List Setup.Block) := [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.target]

column_parts_cover sourceCoverage from Data.GKRSetup.Unified.setupColumn8 parts [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.original, suffix]

theorem sourceShape : Data.GKRSetup.Unified.setupColumn8.blocks.toList = originals.flatten ++ suffix := by
  apply sourceCoverage.trans
  simp only [originals, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem chunksChecked : List.Forall₂ blockChunkAgreement originals targets :=
  List.Forall₂.cons Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.chunkAgreement (List.Forall₂.nil)

column_parts_cover regionShape0 from (UnifiedReduced.Setup.nativeZeroData.columns[(8 : Nat)]) parts [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_0]

theorem region0PartLength0 : (Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_0.map Setup.Block.length).sum = 1 := by decide +kernel

theorem regionLength0 : ((UnifiedReduced.Setup.nativeZeroData.columns[(8 : Nat)]).blocks.toList.map Setup.Block.length).sum = 1 := by
  rw [regionShape0]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region0PartLength0]
  rfl

column_parts_cover regionShape1 from (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(8 : Nat)]) parts [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_1]

theorem region1PartLength0 : (Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_1.map Setup.Block.length).sum = 131072 := by decide +kernel

theorem regionLength1 : ((UnifiedReduced.Setup.nativeRegisterZeroData.columns[(8 : Nat)]).blocks.toList.map Setup.Block.length).sum = 131072 := by
  rw [regionShape1]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region1PartLength0]
  rfl

column_parts_cover regionShape2 from (UnifiedReduced.Setup.nativeCleanupData.columns[(8 : Nat)]) parts [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_2]

theorem region2PartLength0 : (Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_2.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength2 : ((UnifiedReduced.Setup.nativeCleanupData.columns[(8 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape2]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region2PartLength0]
  rfl

column_parts_cover regionShape3 from (UnifiedReduced.Setup.nativeByteSignData.columns[(8 : Nat)]) parts [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_3]

theorem region3PartLength0 : (Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_3.map Setup.Block.length).sum = 256 := by decide +kernel

theorem regionLength3 : ((UnifiedReduced.Setup.nativeByteSignData.columns[(8 : Nat)]).blocks.toList.map Setup.Block.length).sum = 256 := by
  rw [regionShape3]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region3PartLength0]
  rfl

column_parts_cover regionShape4 from (UnifiedReduced.Setup.nativeSignData.columns[(8 : Nat)]) parts [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_4]

theorem region4PartLength0 : (Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_4.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength4 : ((UnifiedReduced.Setup.nativeSignData.columns[(8 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape4]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region4PartLength0]
  rfl

column_parts_cover regionShape5 from (UnifiedReduced.Setup.nativeTruncationData.columns[(8 : Nat)]) parts [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_5]

theorem region5PartLength0 : (Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_5.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength5 : ((UnifiedReduced.Setup.nativeTruncationData.columns[(8 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape5]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region5PartLength0]
  rfl

column_parts_cover regionShape6 from (UnifiedReduced.Setup.nativeShiftData.columns[(8 : Nat)]) parts [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_6]

theorem region6PartLength0 : (Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_6.map Setup.Block.length).sum = 262144 := by decide +kernel

theorem regionLength6 : ((UnifiedReduced.Setup.nativeShiftData.columns[(8 : Nat)]).blocks.toList.map Setup.Block.length).sum = 262144 := by
  rw [regionShape6]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region6PartLength0]
  rfl

column_parts_cover regionShape7 from (UnifiedReduced.Setup.nativeROMData.columns[(8 : Nat)]) parts [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_7]

theorem region7PartLength0 : (Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_7.map Setup.Block.length).sum = 1048576 := by decide +kernel

theorem regionLength7 : ((UnifiedReduced.Setup.nativeROMData.columns[(8 : Nat)]).blocks.toList.map Setup.Block.length).sum = 1048576 := by
  rw [regionShape7]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region7PartLength0]
  rfl

column_parts_cover regionShape8 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(8 : Nat)]) parts [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_8]

theorem region8PartLength0 : (Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_8.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength8 : ((UnifiedReduced.Setup.nativeRotate16Data.columns[(8 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape8]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region8PartLength0]
  rfl

column_parts_cover regionShape9 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(8 : Nat)]) parts [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_9]

theorem region9PartLength0 : (Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_9.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength9 : ((UnifiedReduced.Setup.nativeRotate12Data.columns[(8 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape9]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region9PartLength0]
  rfl

column_parts_cover regionShape10 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(8 : Nat)]) parts [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_10]

theorem region10PartLength0 : (Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_10.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength10 : ((UnifiedReduced.Setup.nativeRotate8Data.columns[(8 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape10]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region10PartLength0]
  rfl

column_parts_cover regionShape11 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(8 : Nat)]) parts [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_11]

theorem region11PartLength0 : (Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_11.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength11 : ((UnifiedReduced.Setup.nativeRotate7Data.columns[(8 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape11]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region11PartLength0]
  rfl

column_parts_cover regionShape12 from (UnifiedReduced.Setup.nativeConditionalData.columns[(8 : Nat)]) parts [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_12]

theorem region12PartLength0 : (Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_12.map Setup.Block.length).sum = 128 := by decide +kernel

theorem regionLength12 : ((UnifiedReduced.Setup.nativeConditionalData.columns[(8 : Nat)]).blocks.toList.map Setup.Block.length).sum = 128 := by
  rw [regionShape12]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region12PartLength0]
  rfl

column_parts_cover regionShape13 from (UnifiedReduced.Setup.nativeXorData.columns[(8 : Nat)]) parts [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_13]

theorem region13PartLength0 : (Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_13.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength13 : ((UnifiedReduced.Setup.nativeXorData.columns[(8 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape13]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region13PartLength0]
  rfl

column_parts_cover regionShape14 from (UnifiedReduced.Setup.nativeOrData.columns[(8 : Nat)]) parts [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_14]

theorem region14PartLength0 : (Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_14.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength14 : ((UnifiedReduced.Setup.nativeOrData.columns[(8 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape14]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region14PartLength0]
  rfl

column_parts_cover regionShape15 from (UnifiedReduced.Setup.nativeAndData.columns[(8 : Nat)]) parts [Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_15]

theorem region15PartLength0 : (Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.part0_15.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength15 : ((UnifiedReduced.Setup.nativeAndData.columns[(8 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape15]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region15PartLength0]
  rfl

noncomputable def regionBlocks : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(8 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(8 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeCleanupData.columns[(8 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeByteSignData.columns[(8 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeSignData.columns[(8 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeTruncationData.columns[(8 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeShiftData.columns[(8 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeROMData.columns[(8 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate16Data.columns[(8 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate12Data.columns[(8 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate8Data.columns[(8 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate7Data.columns[(8 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeConditionalData.columns[(8 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeXorData.columns[(8 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeOrData.columns[(8 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeAndData.columns[(8 : Nat)]).blocks.toList

noncomputable def extra : List Setup.Block := []

theorem targetShape : regionBlocks ++ extra = targets.flatten := by
  rw [regionBlocks, regionShape0, regionShape1, regionShape2, regionShape3, regionShape4, regionShape5, regionShape6, regionShape7, regionShape8, regionShape9, regionShape10, regionShape11, regionShape12, regionShape13, regionShape14, regionShape15]
  simp only [extra, targets, Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.target, Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.targets, Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.target0, List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]

theorem regionTotal : (regionBlocks.map Setup.Block.length).sum = 2097537 := by
  simp only [regionBlocks, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4, regionLength5, regionLength6, regionLength7, regionLength8, regionLength9, regionLength10, regionLength11, regionLength12, regionLength13, regionLength14, regionLength15]

theorem originalLength : (originals.flatten.map Setup.Block.length).sum = 2097537 := by
  simp only [originals, List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil]
  have len0 : (Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0.original.map Setup.Block.length).sum = 2097537 := Airbender.Compiler.UnifiedSpecialLengths.Column8.Chunk0.originalLength
  rw [len0]
  rfl

theorem prefix_value (index : Fin 2097537) : Data.GKRSetup.Unified.setupColumn8.get? index.val = Setup.getFromBlocks regionBlocks index.val := by
  change Setup.getFromBlocks Data.GKRSetup.Unified.setupColumn8.blocks.toList index.val = _
  rw [sourceShape, getFromBlocks_before_suffix _ _ index.val (by rw [originalLength]; have := index.isLt; omega), block_chunks_agree originals targets chunksChecked, ← targetShape]
  exact getFromBlocks_before_suffix regionBlocks extra index.val (by rw [regionTotal]; exact index.isLt)

end Airbender.Compiler.UnifiedAllPrefix.Column8
