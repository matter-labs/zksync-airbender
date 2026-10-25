import GKRProtocol.UnifiedEqualParts.Column0.Part0
import GKRProtocol.BlockCoverageImport
import GKRProtocol.ChunkSpans

namespace Airbender.Compiler.UnifiedAllPrefix.Column0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

theorem chunkAgreement0 : blockChunkAgreement Airbender.Compiler.UnifiedEqualChunks.Column0.original0 Airbender.Compiler.UnifiedEqualChunks.Column0.target0 := by
  have same := Airbender.Compiler.UnifiedEqualChunks.Column0.chunkSame0
  constructor
  · exact congrArg (fun blocks : List Setup.Block => (blocks.map Setup.Block.length).sum) same
  · intro index
    rw [same]

column_blocks_part suffix from Data.GKRSetup.Unified.setupColumn0 start 19 stop 22

noncomputable def originals : List (List Setup.Block) := [Airbender.Compiler.UnifiedEqualChunks.Column0.original0]

noncomputable def targets : List (List Setup.Block) := [Airbender.Compiler.UnifiedEqualChunks.Column0.target0]

column_parts_cover sourceCoverage from Data.GKRSetup.Unified.setupColumn0 parts [Airbender.Compiler.UnifiedEqualChunks.Column0.original0, suffix]

theorem sourceShape : Data.GKRSetup.Unified.setupColumn0.blocks.toList = originals.flatten ++ suffix := by
  apply sourceCoverage.trans
  simp only [originals, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem chunksChecked : List.Forall₂ blockChunkAgreement originals targets :=
  List.Forall₂.cons chunkAgreement0 (List.Forall₂.nil)

column_parts_cover regionShape0 from (UnifiedReduced.Setup.nativeZeroData.columns[(0 : Nat)]) parts [Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region0]

theorem region0PartLength0 : (Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region0.map Setup.Block.length).sum = 1 := by decide +kernel

theorem regionLength0 : ((UnifiedReduced.Setup.nativeZeroData.columns[(0 : Nat)]).blocks.toList.map Setup.Block.length).sum = 1 := by
  rw [regionShape0]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region0PartLength0]
  rfl

column_parts_cover regionShape1 from (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(0 : Nat)]) parts [Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region1]

theorem region1PartLength0 : (Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region1.map Setup.Block.length).sum = 131072 := by decide +kernel

theorem regionLength1 : ((UnifiedReduced.Setup.nativeRegisterZeroData.columns[(0 : Nat)]).blocks.toList.map Setup.Block.length).sum = 131072 := by
  rw [regionShape1]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region1PartLength0]
  rfl

column_parts_cover regionShape2 from (UnifiedReduced.Setup.nativeCleanupData.columns[(0 : Nat)]) parts [Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region2]

theorem region2PartLength0 : (Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region2.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength2 : ((UnifiedReduced.Setup.nativeCleanupData.columns[(0 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape2]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region2PartLength0]
  rfl

column_parts_cover regionShape3 from (UnifiedReduced.Setup.nativeByteSignData.columns[(0 : Nat)]) parts [Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region3]

theorem region3PartLength0 : (Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region3.map Setup.Block.length).sum = 256 := by decide +kernel

theorem regionLength3 : ((UnifiedReduced.Setup.nativeByteSignData.columns[(0 : Nat)]).blocks.toList.map Setup.Block.length).sum = 256 := by
  rw [regionShape3]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region3PartLength0]
  rfl

column_parts_cover regionShape4 from (UnifiedReduced.Setup.nativeSignData.columns[(0 : Nat)]) parts [Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region4]

theorem region4PartLength0 : (Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region4.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength4 : ((UnifiedReduced.Setup.nativeSignData.columns[(0 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape4]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region4PartLength0]
  rfl

column_parts_cover regionShape5 from (UnifiedReduced.Setup.nativeTruncationData.columns[(0 : Nat)]) parts [Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region5]

theorem region5PartLength0 : (Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region5.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength5 : ((UnifiedReduced.Setup.nativeTruncationData.columns[(0 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape5]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region5PartLength0]
  rfl

column_parts_cover regionShape6 from (UnifiedReduced.Setup.nativeShiftData.columns[(0 : Nat)]) parts [Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region6]

theorem region6PartLength0 : (Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region6.map Setup.Block.length).sum = 262144 := by decide +kernel

theorem regionLength6 : ((UnifiedReduced.Setup.nativeShiftData.columns[(0 : Nat)]).blocks.toList.map Setup.Block.length).sum = 262144 := by
  rw [regionShape6]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region6PartLength0]
  rfl

column_parts_cover regionShape7 from (UnifiedReduced.Setup.nativeROMData.columns[(0 : Nat)]) parts [Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region7]

theorem region7PartLength0 : (Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region7.map Setup.Block.length).sum = 1048576 := by decide +kernel

theorem regionLength7 : ((UnifiedReduced.Setup.nativeROMData.columns[(0 : Nat)]).blocks.toList.map Setup.Block.length).sum = 1048576 := by
  rw [regionShape7]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region7PartLength0]
  rfl

column_parts_cover regionShape8 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(0 : Nat)]) parts [Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region8]

theorem region8PartLength0 : (Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region8.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength8 : ((UnifiedReduced.Setup.nativeRotate16Data.columns[(0 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape8]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region8PartLength0]
  rfl

column_parts_cover regionShape9 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(0 : Nat)]) parts [Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region9]

theorem region9PartLength0 : (Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region9.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength9 : ((UnifiedReduced.Setup.nativeRotate12Data.columns[(0 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape9]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region9PartLength0]
  rfl

column_parts_cover regionShape10 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(0 : Nat)]) parts [Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region10]

theorem region10PartLength0 : (Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region10.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength10 : ((UnifiedReduced.Setup.nativeRotate8Data.columns[(0 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape10]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region10PartLength0]
  rfl

column_parts_cover regionShape11 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(0 : Nat)]) parts [Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region11]

theorem region11PartLength0 : (Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region11.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength11 : ((UnifiedReduced.Setup.nativeRotate7Data.columns[(0 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape11]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region11PartLength0]
  rfl

column_parts_cover regionShape12 from (UnifiedReduced.Setup.nativeConditionalData.columns[(0 : Nat)]) parts [Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region12]

theorem region12PartLength0 : (Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region12.map Setup.Block.length).sum = 128 := by decide +kernel

theorem regionLength12 : ((UnifiedReduced.Setup.nativeConditionalData.columns[(0 : Nat)]).blocks.toList.map Setup.Block.length).sum = 128 := by
  rw [regionShape12]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region12PartLength0]
  rfl

column_parts_cover regionShape13 from (UnifiedReduced.Setup.nativeXorData.columns[(0 : Nat)]) parts [Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region13]

theorem region13PartLength0 : (Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region13.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength13 : ((UnifiedReduced.Setup.nativeXorData.columns[(0 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape13]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region13PartLength0]
  rfl

column_parts_cover regionShape14 from (UnifiedReduced.Setup.nativeOrData.columns[(0 : Nat)]) parts [Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region14]

theorem region14PartLength0 : (Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region14.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength14 : ((UnifiedReduced.Setup.nativeOrData.columns[(0 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape14]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region14PartLength0]
  rfl

column_parts_cover regionShape15 from (UnifiedReduced.Setup.nativeAndData.columns[(0 : Nat)]) parts [Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region15]

theorem region15PartLength0 : (Airbender.Compiler.UnifiedEqualChunks.Column0.target0Region15.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength15 : ((UnifiedReduced.Setup.nativeAndData.columns[(0 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape15]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region15PartLength0]
  rfl

noncomputable def regionBlocks : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(0 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(0 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeCleanupData.columns[(0 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeByteSignData.columns[(0 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeSignData.columns[(0 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeTruncationData.columns[(0 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeShiftData.columns[(0 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeROMData.columns[(0 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate16Data.columns[(0 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate12Data.columns[(0 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate8Data.columns[(0 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate7Data.columns[(0 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeConditionalData.columns[(0 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeXorData.columns[(0 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeOrData.columns[(0 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeAndData.columns[(0 : Nat)]).blocks.toList

noncomputable def extra : List Setup.Block := []

theorem targetShape : regionBlocks ++ extra = targets.flatten := by
  rw [regionBlocks, regionShape0, regionShape1, regionShape2, regionShape3, regionShape4, regionShape5, regionShape6, regionShape7, regionShape8, regionShape9, regionShape10, regionShape11, regionShape12, regionShape13, regionShape14, regionShape15]
  simp only [extra, targets, Airbender.Compiler.UnifiedEqualChunks.Column0.target0, List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]

theorem regionTotal : (regionBlocks.map Setup.Block.length).sum = 2097537 := by
  simp only [regionBlocks, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4, regionLength5, regionLength6, regionLength7, regionLength8, regionLength9, regionLength10, regionLength11, regionLength12, regionLength13, regionLength14, regionLength15]

theorem originalLength : (originals.flatten.map Setup.Block.length).sum = 2097537 := by
  simp only [originals, List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil]
  have len0 : (Airbender.Compiler.UnifiedEqualChunks.Column0.original0.map Setup.Block.length).sum = 2097537 := Airbender.Compiler.UnifiedEqualChunks.Column0.chunkLength0
  rw [len0]
  rfl

theorem prefix_value (index : Fin 2097537) : Data.GKRSetup.Unified.setupColumn0.get? index.val = Setup.getFromBlocks regionBlocks index.val := by
  change Setup.getFromBlocks Data.GKRSetup.Unified.setupColumn0.blocks.toList index.val = _
  rw [sourceShape, getFromBlocks_before_suffix _ _ index.val (by rw [originalLength]; have := index.isLt; omega), block_chunks_agree originals targets chunksChecked, ← targetShape]
  exact getFromBlocks_before_suffix regionBlocks extra index.val (by rw [regionTotal]; exact index.isLt)

end Airbender.Compiler.UnifiedAllPrefix.Column0
