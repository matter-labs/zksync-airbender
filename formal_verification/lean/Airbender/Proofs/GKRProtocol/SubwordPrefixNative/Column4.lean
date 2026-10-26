import Airbender.Proofs.GKRProtocol.SubwordPrefixParts.Column4.Part0
import Airbender.Import.GKRProtocol.BlockCoverageImport

namespace Airbender.Compiler.SubwordPrefixNative.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part suffix from Data.GKRSetup.SubwordMemory.setupColumn4 start 1 stop 3
noncomputable def originals : List (List Setup.Block) := [original0]

noncomputable def targets : List (List Setup.Block) := [target0]

noncomputable def target : List Setup.Block := (Verification.subwordZeroData.columns[(4 : Nat)]).blocks.toList ++ (Verification.storePlaceData.columns[(4 : Nat)]).blocks.toList ++ (Verification.storeClearData.columns[(4 : Nat)]).blocks.toList ++ (Verification.loadHalfData.columns[(4 : Nat)]).blocks.toList ++ (Verification.loadByteData.columns[(4 : Nat)]).blocks.toList ++ (Verification.subwordROMHalfData.columns[(4 : Nat)]).blocks.toList ++ (Verification.subwordROMByteData.columns[(4 : Nat)]).blocks.toList

column_parts_cover sourceCoverage from Data.GKRSetup.SubwordMemory.setupColumn4 parts [original0, suffix]

theorem sourceShape : Data.GKRSetup.SubwordMemory.setupColumn4.blocks.toList = originals.flatten ++ suffix := by
  apply sourceCoverage.trans
  simp only [originals, List.flatten_cons, List.flatten_nil, List.append_nil]

column_parts_cover regionShape0 from (Verification.subwordZeroData.columns[(4 : Nat)]) parts [target0Region0]

column_parts_cover regionShape1 from (Verification.storePlaceData.columns[(4 : Nat)]) parts [target0Region1]

column_parts_cover regionShape2 from (Verification.storeClearData.columns[(4 : Nat)]) parts [target0Region2]

column_parts_cover regionShape3 from (Verification.loadHalfData.columns[(4 : Nat)]) parts [target0Region3]

column_parts_cover regionShape4 from (Verification.loadByteData.columns[(4 : Nat)]) parts [target0Region4]

column_parts_cover regionShape5 from (Verification.subwordROMHalfData.columns[(4 : Nat)]) parts [target0Region5]

column_parts_cover regionShape6 from (Verification.subwordROMByteData.columns[(4 : Nat)]) parts [target0Region6]

theorem targetShape : target = targets.flatten := by
  rw [target, regionShape0, regionShape1, regionShape2, regionShape3, regionShape4, regionShape5, regionShape6]
  simp only [targets, target0, List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]

theorem chunksChecked : List.Forall₂ (fun left right => normalizeSetupBlocks left = normalizeSetupBlocks right) originals targets :=
  List.Forall₂.cons chunkChecked0 (List.Forall₂.nil)

theorem prefixLength : (originals.flatten.map Setup.Block.length).sum = 13238273 := by
  simp only [originals, List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, chunkLength0]
  rfl

theorem prefix_value (index : Fin 13238273) : Data.GKRSetup.SubwordMemory.setupColumn4.get? index.val = Setup.getFromBlocks target index.val := by
  change Setup.getFromBlocks Data.GKRSetup.SubwordMemory.setupColumn4.blocks.toList index.val = _
  rw [sourceShape, getFromBlocks_before_suffix _ _ index.val (by rw [prefixLength]; exact index.isLt), targetShape]
  exact normalized_chunks_agree originals targets chunksChecked index.val

theorem regionLength0 : ((Verification.subwordZeroData.columns[(4 : Nat)]).blocks.toList.map Setup.Block.length).sum = 1 := by decide +kernel

noncomputable def front0 : List Setup.Block := []
noncomputable def back0 : List Setup.Block := (Verification.storePlaceData.columns[(4 : Nat)]).blocks.toList ++ (Verification.storeClearData.columns[(4 : Nat)]).blocks.toList ++ (Verification.loadHalfData.columns[(4 : Nat)]).blocks.toList ++ (Verification.loadByteData.columns[(4 : Nat)]).blocks.toList ++ (Verification.subwordROMHalfData.columns[(4 : Nat)]).blocks.toList ++ (Verification.subwordROMByteData.columns[(4 : Nat)]).blocks.toList

theorem regionPrefix0 : (front0.map Setup.Block.length).sum = 0 := by
  rfl

theorem region_value0 (index : Fin 1) :
    Data.GKRSetup.SubwordMemory.setupColumn4.get? (0 + index.val) = (Verification.subwordZeroData.columns[(4 : Nat)]).get? index.val := by
  rw [prefix_value ⟨0 + index.val, by have := index.isLt; omega⟩]
  have shape : target = front0 ++ ((Verification.subwordZeroData.columns[(4 : Nat)]).blocks.toList ++ back0) := by
    simp only [target, front0, back0, List.append_assoc, List.nil_append]
  change Setup.getFromBlocks target (0 + index.val) = _
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front0 ((Verification.subwordZeroData.columns[(4 : Nat)]).blocks.toList ++ back0) index.val
  rw [regionPrefix0] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength0]; exact index.isLt))

theorem regionLength1 : ((Verification.storePlaceData.columns[(4 : Nat)]).blocks.toList.map Setup.Block.length).sum = 131072 := by decide +kernel

noncomputable def front1 : List Setup.Block := (Verification.subwordZeroData.columns[(4 : Nat)]).blocks.toList
noncomputable def back1 : List Setup.Block := (Verification.storeClearData.columns[(4 : Nat)]).blocks.toList ++ (Verification.loadHalfData.columns[(4 : Nat)]).blocks.toList ++ (Verification.loadByteData.columns[(4 : Nat)]).blocks.toList ++ (Verification.subwordROMHalfData.columns[(4 : Nat)]).blocks.toList ++ (Verification.subwordROMByteData.columns[(4 : Nat)]).blocks.toList

theorem regionPrefix1 : (front1.map Setup.Block.length).sum = 1 := by
  exact regionLength0

theorem region_value1 (index : Fin 131072) :
    Data.GKRSetup.SubwordMemory.setupColumn4.get? (1 + index.val) = (Verification.storePlaceData.columns[(4 : Nat)]).get? index.val := by
  rw [prefix_value ⟨1 + index.val, by have := index.isLt; omega⟩]
  have shape : target = front1 ++ ((Verification.storePlaceData.columns[(4 : Nat)]).blocks.toList ++ back1) := by
    simp only [target, front1, back1, List.append_assoc]
  change Setup.getFromBlocks target (1 + index.val) = _
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front1 ((Verification.storePlaceData.columns[(4 : Nat)]).blocks.toList ++ back1) index.val
  rw [regionPrefix1] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength1]; exact index.isLt))

theorem regionLength2 : ((Verification.storeClearData.columns[(4 : Nat)]).blocks.toList.map Setup.Block.length).sum = 131072 := by decide +kernel

noncomputable def front2 : List Setup.Block := (Verification.subwordZeroData.columns[(4 : Nat)]).blocks.toList ++ (Verification.storePlaceData.columns[(4 : Nat)]).blocks.toList
noncomputable def back2 : List Setup.Block := (Verification.loadHalfData.columns[(4 : Nat)]).blocks.toList ++ (Verification.loadByteData.columns[(4 : Nat)]).blocks.toList ++ (Verification.subwordROMHalfData.columns[(4 : Nat)]).blocks.toList ++ (Verification.subwordROMByteData.columns[(4 : Nat)]).blocks.toList

theorem regionPrefix2 : (front2.map Setup.Block.length).sum = 131073 := by
  simp only [front2, List.map_append, List.sum_append, regionLength0, regionLength1]

theorem region_value2 (index : Fin 131072) :
    Data.GKRSetup.SubwordMemory.setupColumn4.get? (131073 + index.val) = (Verification.storeClearData.columns[(4 : Nat)]).get? index.val := by
  rw [prefix_value ⟨131073 + index.val, by have := index.isLt; omega⟩]
  have shape : target = front2 ++ ((Verification.storeClearData.columns[(4 : Nat)]).blocks.toList ++ back2) := by
    simp only [target, front2, back2, List.append_assoc]
  change Setup.getFromBlocks target (131073 + index.val) = _
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front2 ((Verification.storeClearData.columns[(4 : Nat)]).blocks.toList ++ back2) index.val
  rw [regionPrefix2] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength2]; exact index.isLt))

theorem regionLength3 : ((Verification.loadHalfData.columns[(4 : Nat)]).blocks.toList.map Setup.Block.length).sum = 131072 := by decide +kernel

noncomputable def front3 : List Setup.Block := (Verification.subwordZeroData.columns[(4 : Nat)]).blocks.toList ++ (Verification.storePlaceData.columns[(4 : Nat)]).blocks.toList ++ (Verification.storeClearData.columns[(4 : Nat)]).blocks.toList
noncomputable def back3 : List Setup.Block := (Verification.loadByteData.columns[(4 : Nat)]).blocks.toList ++ (Verification.subwordROMHalfData.columns[(4 : Nat)]).blocks.toList ++ (Verification.subwordROMByteData.columns[(4 : Nat)]).blocks.toList

theorem regionPrefix3 : (front3.map Setup.Block.length).sum = 262145 := by
  simp only [front3, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2]

theorem region_value3 (index : Fin 131072) :
    Data.GKRSetup.SubwordMemory.setupColumn4.get? (262145 + index.val) = (Verification.loadHalfData.columns[(4 : Nat)]).get? index.val := by
  rw [prefix_value ⟨262145 + index.val, by have := index.isLt; omega⟩]
  have shape : target = front3 ++ ((Verification.loadHalfData.columns[(4 : Nat)]).blocks.toList ++ back3) := by
    simp only [target, front3, back3, List.append_assoc]
  change Setup.getFromBlocks target (262145 + index.val) = _
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front3 ((Verification.loadHalfData.columns[(4 : Nat)]).blocks.toList ++ back3) index.val
  rw [regionPrefix3] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength3]; exact index.isLt))

theorem regionLength4 : ((Verification.loadByteData.columns[(4 : Nat)]).blocks.toList.map Setup.Block.length).sum = 262144 := by decide +kernel

noncomputable def front4 : List Setup.Block := (Verification.subwordZeroData.columns[(4 : Nat)]).blocks.toList ++ (Verification.storePlaceData.columns[(4 : Nat)]).blocks.toList ++ (Verification.storeClearData.columns[(4 : Nat)]).blocks.toList ++ (Verification.loadHalfData.columns[(4 : Nat)]).blocks.toList
noncomputable def back4 : List Setup.Block := (Verification.subwordROMHalfData.columns[(4 : Nat)]).blocks.toList ++ (Verification.subwordROMByteData.columns[(4 : Nat)]).blocks.toList

theorem regionPrefix4 : (front4.map Setup.Block.length).sum = 393217 := by
  simp only [front4, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3]

theorem region_value4 (index : Fin 262144) :
    Data.GKRSetup.SubwordMemory.setupColumn4.get? (393217 + index.val) = (Verification.loadByteData.columns[(4 : Nat)]).get? index.val := by
  rw [prefix_value ⟨393217 + index.val, by have := index.isLt; omega⟩]
  have shape : target = front4 ++ ((Verification.loadByteData.columns[(4 : Nat)]).blocks.toList ++ back4) := by
    simp only [target, front4, back4, List.append_assoc]
  change Setup.getFromBlocks target (393217 + index.val) = _
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front4 ((Verification.loadByteData.columns[(4 : Nat)]).blocks.toList ++ back4) index.val
  rw [regionPrefix4] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength4]; exact index.isLt))

theorem regionLength5 : ((Verification.subwordROMHalfData.columns[(4 : Nat)]).blocks.toList.map Setup.Block.length).sum = 4194304 := by decide +kernel

noncomputable def front5 : List Setup.Block := (Verification.subwordZeroData.columns[(4 : Nat)]).blocks.toList ++ (Verification.storePlaceData.columns[(4 : Nat)]).blocks.toList ++ (Verification.storeClearData.columns[(4 : Nat)]).blocks.toList ++ (Verification.loadHalfData.columns[(4 : Nat)]).blocks.toList ++ (Verification.loadByteData.columns[(4 : Nat)]).blocks.toList
noncomputable def back5 : List Setup.Block := (Verification.subwordROMByteData.columns[(4 : Nat)]).blocks.toList

theorem regionPrefix5 : (front5.map Setup.Block.length).sum = 655361 := by
  simp only [front5, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4]

theorem region_value5 (index : Fin 4194304) :
    Data.GKRSetup.SubwordMemory.setupColumn4.get? (655361 + index.val) = (Verification.subwordROMHalfData.columns[(4 : Nat)]).get? index.val := by
  rw [prefix_value ⟨655361 + index.val, by have := index.isLt; omega⟩]
  have shape : target = front5 ++ ((Verification.subwordROMHalfData.columns[(4 : Nat)]).blocks.toList ++ back5) := by
    simp only [target, front5, back5, List.append_assoc]
  change Setup.getFromBlocks target (655361 + index.val) = _
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front5 ((Verification.subwordROMHalfData.columns[(4 : Nat)]).blocks.toList ++ back5) index.val
  rw [regionPrefix5] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength5]; exact index.isLt))

theorem regionLength6 : ((Verification.subwordROMByteData.columns[(4 : Nat)]).blocks.toList.map Setup.Block.length).sum = 8388608 := by decide +kernel

noncomputable def front6 : List Setup.Block := (Verification.subwordZeroData.columns[(4 : Nat)]).blocks.toList ++ (Verification.storePlaceData.columns[(4 : Nat)]).blocks.toList ++ (Verification.storeClearData.columns[(4 : Nat)]).blocks.toList ++ (Verification.loadHalfData.columns[(4 : Nat)]).blocks.toList ++ (Verification.loadByteData.columns[(4 : Nat)]).blocks.toList ++ (Verification.subwordROMHalfData.columns[(4 : Nat)]).blocks.toList
noncomputable def back6 : List Setup.Block := []

theorem regionPrefix6 : (front6.map Setup.Block.length).sum = 4849665 := by
  simp only [front6, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4, regionLength5]

theorem region_value6 (index : Fin 8388608) :
    Data.GKRSetup.SubwordMemory.setupColumn4.get? (4849665 + index.val) = (Verification.subwordROMByteData.columns[(4 : Nat)]).get? index.val := by
  rw [prefix_value ⟨4849665 + index.val, by have := index.isLt; omega⟩]
  have shape : target = front6 ++ ((Verification.subwordROMByteData.columns[(4 : Nat)]).blocks.toList ++ back6) := by
    simp only [target, front6, back6, List.append_assoc, List.append_nil]
  change Setup.getFromBlocks target (4849665 + index.val) = _
  rw [shape]
  have skipped := Setup.Proofs.skip_blocks front6 ((Verification.subwordROMByteData.columns[(4 : Nat)]).blocks.toList ++ back6) index.val
  rw [regionPrefix6] at skipped
  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength6]; exact index.isLt))

end Airbender.Compiler.SubwordPrefixNative.Column4
