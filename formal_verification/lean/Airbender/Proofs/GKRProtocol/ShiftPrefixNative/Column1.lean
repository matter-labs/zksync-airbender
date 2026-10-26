import Airbender.Proofs.GKRProtocol.ShiftPrefixParts.Column1.Part0
import Airbender.Review.Helpers.Tables.Bytes
import Airbender.Import.GKRProtocol.BlockCoverageImport

namespace Airbender.Compiler.ShiftPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

column_blocks_part suffix from Data.GKRSetup.ShiftBinop.setupColumn1 start 7 stop 9
noncomputable def originals : List (List Setup.Block) := [original0]

noncomputable def targets : List (List Setup.Block) := [target0]

column_parts_cover sourceCoverage from Data.GKRSetup.ShiftBinop.setupColumn1 parts [original0, suffix]

theorem sourceShape : Data.GKRSetup.ShiftBinop.setupColumn1.blocks.toList = originals.flatten ++ suffix := by
  apply sourceCoverage.trans
  simp only [originals, List.flatten_cons, List.flatten_nil, List.append_nil]

column_parts_cover regionShape0 from (Verification.byteZeroData.columns[(1 : Nat)]) parts [target0Region0]

column_parts_cover regionShape1 from (Verification.byteSignData.columns[(1 : Nat)]) parts [target0Region1]

column_parts_cover regionShape2 from (Verification.byteXorData.columns[(1 : Nat)]) parts [target0Region2]

column_parts_cover regionShape3 from (Verification.byteOrData.columns[(1 : Nat)]) parts [target0Region3]

column_parts_cover regionShape4 from (Verification.byteAndData.columns[(1 : Nat)]) parts [target0Region4]

column_parts_cover regionShape5 from (Verification.byteTruncateData.columns[(1 : Nat)]) parts [target0Region5]

column_parts_cover regionShape6 from Verification.byteShiftColumn1 parts [target0Region6]

theorem targetShape : (Verification.byteZeroData.columns[(1 : Nat)]).blocks.toList ++ (Verification.byteSignData.columns[(1 : Nat)]).blocks.toList ++ (Verification.byteXorData.columns[(1 : Nat)]).blocks.toList ++ (Verification.byteOrData.columns[(1 : Nat)]).blocks.toList ++ (Verification.byteAndData.columns[(1 : Nat)]).blocks.toList ++ (Verification.byteTruncateData.columns[(1 : Nat)]).blocks.toList ++ Verification.byteShiftColumn1.blocks.toList = targets.flatten := by
  rw [regionShape0, regionShape1, regionShape2, regionShape3, regionShape4, regionShape5, regionShape6]
  simp only [targets, target0, List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]

theorem chunksChecked : List.Forall₂ (fun first second => normalizeSetupBlocks first = normalizeSetupBlocks second) originals targets := by
  exact List.Forall₂.cons chunkChecked0 (List.Forall₂.nil)

theorem prefixLength : (originals.flatten.map Setup.Block.length).sum = 524545 := by
  simp only [originals, List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, chunkLength0]
  rfl

theorem region0Part0Length : (target0Region0.map Setup.Block.length).sum = 1 := by decide +kernel

theorem regionLength0 : ((Verification.byteZeroData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 1 := by
  rw [regionShape0]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region0Part0Length]
  rfl

theorem region1Part0Length : (target0Region1.map Setup.Block.length).sum = 256 := by decide +kernel

theorem regionLength1 : ((Verification.byteSignData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 256 := by
  rw [regionShape1]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region1Part0Length]
  rfl

theorem region2Part0Length : (target0Region2.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength2 : ((Verification.byteXorData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape2]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region2Part0Length]
  rfl

theorem region3Part0Length : (target0Region3.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength3 : ((Verification.byteOrData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape3]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region3Part0Length]
  rfl

theorem region4Part0Length : (target0Region4.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength4 : ((Verification.byteAndData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape4]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region4Part0Length]
  rfl

theorem region5Part0Length : (target0Region5.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength5 : ((Verification.byteTruncateData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape5]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region5Part0Length]
  rfl

theorem prefix_value (index : Fin 524545) :
    Data.GKRSetup.ShiftBinop.setupColumn1.get? index.val = Setup.getFromBlocks ((Verification.byteZeroData.columns[(1 : Nat)]).blocks.toList ++ (Verification.byteSignData.columns[(1 : Nat)]).blocks.toList ++ (Verification.byteXorData.columns[(1 : Nat)]).blocks.toList ++ (Verification.byteOrData.columns[(1 : Nat)]).blocks.toList ++ (Verification.byteAndData.columns[(1 : Nat)]).blocks.toList ++ (Verification.byteTruncateData.columns[(1 : Nat)]).blocks.toList ++ Verification.byteShiftColumn1.blocks.toList) index.val := by
  change Setup.getFromBlocks Data.GKRSetup.ShiftBinop.setupColumn1.blocks.toList index.val = _
  rw [sourceShape, getFromBlocks_before_suffix _ _ _ (by rw [prefixLength]; exact index.isLt), targetShape]
  exact normalized_chunks_agree originals targets chunksChecked index.val

theorem padding_value (index : Fin 16777216) (lower : 1573121 ≤ index.val) :
    Data.GKRSetup.ShiftBinop.setupColumn1.get? index.val = some 0 := by
  change Setup.getFromBlocks Data.GKRSetup.ShiftBinop.setupColumn1.blocks.toList index.val = some 0
  rw [sourceShape, getFromBlocks_append, prefixLength, if_neg (by omega)]
  change Setup.getFromBlocks [Setup.Block.affine 1048576 2013265920 0, .affine 15204095 0 0] (index.val - 524545) = some 0
  simp only [Setup.getFromBlocks, Setup.Block.length]
  rw [if_neg (by omega), if_pos (by omega)]
  apply constant_block_get
  omega

theorem clean_value (index : Fin 524545) :
    (Data.GKRSetup.ShiftBinop.setupColumn1.get? index.val).getD 0 = (Verification.shiftBinopRow index)[(1 : Nat)] := by
  have formula : (Verification.shiftBinopRow index)[(1 : Nat)] = (if index.val < 1 then (Setup.getFromBlocks (Verification.byteZeroData.columns[(1 : Nat)]).blocks.toList (index.val - 0)).getD 0 else if index.val < 257 then (Setup.getFromBlocks (Verification.byteSignData.columns[(1 : Nat)]).blocks.toList (index.val - 1)).getD 0 else if index.val < 65793 then (Setup.getFromBlocks (Verification.byteXorData.columns[(1 : Nat)]).blocks.toList (index.val - 257)).getD 0 else if index.val < 131329 then (Setup.getFromBlocks (Verification.byteOrData.columns[(1 : Nat)]).blocks.toList (index.val - 65793)).getD 0 else if index.val < 196865 then (Setup.getFromBlocks (Verification.byteAndData.columns[(1 : Nat)]).blocks.toList (index.val - 131329)).getD 0 else if index.val < 262401 then (Setup.getFromBlocks (Verification.byteTruncateData.columns[(1 : Nat)]).blocks.toList (index.val - 196865)).getD 0 else (Setup.getFromBlocks Verification.byteShiftColumn1.blocks.toList (index.val - 262401)).getD 0) := by
    change (if index.val < 1 then Verification.shiftRegionRow 0 (index.val - 0) else if index.val < 257 then Verification.shiftRegionRow 1 (index.val - 1) else if index.val < 65793 then Verification.shiftRegionRow 2 (index.val - 257) else if index.val < 131329 then Verification.shiftRegionRow 3 (index.val - 65793) else if index.val < 196865 then Verification.shiftRegionRow 4 (index.val - 131329) else if index.val < 262401 then Verification.shiftRegionRow 5 (index.val - 196865) else Verification.shiftRegionRow 6 (index.val - 262401))[(1 : Nat)] = _
    split_ifs <;> simp only [Verification.shiftRegionRow, Vector.getElem_map] <;> rfl
  rw [prefix_value, formula]
  simp only [List.append_assoc, getFromBlocks_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4, regionLength5, Nat.sub_sub, Nat.reduceAdd, Nat.sub_zero]
  split_ifs <;> omega

end Airbender.Compiler.ShiftPrefixNative.Column1
