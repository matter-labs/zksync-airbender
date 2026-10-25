import GKRProtocol.ShiftPrefixParts.Column2.Part0
import GKRProtocol.ShiftPrefixParts.Column2.Part1
import GKRProtocol.ShiftPrefixParts.Column2.Part2
import Airbender.Review.Helpers.Tables.Bytes
import GKRProtocol.BlockCoverageImport

namespace Airbender.Compiler.ShiftPrefixNative.Column2
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

column_blocks_part suffix from Data.GKRSetup.ShiftBinop.setupColumn2 start 2704 stop 2706
noncomputable def originals : List (List Setup.Block) := [original0, original1, original2, original3, original4, original5, original6, original7, original8, original9, original10, original11, original12, original13, original14, original15, original16, original17, original18, original19, original20, original21]

noncomputable def targets : List (List Setup.Block) := [target0, target1, target2, target3, target4, target5, target6, target7, target8, target9, target10, target11, target12, target13, target14, target15, target16, target17, target18, target19, target20, target21]

column_parts_cover sourceCoverage from Data.GKRSetup.ShiftBinop.setupColumn2 parts [original0, original1, original2, original3, original4, original5, original6, original7, original8, original9, original10, original11, original12, original13, original14, original15, original16, original17, original18, original19, original20, original21, suffix]

theorem sourceShape : Data.GKRSetup.ShiftBinop.setupColumn2.blocks.toList = originals.flatten ++ suffix := by
  apply sourceCoverage.trans
  simp only [originals, List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]

column_parts_cover regionShape0 from (Verification.byteZeroData.columns[(2 : Nat)]) parts [target0Region0]

column_parts_cover regionShape1 from (Verification.byteSignData.columns[(2 : Nat)]) parts [target0Region1]

column_parts_cover regionShape2 from (Verification.byteXorData.columns[(2 : Nat)]) parts [target0Region2, target1Region2, target2Region2, target3Region2, target4Region2, target5Region2, target6Region2, target7Region2]

column_parts_cover regionShape3 from (Verification.byteOrData.columns[(2 : Nat)]) parts [target7Region3, target8Region3, target9Region3, target10Region3, target11Region3, target12Region3, target13Region3, target14Region3]

column_parts_cover regionShape4 from (Verification.byteAndData.columns[(2 : Nat)]) parts [target14Region4, target15Region4, target16Region4, target17Region4, target18Region4, target19Region4, target20Region4, target21Region4]

column_parts_cover regionShape5 from (Verification.byteTruncateData.columns[(2 : Nat)]) parts [target21Region5]

column_parts_cover regionShape6 from Verification.byteShiftColumn2 parts [target21Region6]

theorem targetShape : (Verification.byteZeroData.columns[(2 : Nat)]).blocks.toList ++ (Verification.byteSignData.columns[(2 : Nat)]).blocks.toList ++ (Verification.byteXorData.columns[(2 : Nat)]).blocks.toList ++ (Verification.byteOrData.columns[(2 : Nat)]).blocks.toList ++ (Verification.byteAndData.columns[(2 : Nat)]).blocks.toList ++ (Verification.byteTruncateData.columns[(2 : Nat)]).blocks.toList ++ Verification.byteShiftColumn2.blocks.toList = targets.flatten := by
  rw [regionShape0, regionShape1, regionShape2, regionShape3, regionShape4, regionShape5, regionShape6]
  simp only [targets, target0, target1, target2, target3, target4, target5, target6, target7, target8, target9, target10, target11, target12, target13, target14, target15, target16, target17, target18, target19, target20, target21, List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]

theorem chunksChecked : List.Forall₂ (fun first second => normalizeSetupBlocks first = normalizeSetupBlocks second) originals targets := by
  exact List.Forall₂.cons chunkChecked0 (List.Forall₂.cons chunkChecked1 (List.Forall₂.cons chunkChecked2 (List.Forall₂.cons chunkChecked3 (List.Forall₂.cons chunkChecked4 (List.Forall₂.cons chunkChecked5 (List.Forall₂.cons chunkChecked6 (List.Forall₂.cons chunkChecked7 (List.Forall₂.cons chunkChecked8 (List.Forall₂.cons chunkChecked9 (List.Forall₂.cons chunkChecked10 (List.Forall₂.cons chunkChecked11 (List.Forall₂.cons chunkChecked12 (List.Forall₂.cons chunkChecked13 (List.Forall₂.cons chunkChecked14 (List.Forall₂.cons chunkChecked15 (List.Forall₂.cons chunkChecked16 (List.Forall₂.cons chunkChecked17 (List.Forall₂.cons chunkChecked18 (List.Forall₂.cons chunkChecked19 (List.Forall₂.cons chunkChecked20 (List.Forall₂.cons chunkChecked21 (List.Forall₂.nil))))))))))))))))))))))

theorem prefixLength : (originals.flatten.map Setup.Block.length).sum = 524545 := by
  simp only [originals, List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, chunkLength0, chunkLength1, chunkLength2, chunkLength3, chunkLength4, chunkLength5, chunkLength6, chunkLength7, chunkLength8, chunkLength9, chunkLength10, chunkLength11, chunkLength12, chunkLength13, chunkLength14, chunkLength15, chunkLength16, chunkLength17, chunkLength18, chunkLength19, chunkLength20, chunkLength21]
  rfl

theorem region0Part0Length : (target0Region0.map Setup.Block.length).sum = 1 := by decide +kernel

theorem regionLength0 : ((Verification.byteZeroData.columns[(2 : Nat)]).blocks.toList.map Setup.Block.length).sum = 1 := by
  rw [regionShape0]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region0Part0Length]
  rfl

theorem region1Part0Length : (target0Region1.map Setup.Block.length).sum = 256 := by decide +kernel

theorem regionLength1 : ((Verification.byteSignData.columns[(2 : Nat)]).blocks.toList.map Setup.Block.length).sum = 256 := by
  rw [regionShape1]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region1Part0Length]
  rfl

theorem region2Part0Length : (target0Region2.map Setup.Block.length).sum = 20416 := by decide +kernel

theorem region2Part1Length : (target1Region2.map Setup.Block.length).sum = 1340 := by decide +kernel

theorem region2Part2Length : (target2Region2.map Setup.Block.length).sum = 2756 := by decide +kernel

theorem region2Part3Length : (target3Region2.map Setup.Block.length).sum = 16192 := by decide +kernel

theorem region2Part4Length : (target4Region2.map Setup.Block.length).sum = 2800 := by decide +kernel

theorem region2Part5Length : (target5Region2.map Setup.Block.length).sum = 1504 := by decide +kernel

theorem region2Part6Length : (target6Region2.map Setup.Block.length).sum = 19760 := by decide +kernel

theorem region2Part7Length : (target7Region2.map Setup.Block.length).sum = 768 := by decide +kernel

theorem regionLength2 : ((Verification.byteXorData.columns[(2 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape2]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region2Part0Length, region2Part1Length, region2Part2Length, region2Part3Length, region2Part4Length, region2Part5Length, region2Part6Length, region2Part7Length]
  rfl

theorem region3Part7Length : (target7Region3.map Setup.Block.length).sum = 20288 := by decide +kernel

theorem region3Part8Length : (target8Region3.map Setup.Block.length).sum = 1460 := by decide +kernel

theorem region3Part9Length : (target9Region3.map Setup.Block.length).sum = 2700 := by decide +kernel

theorem region3Part10Length : (target10Region3.map Setup.Block.length).sum = 16000 := by decide +kernel

theorem region3Part11Length : (target11Region3.map Setup.Block.length).sum = 3040 := by decide +kernel

theorem region3Part12Length : (target12Region3.map Setup.Block.length).sum = 1488 := by decide +kernel

theorem region3Part13Length : (target13Region3.map Setup.Block.length).sum = 19280 := by decide +kernel

theorem region3Part14Length : (target14Region3.map Setup.Block.length).sum = 1280 := by decide +kernel

theorem regionLength3 : ((Verification.byteOrData.columns[(2 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape3]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region3Part7Length, region3Part8Length, region3Part9Length, region3Part10Length, region3Part11Length, region3Part12Length, region3Part13Length, region3Part14Length]
  rfl

theorem region4Part14Length : (target14Region4.map Setup.Block.length).sum = 20160 := by decide +kernel

theorem region4Part15Length : (target15Region4.map Setup.Block.length).sum = 1580 := by decide +kernel

theorem region4Part16Length : (target16Region4.map Setup.Block.length).sum = 2644 := by decide +kernel

theorem region4Part17Length : (target17Region4.map Setup.Block.length).sum = 15808 := by decide +kernel

theorem region4Part18Length : (target18Region4.map Setup.Block.length).sum = 3280 := by decide +kernel

theorem region4Part19Length : (target19Region4.map Setup.Block.length).sum = 1472 := by decide +kernel

theorem region4Part20Length : (target20Region4.map Setup.Block.length).sum = 18800 := by decide +kernel

theorem region4Part21Length : (target21Region4.map Setup.Block.length).sum = 1792 := by decide +kernel

theorem regionLength4 : ((Verification.byteAndData.columns[(2 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape4]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region4Part14Length, region4Part15Length, region4Part16Length, region4Part17Length, region4Part18Length, region4Part19Length, region4Part20Length, region4Part21Length]
  rfl

theorem region5Part21Length : (target21Region5.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem regionLength5 : ((Verification.byteTruncateData.columns[(2 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by
  rw [regionShape5]
  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, region5Part21Length]
  rfl

theorem prefix_value (index : Fin 524545) :
    Data.GKRSetup.ShiftBinop.setupColumn2.get? index.val = Setup.getFromBlocks ((Verification.byteZeroData.columns[(2 : Nat)]).blocks.toList ++ (Verification.byteSignData.columns[(2 : Nat)]).blocks.toList ++ (Verification.byteXorData.columns[(2 : Nat)]).blocks.toList ++ (Verification.byteOrData.columns[(2 : Nat)]).blocks.toList ++ (Verification.byteAndData.columns[(2 : Nat)]).blocks.toList ++ (Verification.byteTruncateData.columns[(2 : Nat)]).blocks.toList ++ Verification.byteShiftColumn2.blocks.toList) index.val := by
  change Setup.getFromBlocks Data.GKRSetup.ShiftBinop.setupColumn2.blocks.toList index.val = _
  rw [sourceShape, getFromBlocks_before_suffix _ _ _ (by rw [prefixLength]; exact index.isLt), targetShape]
  exact normalized_chunks_agree originals targets chunksChecked index.val

theorem padding_value (index : Fin 16777216) (lower : 1573121 ≤ index.val) :
    Data.GKRSetup.ShiftBinop.setupColumn2.get? index.val = some 0 := by
  change Setup.getFromBlocks Data.GKRSetup.ShiftBinop.setupColumn2.blocks.toList index.val = some 0
  rw [sourceShape, getFromBlocks_append, prefixLength, if_neg (by omega)]
  change Setup.getFromBlocks [Setup.Block.affine 1048576 2013265920 0, .affine 15204095 0 0] (index.val - 524545) = some 0
  simp only [Setup.getFromBlocks, Setup.Block.length]
  rw [if_neg (by omega), if_pos (by omega)]
  apply constant_block_get
  omega

theorem clean_value (index : Fin 524545) :
    (Data.GKRSetup.ShiftBinop.setupColumn2.get? index.val).getD 0 = (Verification.shiftBinopRow index)[(2 : Nat)] := by
  have formula : (Verification.shiftBinopRow index)[(2 : Nat)] = (if index.val < 1 then (Setup.getFromBlocks (Verification.byteZeroData.columns[(2 : Nat)]).blocks.toList (index.val - 0)).getD 0 else if index.val < 257 then (Setup.getFromBlocks (Verification.byteSignData.columns[(2 : Nat)]).blocks.toList (index.val - 1)).getD 0 else if index.val < 65793 then (Setup.getFromBlocks (Verification.byteXorData.columns[(2 : Nat)]).blocks.toList (index.val - 257)).getD 0 else if index.val < 131329 then (Setup.getFromBlocks (Verification.byteOrData.columns[(2 : Nat)]).blocks.toList (index.val - 65793)).getD 0 else if index.val < 196865 then (Setup.getFromBlocks (Verification.byteAndData.columns[(2 : Nat)]).blocks.toList (index.val - 131329)).getD 0 else if index.val < 262401 then (Setup.getFromBlocks (Verification.byteTruncateData.columns[(2 : Nat)]).blocks.toList (index.val - 196865)).getD 0 else (Setup.getFromBlocks Verification.byteShiftColumn2.blocks.toList (index.val - 262401)).getD 0) := by
    change (if index.val < 1 then Verification.shiftRegionRow 0 (index.val - 0) else if index.val < 257 then Verification.shiftRegionRow 1 (index.val - 1) else if index.val < 65793 then Verification.shiftRegionRow 2 (index.val - 257) else if index.val < 131329 then Verification.shiftRegionRow 3 (index.val - 65793) else if index.val < 196865 then Verification.shiftRegionRow 4 (index.val - 131329) else if index.val < 262401 then Verification.shiftRegionRow 5 (index.val - 196865) else Verification.shiftRegionRow 6 (index.val - 262401))[(2 : Nat)] = _
    split_ifs <;> simp only [Verification.shiftRegionRow, Vector.getElem_map] <;> rfl
  rw [prefix_value, formula]
  simp only [List.append_assoc, getFromBlocks_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4, regionLength5, Nat.sub_sub, Nat.reduceAdd, Nat.sub_zero]
  split_ifs <;> omega

end Airbender.Compiler.ShiftPrefixNative.Column2
