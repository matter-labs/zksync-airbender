import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Part0
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit8
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit9
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit10
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit11
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit12
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit13
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit14
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit15
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit16
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit17
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit18
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit19
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit20
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit21
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit22
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit23
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit24
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit25
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit26
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit27
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit28
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit29
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit30
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit31
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit32
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit33

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def sources : List Setup.Block := [source0, source1, source2, source3, source4, source5, source6, source7, source8, source9, source10, source11, source12, source13, source14, source15, source16, source17, source18, source19, source20, source21, source22, source23, source24, source25, source26, source27, source28, source29, source30, source31, source32, source33]

noncomputable def targets : List (List Setup.Block) := [target0, target1, target2, target3, target4, target5, target6, target7, target8, target9, target10, target11, target12, target13, target14, target15, target16, target17, target18, target19, target20, target21, target22, target23, target24, target25, target26, target27, target28, target29, target30, target31, target32, target33]

theorem sourcesAgree : original = sources := by rfl

theorem spansChecked : List.Forall₂ (fun source target => (target.map Setup.Block.length).sum = source.length ∧ blockTargetsFollow source 0 target) sources targets :=
  List.Forall₂.cons (⟨length0, follows0⟩) (List.Forall₂.cons (⟨length1, follows1⟩) (List.Forall₂.cons (⟨length2, follows2⟩) (List.Forall₂.cons (⟨length3, follows3⟩) (List.Forall₂.cons (⟨length4, follows4⟩) (List.Forall₂.cons (⟨length5, follows5⟩) (List.Forall₂.cons (⟨length6, follows6⟩) (List.Forall₂.cons (⟨length7, follows7⟩) (List.Forall₂.cons (⟨length8, follows8⟩) (List.Forall₂.cons (⟨length9, follows9⟩) (List.Forall₂.cons (⟨length10, follows10⟩) (List.Forall₂.cons (⟨length11, follows11⟩) (List.Forall₂.cons (⟨length12, follows12⟩) (List.Forall₂.cons (⟨length13, follows13⟩) (List.Forall₂.cons (⟨length14, follows14⟩) (List.Forall₂.cons (⟨length15, follows15⟩) (List.Forall₂.cons (⟨length16, follows16⟩) (List.Forall₂.cons (⟨length17, follows17⟩) (List.Forall₂.cons (⟨length18, follows18⟩) (List.Forall₂.cons (⟨length19, follows19⟩) (List.Forall₂.cons (⟨length20, follows20⟩) (List.Forall₂.cons (⟨length21, follows21⟩) (List.Forall₂.cons (⟨length22, follows22⟩) (List.Forall₂.cons (⟨length23, follows23⟩) (List.Forall₂.cons (⟨length24, follows24⟩) (List.Forall₂.cons (⟨length25, follows25⟩) (List.Forall₂.cons (⟨length26, follows26⟩) (List.Forall₂.cons (⟨length27, follows27⟩) (List.Forall₂.cons (⟨length28, follows28⟩) (List.Forall₂.cons (⟨length29, follows29⟩) (List.Forall₂.cons (⟨length30, follows30⟩) (List.Forall₂.cons (⟨length31, follows31⟩) (List.Forall₂.cons (⟨length32, follows32⟩) (List.Forall₂.cons (⟨length33, follows33⟩) (List.Forall₂.nil))))))))))))))))))))))))))))))))))

column_parts_cover sourceCoverage from Data.GKRSetup.Unified.setupColumn1 parts [original, suffix]

theorem sourceShape : Data.GKRSetup.Unified.setupColumn1.blocks.toList = original ++ suffix := by
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using sourceCoverage

column_parts_cover regionShape0 from (UnifiedReduced.Setup.nativeZeroData.columns[(1 : Nat)]) parts [part0_0]

theorem regionLength0 : ((UnifiedReduced.Setup.nativeZeroData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 1 := by decide +kernel

column_parts_cover regionShape1 from (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(1 : Nat)]) parts [part0_1, part1_0]

theorem regionLength1 : ((UnifiedReduced.Setup.nativeRegisterZeroData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 131072 := by decide +kernel

column_parts_cover regionShape2 from (UnifiedReduced.Setup.nativeCleanupData.columns[(1 : Nat)]) parts [part1_1, part2_0, part2_1]

theorem regionLength2 : ((UnifiedReduced.Setup.nativeCleanupData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by decide +kernel

column_parts_cover regionShape3 from (UnifiedReduced.Setup.nativeByteSignData.columns[(1 : Nat)]) parts [part2_2, part3_0, part4_0]

theorem regionLength3 : ((UnifiedReduced.Setup.nativeByteSignData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 256 := by decide +kernel

column_parts_cover regionShape4 from (UnifiedReduced.Setup.nativeSignData.columns[(1 : Nat)]) parts [part5_0, part6_0]

theorem regionLength4 : ((UnifiedReduced.Setup.nativeSignData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by decide +kernel

column_parts_cover regionShape5 from (UnifiedReduced.Setup.nativeTruncationData.columns[(1 : Nat)]) parts [part7_0]

theorem regionLength5 : ((UnifiedReduced.Setup.nativeTruncationData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by decide +kernel

column_parts_cover regionShape6 from (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]) parts [part8_0, part9_0, part10_0, part11_0]

theorem regionLength6 : ((UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 262144 := by decide +kernel

column_parts_cover regionShape7 from (UnifiedReduced.Setup.nativeROMData.columns[(1 : Nat)]) parts [part12_0, part13_0]

theorem regionLength7 : ((UnifiedReduced.Setup.nativeROMData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 1048576 := by decide +kernel

column_parts_cover regionShape8 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(1 : Nat)]) parts [part13_1, part14_0, part14_1]

theorem regionLength8 : ((UnifiedReduced.Setup.nativeRotate16Data.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by decide +kernel

column_parts_cover regionShape9 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(1 : Nat)]) parts [part14_2, part14_3, part14_4]

theorem regionLength9 : ((UnifiedReduced.Setup.nativeRotate12Data.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by decide +kernel

column_parts_cover regionShape10 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(1 : Nat)]) parts [part14_5, part14_6, part14_7]

theorem regionLength10 : ((UnifiedReduced.Setup.nativeRotate8Data.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by decide +kernel

column_parts_cover regionShape11 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(1 : Nat)]) parts [part14_8, part14_9, part14_10]

theorem regionLength11 : ((UnifiedReduced.Setup.nativeRotate7Data.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by decide +kernel

column_parts_cover regionShape12 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) parts [part14_11, part15_0, part16_0, part17_0, part18_0, part19_0, part20_0, part21_0, part22_0, part23_0, part24_0, part25_0, part26_0, part27_0, part28_0, part29_0, part30_0, part31_0, part32_0]

theorem regionLength12 : ((UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 128 := by decide +kernel

column_parts_cover regionShape13 from (UnifiedReduced.Setup.nativeXorData.columns[(1 : Nat)]) parts [part32_1, part33_0, part33_1]

theorem regionLength13 : ((UnifiedReduced.Setup.nativeXorData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by decide +kernel

column_parts_cover regionShape14 from (UnifiedReduced.Setup.nativeOrData.columns[(1 : Nat)]) parts [part33_2, part33_3, part33_4]

theorem regionLength14 : ((UnifiedReduced.Setup.nativeOrData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by decide +kernel

column_parts_cover regionShape15 from (UnifiedReduced.Setup.nativeAndData.columns[(1 : Nat)]) parts [part33_5, part33_6, part33_7]

theorem regionLength15 : ((UnifiedReduced.Setup.nativeAndData.columns[(1 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536 := by decide +kernel

noncomputable def regionBlocks : List Setup.Block := (UnifiedReduced.Setup.nativeZeroData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeCleanupData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeByteSignData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeSignData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeTruncationData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeROMData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate16Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate12Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate8Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeRotate7Data.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeXorData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeOrData.columns[(1 : Nat)]).blocks.toList ++ (UnifiedReduced.Setup.nativeAndData.columns[(1 : Nat)]).blocks.toList

noncomputable def extra : List Setup.Block := part33_8

theorem targetShape : regionBlocks ++ extra = targets.flatten := by
  rw [regionBlocks, regionShape0, regionShape1, regionShape2, regionShape3, regionShape4, regionShape5, regionShape6, regionShape7, regionShape8, regionShape9, regionShape10, regionShape11, regionShape12, regionShape13, regionShape14, regionShape15]
  simp only [extra, targets, target0, target1, target2, target3, target4, target5, target6, target7, target8, target9, target10, target11, target12, target13, target14, target15, target16, target17, target18, target19, target20, target21, target22, target23, target24, target25, target26, target27, target28, target29, target30, target31, target32, target33, List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]

theorem regionTotal : (regionBlocks.map Setup.Block.length).sum = 2097537 := by
  simp only [regionBlocks, List.map_append, List.sum_append, regionLength0, regionLength1, regionLength2, regionLength3, regionLength4, regionLength5, regionLength6, regionLength7, regionLength8, regionLength9, regionLength10, regionLength11, regionLength12, regionLength13, regionLength14, regionLength15]

theorem originalLength : (original.map Setup.Block.length).sum = 2097538 := by decide +kernel

theorem prefix_value (index : Fin 2097537) : Data.GKRSetup.Unified.setupColumn1.get? index.val = Setup.getFromBlocks regionBlocks index.val := by
  change Setup.getFromBlocks Data.GKRSetup.Unified.setupColumn1.blocks.toList index.val = _
  rw [sourceShape, getFromBlocks_before_suffix original suffix index.val (by rw [originalLength]; have := index.isLt; omega)]
  rw [sourcesAgree, block_partitions_agree sources targets spansChecked, ← targetShape]
  exact getFromBlocks_before_suffix regionBlocks extra index.val (by rw [regionTotal]; exact index.isLt)

end Airbender.Compiler.UnifiedPrefixNative.Column1
