import Airbender.Proofs.GKRProtocol.UnifiedPackedEqualityCertificate

namespace Airbender.Compiler.UnifiedEqualChunks.Column2
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false

noncomputable def original1 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 0).take 128
noncomputable def target1Region13 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 0).take 128
noncomputable def target1 : List Setup.Block := target1Region13

theorem chunkSame1 : original1 = target1 := by
  exact UnifiedPackedEquality.slice_eq 0 128

theorem chunkLength1 : (original1.map Setup.Block.length).sum = 2360 := by
  exact UnifiedPackedEquality.length_at ⟨0, by decide +kernel⟩

noncomputable def original2 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 128).take 128
noncomputable def target2Region13 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 128).take 128
noncomputable def target2 : List Setup.Block := target2Region13

theorem chunkSame2 : original2 = target2 := by
  exact UnifiedPackedEquality.slice_eq 128 128

theorem chunkLength2 : (original2.map Setup.Block.length).sum = 2280 := by
  exact UnifiedPackedEquality.length_at ⟨1, by decide +kernel⟩

noncomputable def original3 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 256).take 128
noncomputable def target3Region13 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 256).take 128
noncomputable def target3 : List Setup.Block := target3Region13

theorem chunkSame3 : original3 = target3 := by
  exact UnifiedPackedEquality.slice_eq 256 128

theorem chunkLength3 : (original3.map Setup.Block.length).sum = 14560 := by
  exact UnifiedPackedEquality.length_at ⟨2, by decide +kernel⟩

noncomputable def original4 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 384).take 128
noncomputable def target4Region13 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 384).take 128
noncomputable def target4 : List Setup.Block := target4Region13

theorem chunkSame4 : original4 = target4 := by
  exact UnifiedPackedEquality.slice_eq 384 128

theorem chunkLength4 : (original4.map Setup.Block.length).sum = 4840 := by
  exact UnifiedPackedEquality.length_at ⟨3, by decide +kernel⟩

noncomputable def original5 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 512).take 128
noncomputable def target5Region13 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 512).take 128
noncomputable def target5 : List Setup.Block := target5Region13

theorem chunkSame5 : original5 = target5 := by
  exact UnifiedPackedEquality.slice_eq 512 128

theorem chunkLength5 : (original5.map Setup.Block.length).sum = 1368 := by
  exact UnifiedPackedEquality.length_at ⟨4, by decide +kernel⟩

noncomputable def original6 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 640).take 128
noncomputable def target6Region13 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 640).take 128
noncomputable def target6 : List Setup.Block := target6Region13

theorem chunkSame6 : original6 = target6 := by
  exact UnifiedPackedEquality.slice_eq 640 128

theorem chunkLength6 : (original6.map Setup.Block.length).sum = 15680 := by
  exact UnifiedPackedEquality.length_at ⟨5, by decide +kernel⟩

noncomputable def original7 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 768).take 128
noncomputable def target7Region13 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 768).take 20
noncomputable def target7Region14 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 788).take 108
noncomputable def target7 : List Setup.Block := target7Region13 ++ target7Region14

theorem chunkSame7 : original7 = target7 := by
  exact (UnifiedPackedEquality.slice_eq 768 128).trans
    (PackedSetupEquality.slice_split UnifiedPackedEquality.targetBlocks 768 20 108)

theorem chunkLength7 : (original7.map Setup.Block.length).sum = 24320 := by
  exact UnifiedPackedEquality.length_at ⟨6, by decide +kernel⟩

noncomputable def original8 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 896).take 128
noncomputable def target8Region14 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 896).take 128
noncomputable def target8 : List Setup.Block := target8Region14

theorem chunkSame8 : original8 = target8 := by
  exact UnifiedPackedEquality.slice_eq 896 128

theorem chunkLength8 : (original8.map Setup.Block.length).sum = 2480 := by
  exact UnifiedPackedEquality.length_at ⟨7, by decide +kernel⟩

noncomputable def original9 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 1024).take 128
noncomputable def target9Region14 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 1024).take 128
noncomputable def target9 : List Setup.Block := target9Region14

theorem chunkSame9 : original9 = target9 := by
  exact UnifiedPackedEquality.slice_eq 1024 128

theorem chunkLength9 : (original9.map Setup.Block.length).sum = 2224 := by
  exact UnifiedPackedEquality.length_at ⟨8, by decide +kernel⟩

noncomputable def original10 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 1152).take 128
noncomputable def target10Region14 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 1152).take 128
noncomputable def target10 : List Setup.Block := target10Region14

theorem chunkSame10 : original10 = target10 := by
  exact UnifiedPackedEquality.slice_eq 1152 128

theorem chunkLength10 : (original10.map Setup.Block.length).sum = 14368 := by
  exact UnifiedPackedEquality.length_at ⟨9, by decide +kernel⟩

noncomputable def original11 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 1280).take 128
noncomputable def target11Region14 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 1280).take 128
noncomputable def target11 : List Setup.Block := target11Region14

theorem chunkSame11 : original11 = target11 := by
  exact UnifiedPackedEquality.slice_eq 1280 128

theorem chunkLength11 : (original11.map Setup.Block.length).sum = 5080 := by
  exact UnifiedPackedEquality.length_at ⟨10, by decide +kernel⟩

noncomputable def original12 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 1408).take 128
noncomputable def target12Region14 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 1408).take 128
noncomputable def target12 : List Setup.Block := target12Region14

theorem chunkSame12 : original12 = target12 := by
  exact UnifiedPackedEquality.slice_eq 1408 128

theorem chunkLength12 : (original12.map Setup.Block.length).sum = 1352 := by
  exact UnifiedPackedEquality.length_at ⟨11, by decide +kernel⟩

noncomputable def original13 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 1536).take 128
noncomputable def target13Region14 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 1536).take 128
noncomputable def target13 : List Setup.Block := target13Region14

theorem chunkSame13 : original13 = target13 := by
  exact UnifiedPackedEquality.slice_eq 1536 128

theorem chunkLength13 : (original13.map Setup.Block.length).sum = 15200 := by
  exact UnifiedPackedEquality.length_at ⟨12, by decide +kernel⟩

noncomputable def original14 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 1664).take 128
noncomputable def target14Region14 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 1664).take 22
noncomputable def target14Region15 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 1686).take 106
noncomputable def target14 : List Setup.Block := target14Region14 ++ target14Region15

theorem chunkSame14 : original14 = target14 := by
  exact (UnifiedPackedEquality.slice_eq 1664 128).trans
    (PackedSetupEquality.slice_split UnifiedPackedEquality.targetBlocks 1664 22 106)

theorem chunkLength14 : (original14.map Setup.Block.length).sum = 24704 := by
  exact UnifiedPackedEquality.length_at ⟨13, by decide +kernel⟩

noncomputable def original15 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 1792).take 128
noncomputable def target15Region15 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 1792).take 128
noncomputable def target15 : List Setup.Block := target15Region15

theorem chunkSame15 : original15 = target15 := by
  exact UnifiedPackedEquality.slice_eq 1792 128

theorem chunkLength15 : (original15.map Setup.Block.length).sum = 2600 := by
  exact UnifiedPackedEquality.length_at ⟨14, by decide +kernel⟩

noncomputable def original16 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 1920).take 128
noncomputable def target16Region15 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 1920).take 128
noncomputable def target16 : List Setup.Block := target16Region15

theorem chunkSame16 : original16 = target16 := by
  exact UnifiedPackedEquality.slice_eq 1920 128

theorem chunkLength16 : (original16.map Setup.Block.length).sum = 2168 := by
  exact UnifiedPackedEquality.length_at ⟨15, by decide +kernel⟩

noncomputable def original17 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 2048).take 128
noncomputable def target17Region15 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 2048).take 128
noncomputable def target17 : List Setup.Block := target17Region15

theorem chunkSame17 : original17 = target17 := by
  exact UnifiedPackedEquality.slice_eq 2048 128

theorem chunkLength17 : (original17.map Setup.Block.length).sum = 14176 := by
  exact UnifiedPackedEquality.length_at ⟨16, by decide +kernel⟩

noncomputable def original18 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 2176).take 128
noncomputable def target18Region15 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 2176).take 128
noncomputable def target18 : List Setup.Block := target18Region15

theorem chunkSame18 : original18 = target18 := by
  exact UnifiedPackedEquality.slice_eq 2176 128

theorem chunkLength18 : (original18.map Setup.Block.length).sum = 5320 := by
  exact UnifiedPackedEquality.length_at ⟨17, by decide +kernel⟩

noncomputable def original19 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 2304).take 128
noncomputable def target19Region15 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 2304).take 128
noncomputable def target19 : List Setup.Block := target19Region15

theorem chunkSame19 : original19 = target19 := by
  exact UnifiedPackedEquality.slice_eq 2304 128

theorem chunkLength19 : (original19.map Setup.Block.length).sum = 1336 := by
  exact UnifiedPackedEquality.length_at ⟨18, by decide +kernel⟩

noncomputable def original20 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 2432).take 128
noncomputable def target20Region15 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 2432).take 128
noncomputable def target20 : List Setup.Block := target20Region15

theorem chunkSame20 : original20 = target20 := by
  exact UnifiedPackedEquality.slice_eq 2432 128

theorem chunkLength20 : (original20.map Setup.Block.length).sum = 14720 := by
  exact UnifiedPackedEquality.length_at ⟨19, by decide +kernel⟩

noncomputable def original21 : List Setup.Block :=
  (UnifiedPackedEquality.sourceBlocks.drop 2560).take 24
noncomputable def target21Region15 : List Setup.Block :=
  (UnifiedPackedEquality.targetBlocks.drop 2560).take 24
noncomputable def target21 : List Setup.Block := target21Region15

theorem chunkSame21 : original21 = target21 := by
  exact UnifiedPackedEquality.slice_eq 2560 24

theorem chunkLength21 : (original21.map Setup.Block.length).sum = 6144 := by
  exact UnifiedPackedEquality.length_at ⟨20, by decide +kernel⟩

end Airbender.Compiler.UnifiedEqualChunks.Column2
