import GKRProtocol.UnifiedSpecialParts.Column4.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source64 : Setup.Block := original.get ⟨64, by decide +kernel⟩

column_blocks_part part64_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 64 stop 65
noncomputable def destination64_0 : Setup.Block := part64_0.get ⟨0, by decide +kernel⟩

noncomputable def target64 : List Setup.Block := part64_0

theorem follows64 : blockTargetsFollow source64 0 target64 :=
  And.intro (by
    intro index bounded
    change source64.get? (0 + index) = destination64_0.get? index
    have same : source64 = destination64_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length64 : (target64.map Setup.Block.length).sum = source64.length := by decide +kernel

noncomputable def source65 : Setup.Block := original.get ⟨65, by decide +kernel⟩

column_blocks_part part65_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 65 stop 66
noncomputable def destination65_0 : Setup.Block := part65_0.get ⟨0, by decide +kernel⟩

noncomputable def target65 : List Setup.Block := part65_0

theorem follows65 : blockTargetsFollow source65 0 target65 :=
  And.intro (by
    intro index bounded
    change source65.get? (0 + index) = destination65_0.get? index
    have same : source65 = destination65_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length65 : (target65.map Setup.Block.length).sum = source65.length := by decide +kernel

noncomputable def source66 : Setup.Block := original.get ⟨66, by decide +kernel⟩

column_blocks_part part66_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 66 stop 67
noncomputable def destination66_0 : Setup.Block := part66_0.get ⟨0, by decide +kernel⟩

noncomputable def target66 : List Setup.Block := part66_0

theorem follows66 : blockTargetsFollow source66 0 target66 :=
  And.intro (by
    intro index bounded
    change source66.get? (0 + index) = destination66_0.get? index
    have same : source66 = destination66_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length66 : (target66.map Setup.Block.length).sum = source66.length := by decide +kernel

noncomputable def source67 : Setup.Block := original.get ⟨67, by decide +kernel⟩

column_blocks_part part67_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 67 stop 68
noncomputable def destination67_0 : Setup.Block := part67_0.get ⟨0, by decide +kernel⟩

noncomputable def target67 : List Setup.Block := part67_0

theorem follows67 : blockTargetsFollow source67 0 target67 :=
  And.intro (by
    intro index bounded
    change source67.get? (0 + index) = destination67_0.get? index
    have same : source67 = destination67_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length67 : (target67.map Setup.Block.length).sum = source67.length := by decide +kernel

noncomputable def source68 : Setup.Block := original.get ⟨68, by decide +kernel⟩

column_blocks_part part68_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 68 stop 69
noncomputable def destination68_0 : Setup.Block := part68_0.get ⟨0, by decide +kernel⟩

noncomputable def target68 : List Setup.Block := part68_0

theorem follows68 : blockTargetsFollow source68 0 target68 :=
  And.intro (by
    intro index bounded
    change source68.get? (0 + index) = destination68_0.get? index
    have same : source68 = destination68_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length68 : (target68.map Setup.Block.length).sum = source68.length := by decide +kernel

noncomputable def source69 : Setup.Block := original.get ⟨69, by decide +kernel⟩

column_blocks_part part69_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 69 stop 70
noncomputable def destination69_0 : Setup.Block := part69_0.get ⟨0, by decide +kernel⟩

noncomputable def target69 : List Setup.Block := part69_0

theorem follows69 : blockTargetsFollow source69 0 target69 :=
  And.intro (by
    intro index bounded
    change source69.get? (0 + index) = destination69_0.get? index
    have same : source69 = destination69_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length69 : (target69.map Setup.Block.length).sum = source69.length := by decide +kernel

noncomputable def source70 : Setup.Block := original.get ⟨70, by decide +kernel⟩

column_blocks_part part70_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 70 stop 71
noncomputable def destination70_0 : Setup.Block := part70_0.get ⟨0, by decide +kernel⟩

noncomputable def target70 : List Setup.Block := part70_0

theorem follows70 : blockTargetsFollow source70 0 target70 :=
  And.intro (by
    intro index bounded
    change source70.get? (0 + index) = destination70_0.get? index
    have same : source70 = destination70_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length70 : (target70.map Setup.Block.length).sum = source70.length := by decide +kernel

noncomputable def source71 : Setup.Block := original.get ⟨71, by decide +kernel⟩

column_blocks_part part71_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 71 stop 72
noncomputable def destination71_0 : Setup.Block := part71_0.get ⟨0, by decide +kernel⟩

noncomputable def target71 : List Setup.Block := part71_0

theorem follows71 : blockTargetsFollow source71 0 target71 :=
  And.intro (by
    intro index bounded
    change source71.get? (0 + index) = destination71_0.get? index
    have same : source71 = destination71_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length71 : (target71.map Setup.Block.length).sum = source71.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk0
