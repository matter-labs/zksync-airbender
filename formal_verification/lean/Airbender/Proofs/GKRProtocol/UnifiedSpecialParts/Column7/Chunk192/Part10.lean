import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column7.Chunk192.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24656 : Setup.Block := original.get ⟨80, by decide +kernel⟩

column_blocks_part part24656_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24656 stop 24657
noncomputable def destination24656_0 : Setup.Block := part24656_0.get ⟨0, by decide +kernel⟩

noncomputable def target24656 : List Setup.Block := part24656_0

theorem follows24656 : blockTargetsFollow source24656 0 target24656 :=
  And.intro (by
    intro index bounded
    change source24656.get? (0 + index) = destination24656_0.get? index
    have same : source24656 = destination24656_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24656 : (target24656.map Setup.Block.length).sum = source24656.length := by decide +kernel

noncomputable def source24657 : Setup.Block := original.get ⟨81, by decide +kernel⟩

column_blocks_part part24657_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24657 stop 24658
noncomputable def destination24657_0 : Setup.Block := part24657_0.get ⟨0, by decide +kernel⟩

noncomputable def target24657 : List Setup.Block := part24657_0

theorem follows24657 : blockTargetsFollow source24657 0 target24657 :=
  And.intro (by
    intro index bounded
    change source24657.get? (0 + index) = destination24657_0.get? index
    have same : source24657 = destination24657_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24657 : (target24657.map Setup.Block.length).sum = source24657.length := by decide +kernel

noncomputable def source24658 : Setup.Block := original.get ⟨82, by decide +kernel⟩

column_blocks_part part24658_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24658 stop 24659
noncomputable def destination24658_0 : Setup.Block := part24658_0.get ⟨0, by decide +kernel⟩

noncomputable def target24658 : List Setup.Block := part24658_0

theorem follows24658 : blockTargetsFollow source24658 0 target24658 :=
  And.intro (by
    intro index bounded
    change source24658.get? (0 + index) = destination24658_0.get? index
    have same : source24658 = destination24658_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24658 : (target24658.map Setup.Block.length).sum = source24658.length := by decide +kernel

noncomputable def source24659 : Setup.Block := original.get ⟨83, by decide +kernel⟩

column_blocks_part part24659_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24659 stop 24660
noncomputable def destination24659_0 : Setup.Block := part24659_0.get ⟨0, by decide +kernel⟩

noncomputable def target24659 : List Setup.Block := part24659_0

theorem follows24659 : blockTargetsFollow source24659 0 target24659 :=
  And.intro (by
    intro index bounded
    change source24659.get? (0 + index) = destination24659_0.get? index
    have same : source24659 = destination24659_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24659 : (target24659.map Setup.Block.length).sum = source24659.length := by decide +kernel

noncomputable def source24660 : Setup.Block := original.get ⟨84, by decide +kernel⟩

column_blocks_part part24660_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24660 stop 24661
noncomputable def destination24660_0 : Setup.Block := part24660_0.get ⟨0, by decide +kernel⟩

noncomputable def target24660 : List Setup.Block := part24660_0

theorem follows24660 : blockTargetsFollow source24660 0 target24660 :=
  And.intro (by
    intro index bounded
    change source24660.get? (0 + index) = destination24660_0.get? index
    have same : source24660 = destination24660_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24660 : (target24660.map Setup.Block.length).sum = source24660.length := by decide +kernel

noncomputable def source24661 : Setup.Block := original.get ⟨85, by decide +kernel⟩

column_blocks_part part24661_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24661 stop 24662
noncomputable def destination24661_0 : Setup.Block := part24661_0.get ⟨0, by decide +kernel⟩

noncomputable def target24661 : List Setup.Block := part24661_0

theorem follows24661 : blockTargetsFollow source24661 0 target24661 :=
  And.intro (by
    intro index bounded
    change source24661.get? (0 + index) = destination24661_0.get? index
    have same : source24661 = destination24661_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24661 : (target24661.map Setup.Block.length).sum = source24661.length := by decide +kernel

noncomputable def source24662 : Setup.Block := original.get ⟨86, by decide +kernel⟩

column_blocks_part part24662_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24662 stop 24663
noncomputable def destination24662_0 : Setup.Block := part24662_0.get ⟨0, by decide +kernel⟩

noncomputable def target24662 : List Setup.Block := part24662_0

theorem follows24662 : blockTargetsFollow source24662 0 target24662 :=
  And.intro (by
    intro index bounded
    change source24662.get? (0 + index) = destination24662_0.get? index
    have same : source24662 = destination24662_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24662 : (target24662.map Setup.Block.length).sum = source24662.length := by decide +kernel

noncomputable def source24663 : Setup.Block := original.get ⟨87, by decide +kernel⟩

column_blocks_part part24663_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24663 stop 24664
noncomputable def destination24663_0 : Setup.Block := part24663_0.get ⟨0, by decide +kernel⟩

noncomputable def target24663 : List Setup.Block := part24663_0

theorem follows24663 : blockTargetsFollow source24663 0 target24663 :=
  And.intro (by
    intro index bounded
    change source24663.get? (0 + index) = destination24663_0.get? index
    have same : source24663 = destination24663_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24663 : (target24663.map Setup.Block.length).sum = source24663.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
