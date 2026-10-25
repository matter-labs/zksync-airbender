import GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24544 : Setup.Block := original.get ⟨96, by decide +kernel⟩

column_blocks_part part24544_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 2 stop 3
noncomputable def destination24544_0 : Setup.Block := part24544_0.get ⟨0, by decide +kernel⟩

noncomputable def target24544 : List Setup.Block := part24544_0

theorem follows24544 : blockTargetsFollow source24544 0 target24544 :=
  And.intro (by
    intro index bounded
    change source24544.get? (0 + index) = destination24544_0.get? index
    have same : source24544 = destination24544_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24544 : (target24544.map Setup.Block.length).sum = source24544.length := by decide +kernel

noncomputable def source24545 : Setup.Block := original.get ⟨97, by decide +kernel⟩

column_blocks_part part24545_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 3 stop 4
noncomputable def destination24545_0 : Setup.Block := part24545_0.get ⟨0, by decide +kernel⟩

noncomputable def target24545 : List Setup.Block := part24545_0

theorem follows24545 : blockTargetsFollow source24545 0 target24545 :=
  And.intro (by
    intro index bounded
    change source24545.get? (0 + index) = destination24545_0.get? index
    have same : source24545 = destination24545_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24545 : (target24545.map Setup.Block.length).sum = source24545.length := by decide +kernel

noncomputable def source24546 : Setup.Block := original.get ⟨98, by decide +kernel⟩

column_blocks_part part24546_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 4 stop 5
noncomputable def destination24546_0 : Setup.Block := part24546_0.get ⟨0, by decide +kernel⟩

noncomputable def target24546 : List Setup.Block := part24546_0

theorem follows24546 : blockTargetsFollow source24546 0 target24546 :=
  And.intro (by
    intro index bounded
    change source24546.get? (0 + index) = destination24546_0.get? index
    have same : source24546 = destination24546_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24546 : (target24546.map Setup.Block.length).sum = source24546.length := by decide +kernel

noncomputable def source24547 : Setup.Block := original.get ⟨99, by decide +kernel⟩

column_blocks_part part24547_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 5 stop 6
noncomputable def destination24547_0 : Setup.Block := part24547_0.get ⟨0, by decide +kernel⟩

noncomputable def target24547 : List Setup.Block := part24547_0

theorem follows24547 : blockTargetsFollow source24547 0 target24547 :=
  And.intro (by
    intro index bounded
    change source24547.get? (0 + index) = destination24547_0.get? index
    have same : source24547 = destination24547_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24547 : (target24547.map Setup.Block.length).sum = source24547.length := by decide +kernel

noncomputable def source24548 : Setup.Block := original.get ⟨100, by decide +kernel⟩

column_blocks_part part24548_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 6 stop 7
noncomputable def destination24548_0 : Setup.Block := part24548_0.get ⟨0, by decide +kernel⟩

noncomputable def target24548 : List Setup.Block := part24548_0

theorem follows24548 : blockTargetsFollow source24548 0 target24548 :=
  And.intro (by
    intro index bounded
    change source24548.get? (0 + index) = destination24548_0.get? index
    have same : source24548 = destination24548_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24548 : (target24548.map Setup.Block.length).sum = source24548.length := by decide +kernel

noncomputable def source24549 : Setup.Block := original.get ⟨101, by decide +kernel⟩

column_blocks_part part24549_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 7 stop 8
noncomputable def destination24549_0 : Setup.Block := part24549_0.get ⟨0, by decide +kernel⟩

noncomputable def target24549 : List Setup.Block := part24549_0

theorem follows24549 : blockTargetsFollow source24549 0 target24549 :=
  And.intro (by
    intro index bounded
    change source24549.get? (0 + index) = destination24549_0.get? index
    have same : source24549 = destination24549_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24549 : (target24549.map Setup.Block.length).sum = source24549.length := by decide +kernel

noncomputable def source24550 : Setup.Block := original.get ⟨102, by decide +kernel⟩

column_blocks_part part24550_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 8 stop 9
noncomputable def destination24550_0 : Setup.Block := part24550_0.get ⟨0, by decide +kernel⟩

noncomputable def target24550 : List Setup.Block := part24550_0

theorem follows24550 : blockTargetsFollow source24550 0 target24550 :=
  And.intro (by
    intro index bounded
    change source24550.get? (0 + index) = destination24550_0.get? index
    have same : source24550 = destination24550_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24550 : (target24550.map Setup.Block.length).sum = source24550.length := by decide +kernel

noncomputable def source24551 : Setup.Block := original.get ⟨103, by decide +kernel⟩

column_blocks_part part24551_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 9 stop 10
noncomputable def destination24551_0 : Setup.Block := part24551_0.get ⟨0, by decide +kernel⟩

noncomputable def target24551 : List Setup.Block := part24551_0

theorem follows24551 : blockTargetsFollow source24551 0 target24551 :=
  And.intro (by
    intro index bounded
    change source24551.get? (0 + index) = destination24551_0.get? index
    have same : source24551 = destination24551_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24551 : (target24551.map Setup.Block.length).sum = source24551.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
