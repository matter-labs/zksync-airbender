import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column7.Chunk192.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24608 : Setup.Block := original.get ⟨32, by decide +kernel⟩

column_blocks_part part24608_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24608 stop 24609
noncomputable def destination24608_0 : Setup.Block := part24608_0.get ⟨0, by decide +kernel⟩

noncomputable def target24608 : List Setup.Block := part24608_0

theorem follows24608 : blockTargetsFollow source24608 0 target24608 :=
  And.intro (by
    intro index bounded
    change source24608.get? (0 + index) = destination24608_0.get? index
    have same : source24608 = destination24608_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24608 : (target24608.map Setup.Block.length).sum = source24608.length := by decide +kernel

noncomputable def source24609 : Setup.Block := original.get ⟨33, by decide +kernel⟩

column_blocks_part part24609_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24609 stop 24610
noncomputable def destination24609_0 : Setup.Block := part24609_0.get ⟨0, by decide +kernel⟩

noncomputable def target24609 : List Setup.Block := part24609_0

theorem follows24609 : blockTargetsFollow source24609 0 target24609 :=
  And.intro (by
    intro index bounded
    change source24609.get? (0 + index) = destination24609_0.get? index
    have same : source24609 = destination24609_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24609 : (target24609.map Setup.Block.length).sum = source24609.length := by decide +kernel

noncomputable def source24610 : Setup.Block := original.get ⟨34, by decide +kernel⟩

column_blocks_part part24610_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24610 stop 24611
noncomputable def destination24610_0 : Setup.Block := part24610_0.get ⟨0, by decide +kernel⟩

noncomputable def target24610 : List Setup.Block := part24610_0

theorem follows24610 : blockTargetsFollow source24610 0 target24610 :=
  And.intro (by
    intro index bounded
    change source24610.get? (0 + index) = destination24610_0.get? index
    have same : source24610 = destination24610_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24610 : (target24610.map Setup.Block.length).sum = source24610.length := by decide +kernel

noncomputable def source24611 : Setup.Block := original.get ⟨35, by decide +kernel⟩

column_blocks_part part24611_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24611 stop 24612
noncomputable def destination24611_0 : Setup.Block := part24611_0.get ⟨0, by decide +kernel⟩

noncomputable def target24611 : List Setup.Block := part24611_0

theorem follows24611 : blockTargetsFollow source24611 0 target24611 :=
  And.intro (by
    intro index bounded
    change source24611.get? (0 + index) = destination24611_0.get? index
    have same : source24611 = destination24611_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24611 : (target24611.map Setup.Block.length).sum = source24611.length := by decide +kernel

noncomputable def source24612 : Setup.Block := original.get ⟨36, by decide +kernel⟩

column_blocks_part part24612_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24612 stop 24613
noncomputable def destination24612_0 : Setup.Block := part24612_0.get ⟨0, by decide +kernel⟩

noncomputable def target24612 : List Setup.Block := part24612_0

theorem follows24612 : blockTargetsFollow source24612 0 target24612 :=
  And.intro (by
    intro index bounded
    change source24612.get? (0 + index) = destination24612_0.get? index
    have same : source24612 = destination24612_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24612 : (target24612.map Setup.Block.length).sum = source24612.length := by decide +kernel

noncomputable def source24613 : Setup.Block := original.get ⟨37, by decide +kernel⟩

column_blocks_part part24613_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24613 stop 24614
noncomputable def destination24613_0 : Setup.Block := part24613_0.get ⟨0, by decide +kernel⟩

noncomputable def target24613 : List Setup.Block := part24613_0

theorem follows24613 : blockTargetsFollow source24613 0 target24613 :=
  And.intro (by
    intro index bounded
    change source24613.get? (0 + index) = destination24613_0.get? index
    have same : source24613 = destination24613_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24613 : (target24613.map Setup.Block.length).sum = source24613.length := by decide +kernel

noncomputable def source24614 : Setup.Block := original.get ⟨38, by decide +kernel⟩

column_blocks_part part24614_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24614 stop 24615
noncomputable def destination24614_0 : Setup.Block := part24614_0.get ⟨0, by decide +kernel⟩

noncomputable def target24614 : List Setup.Block := part24614_0

theorem follows24614 : blockTargetsFollow source24614 0 target24614 :=
  And.intro (by
    intro index bounded
    change source24614.get? (0 + index) = destination24614_0.get? index
    have same : source24614 = destination24614_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24614 : (target24614.map Setup.Block.length).sum = source24614.length := by decide +kernel

noncomputable def source24615 : Setup.Block := original.get ⟨39, by decide +kernel⟩

column_blocks_part part24615_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24615 stop 24616
noncomputable def destination24615_0 : Setup.Block := part24615_0.get ⟨0, by decide +kernel⟩

noncomputable def target24615 : List Setup.Block := part24615_0

theorem follows24615 : blockTargetsFollow source24615 0 target24615 :=
  And.intro (by
    intro index bounded
    change source24615.get? (0 + index) = destination24615_0.get? index
    have same : source24615 = destination24615_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24615 : (target24615.map Setup.Block.length).sum = source24615.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
