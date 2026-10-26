import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk190.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24336 : Setup.Block := original.get ⟨16, by decide +kernel⟩

column_blocks_part part24336_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24336 stop 24337
noncomputable def destination24336_0 : Setup.Block := part24336_0.get ⟨0, by decide +kernel⟩

noncomputable def target24336 : List Setup.Block := part24336_0

theorem follows24336 : blockTargetsFollow source24336 0 target24336 :=
  And.intro (by
    intro index bounded
    change source24336.get? (0 + index) = destination24336_0.get? index
    have same : source24336 = destination24336_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24336 : (target24336.map Setup.Block.length).sum = source24336.length := by decide +kernel

noncomputable def source24337 : Setup.Block := original.get ⟨17, by decide +kernel⟩

column_blocks_part part24337_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24337 stop 24338
noncomputable def destination24337_0 : Setup.Block := part24337_0.get ⟨0, by decide +kernel⟩

noncomputable def target24337 : List Setup.Block := part24337_0

theorem follows24337 : blockTargetsFollow source24337 0 target24337 :=
  And.intro (by
    intro index bounded
    change source24337.get? (0 + index) = destination24337_0.get? index
    have same : source24337 = destination24337_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24337 : (target24337.map Setup.Block.length).sum = source24337.length := by decide +kernel

noncomputable def source24338 : Setup.Block := original.get ⟨18, by decide +kernel⟩

column_blocks_part part24338_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24338 stop 24339
noncomputable def destination24338_0 : Setup.Block := part24338_0.get ⟨0, by decide +kernel⟩

noncomputable def target24338 : List Setup.Block := part24338_0

theorem follows24338 : blockTargetsFollow source24338 0 target24338 :=
  And.intro (by
    intro index bounded
    change source24338.get? (0 + index) = destination24338_0.get? index
    have same : source24338 = destination24338_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24338 : (target24338.map Setup.Block.length).sum = source24338.length := by decide +kernel

noncomputable def source24339 : Setup.Block := original.get ⟨19, by decide +kernel⟩

column_blocks_part part24339_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24339 stop 24340
noncomputable def destination24339_0 : Setup.Block := part24339_0.get ⟨0, by decide +kernel⟩

noncomputable def target24339 : List Setup.Block := part24339_0

theorem follows24339 : blockTargetsFollow source24339 0 target24339 :=
  And.intro (by
    intro index bounded
    change source24339.get? (0 + index) = destination24339_0.get? index
    have same : source24339 = destination24339_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24339 : (target24339.map Setup.Block.length).sum = source24339.length := by decide +kernel

noncomputable def source24340 : Setup.Block := original.get ⟨20, by decide +kernel⟩

column_blocks_part part24340_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24340 stop 24341
noncomputable def destination24340_0 : Setup.Block := part24340_0.get ⟨0, by decide +kernel⟩

noncomputable def target24340 : List Setup.Block := part24340_0

theorem follows24340 : blockTargetsFollow source24340 0 target24340 :=
  And.intro (by
    intro index bounded
    change source24340.get? (0 + index) = destination24340_0.get? index
    have same : source24340 = destination24340_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24340 : (target24340.map Setup.Block.length).sum = source24340.length := by decide +kernel

noncomputable def source24341 : Setup.Block := original.get ⟨21, by decide +kernel⟩

column_blocks_part part24341_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24341 stop 24342
noncomputable def destination24341_0 : Setup.Block := part24341_0.get ⟨0, by decide +kernel⟩

noncomputable def target24341 : List Setup.Block := part24341_0

theorem follows24341 : blockTargetsFollow source24341 0 target24341 :=
  And.intro (by
    intro index bounded
    change source24341.get? (0 + index) = destination24341_0.get? index
    have same : source24341 = destination24341_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24341 : (target24341.map Setup.Block.length).sum = source24341.length := by decide +kernel

noncomputable def source24342 : Setup.Block := original.get ⟨22, by decide +kernel⟩

column_blocks_part part24342_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24342 stop 24343
noncomputable def destination24342_0 : Setup.Block := part24342_0.get ⟨0, by decide +kernel⟩

noncomputable def target24342 : List Setup.Block := part24342_0

theorem follows24342 : blockTargetsFollow source24342 0 target24342 :=
  And.intro (by
    intro index bounded
    change source24342.get? (0 + index) = destination24342_0.get? index
    have same : source24342 = destination24342_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24342 : (target24342.map Setup.Block.length).sum = source24342.length := by decide +kernel

noncomputable def source24343 : Setup.Block := original.get ⟨23, by decide +kernel⟩

column_blocks_part part24343_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24343 stop 24344
noncomputable def destination24343_0 : Setup.Block := part24343_0.get ⟨0, by decide +kernel⟩

noncomputable def target24343 : List Setup.Block := part24343_0

theorem follows24343 : blockTargetsFollow source24343 0 target24343 :=
  And.intro (by
    intro index bounded
    change source24343.get? (0 + index) = destination24343_0.get? index
    have same : source24343 = destination24343_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24343 : (target24343.map Setup.Block.length).sum = source24343.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
