import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk190.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24400 : Setup.Block := original.get ⟨80, by decide +kernel⟩

column_blocks_part part24400_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24400 stop 24401
noncomputable def destination24400_0 : Setup.Block := part24400_0.get ⟨0, by decide +kernel⟩

noncomputable def target24400 : List Setup.Block := part24400_0

theorem follows24400 : blockTargetsFollow source24400 0 target24400 :=
  And.intro (by
    intro index bounded
    change source24400.get? (0 + index) = destination24400_0.get? index
    have same : source24400 = destination24400_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24400 : (target24400.map Setup.Block.length).sum = source24400.length := by decide +kernel

noncomputable def source24401 : Setup.Block := original.get ⟨81, by decide +kernel⟩

column_blocks_part part24401_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24401 stop 24402
noncomputable def destination24401_0 : Setup.Block := part24401_0.get ⟨0, by decide +kernel⟩

noncomputable def target24401 : List Setup.Block := part24401_0

theorem follows24401 : blockTargetsFollow source24401 0 target24401 :=
  And.intro (by
    intro index bounded
    change source24401.get? (0 + index) = destination24401_0.get? index
    have same : source24401 = destination24401_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24401 : (target24401.map Setup.Block.length).sum = source24401.length := by decide +kernel

noncomputable def source24402 : Setup.Block := original.get ⟨82, by decide +kernel⟩

column_blocks_part part24402_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24402 stop 24403
noncomputable def destination24402_0 : Setup.Block := part24402_0.get ⟨0, by decide +kernel⟩

noncomputable def target24402 : List Setup.Block := part24402_0

theorem follows24402 : blockTargetsFollow source24402 0 target24402 :=
  And.intro (by
    intro index bounded
    change source24402.get? (0 + index) = destination24402_0.get? index
    have same : source24402 = destination24402_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24402 : (target24402.map Setup.Block.length).sum = source24402.length := by decide +kernel

noncomputable def source24403 : Setup.Block := original.get ⟨83, by decide +kernel⟩

column_blocks_part part24403_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24403 stop 24404
noncomputable def destination24403_0 : Setup.Block := part24403_0.get ⟨0, by decide +kernel⟩

noncomputable def target24403 : List Setup.Block := part24403_0

theorem follows24403 : blockTargetsFollow source24403 0 target24403 :=
  And.intro (by
    intro index bounded
    change source24403.get? (0 + index) = destination24403_0.get? index
    have same : source24403 = destination24403_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24403 : (target24403.map Setup.Block.length).sum = source24403.length := by decide +kernel

noncomputable def source24404 : Setup.Block := original.get ⟨84, by decide +kernel⟩

column_blocks_part part24404_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24404 stop 24405
noncomputable def destination24404_0 : Setup.Block := part24404_0.get ⟨0, by decide +kernel⟩

noncomputable def target24404 : List Setup.Block := part24404_0

theorem follows24404 : blockTargetsFollow source24404 0 target24404 :=
  And.intro (by
    intro index bounded
    change source24404.get? (0 + index) = destination24404_0.get? index
    have same : source24404 = destination24404_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24404 : (target24404.map Setup.Block.length).sum = source24404.length := by decide +kernel

noncomputable def source24405 : Setup.Block := original.get ⟨85, by decide +kernel⟩

column_blocks_part part24405_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24405 stop 24406
noncomputable def destination24405_0 : Setup.Block := part24405_0.get ⟨0, by decide +kernel⟩

noncomputable def target24405 : List Setup.Block := part24405_0

theorem follows24405 : blockTargetsFollow source24405 0 target24405 :=
  And.intro (by
    intro index bounded
    change source24405.get? (0 + index) = destination24405_0.get? index
    have same : source24405 = destination24405_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24405 : (target24405.map Setup.Block.length).sum = source24405.length := by decide +kernel

noncomputable def source24406 : Setup.Block := original.get ⟨86, by decide +kernel⟩

column_blocks_part part24406_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24406 stop 24407
noncomputable def destination24406_0 : Setup.Block := part24406_0.get ⟨0, by decide +kernel⟩

noncomputable def target24406 : List Setup.Block := part24406_0

theorem follows24406 : blockTargetsFollow source24406 0 target24406 :=
  And.intro (by
    intro index bounded
    change source24406.get? (0 + index) = destination24406_0.get? index
    have same : source24406 = destination24406_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24406 : (target24406.map Setup.Block.length).sum = source24406.length := by decide +kernel

noncomputable def source24407 : Setup.Block := original.get ⟨87, by decide +kernel⟩

column_blocks_part part24407_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24407 stop 24408
noncomputable def destination24407_0 : Setup.Block := part24407_0.get ⟨0, by decide +kernel⟩

noncomputable def target24407 : List Setup.Block := part24407_0

theorem follows24407 : blockTargetsFollow source24407 0 target24407 :=
  And.intro (by
    intro index bounded
    change source24407.get? (0 + index) = destination24407_0.get? index
    have same : source24407 = destination24407_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24407 : (target24407.map Setup.Block.length).sum = source24407.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
