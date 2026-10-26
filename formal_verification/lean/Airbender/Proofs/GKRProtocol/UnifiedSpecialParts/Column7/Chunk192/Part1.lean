import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column7.Chunk192.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24584 : Setup.Block := original.get ⟨8, by decide +kernel⟩

column_blocks_part part24584_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24584 stop 24585
noncomputable def destination24584_0 : Setup.Block := part24584_0.get ⟨0, by decide +kernel⟩

noncomputable def target24584 : List Setup.Block := part24584_0

theorem follows24584 : blockTargetsFollow source24584 0 target24584 :=
  And.intro (by
    intro index bounded
    change source24584.get? (0 + index) = destination24584_0.get? index
    have same : source24584 = destination24584_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24584 : (target24584.map Setup.Block.length).sum = source24584.length := by decide +kernel

noncomputable def source24585 : Setup.Block := original.get ⟨9, by decide +kernel⟩

column_blocks_part part24585_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24585 stop 24586
noncomputable def destination24585_0 : Setup.Block := part24585_0.get ⟨0, by decide +kernel⟩

noncomputable def target24585 : List Setup.Block := part24585_0

theorem follows24585 : blockTargetsFollow source24585 0 target24585 :=
  And.intro (by
    intro index bounded
    change source24585.get? (0 + index) = destination24585_0.get? index
    have same : source24585 = destination24585_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24585 : (target24585.map Setup.Block.length).sum = source24585.length := by decide +kernel

noncomputable def source24586 : Setup.Block := original.get ⟨10, by decide +kernel⟩

column_blocks_part part24586_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24586 stop 24587
noncomputable def destination24586_0 : Setup.Block := part24586_0.get ⟨0, by decide +kernel⟩

noncomputable def target24586 : List Setup.Block := part24586_0

theorem follows24586 : blockTargetsFollow source24586 0 target24586 :=
  And.intro (by
    intro index bounded
    change source24586.get? (0 + index) = destination24586_0.get? index
    have same : source24586 = destination24586_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24586 : (target24586.map Setup.Block.length).sum = source24586.length := by decide +kernel

noncomputable def source24587 : Setup.Block := original.get ⟨11, by decide +kernel⟩

column_blocks_part part24587_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24587 stop 24588
noncomputable def destination24587_0 : Setup.Block := part24587_0.get ⟨0, by decide +kernel⟩

noncomputable def target24587 : List Setup.Block := part24587_0

theorem follows24587 : blockTargetsFollow source24587 0 target24587 :=
  And.intro (by
    intro index bounded
    change source24587.get? (0 + index) = destination24587_0.get? index
    have same : source24587 = destination24587_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24587 : (target24587.map Setup.Block.length).sum = source24587.length := by decide +kernel

noncomputable def source24588 : Setup.Block := original.get ⟨12, by decide +kernel⟩

column_blocks_part part24588_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24588 stop 24589
noncomputable def destination24588_0 : Setup.Block := part24588_0.get ⟨0, by decide +kernel⟩

noncomputable def target24588 : List Setup.Block := part24588_0

theorem follows24588 : blockTargetsFollow source24588 0 target24588 :=
  And.intro (by
    intro index bounded
    change source24588.get? (0 + index) = destination24588_0.get? index
    have same : source24588 = destination24588_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24588 : (target24588.map Setup.Block.length).sum = source24588.length := by decide +kernel

noncomputable def source24589 : Setup.Block := original.get ⟨13, by decide +kernel⟩

column_blocks_part part24589_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24589 stop 24590
noncomputable def destination24589_0 : Setup.Block := part24589_0.get ⟨0, by decide +kernel⟩

noncomputable def target24589 : List Setup.Block := part24589_0

theorem follows24589 : blockTargetsFollow source24589 0 target24589 :=
  And.intro (by
    intro index bounded
    change source24589.get? (0 + index) = destination24589_0.get? index
    have same : source24589 = destination24589_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24589 : (target24589.map Setup.Block.length).sum = source24589.length := by decide +kernel

noncomputable def source24590 : Setup.Block := original.get ⟨14, by decide +kernel⟩

column_blocks_part part24590_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24590 stop 24591
noncomputable def destination24590_0 : Setup.Block := part24590_0.get ⟨0, by decide +kernel⟩

noncomputable def target24590 : List Setup.Block := part24590_0

theorem follows24590 : blockTargetsFollow source24590 0 target24590 :=
  And.intro (by
    intro index bounded
    change source24590.get? (0 + index) = destination24590_0.get? index
    have same : source24590 = destination24590_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24590 : (target24590.map Setup.Block.length).sum = source24590.length := by decide +kernel

noncomputable def source24591 : Setup.Block := original.get ⟨15, by decide +kernel⟩

column_blocks_part part24591_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24591 stop 24592
noncomputable def destination24591_0 : Setup.Block := part24591_0.get ⟨0, by decide +kernel⟩

noncomputable def target24591 : List Setup.Block := part24591_0

theorem follows24591 : blockTargetsFollow source24591 0 target24591 :=
  And.intro (by
    intro index bounded
    change source24591.get? (0 + index) = destination24591_0.get? index
    have same : source24591 = destination24591_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24591 : (target24591.map Setup.Block.length).sum = source24591.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
