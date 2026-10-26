import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24448 : Setup.Block := original.get ⟨0, by decide +kernel⟩

column_blocks_part part24448_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24448 stop 24449
noncomputable def destination24448_0 : Setup.Block := part24448_0.get ⟨0, by decide +kernel⟩

noncomputable def target24448 : List Setup.Block := part24448_0

theorem follows24448 : blockTargetsFollow source24448 0 target24448 :=
  And.intro (by
    intro index bounded
    change source24448.get? (0 + index) = destination24448_0.get? index
    have same : source24448 = destination24448_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24448 : (target24448.map Setup.Block.length).sum = source24448.length := by decide +kernel

noncomputable def source24449 : Setup.Block := original.get ⟨1, by decide +kernel⟩

column_blocks_part part24449_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24449 stop 24450
noncomputable def destination24449_0 : Setup.Block := part24449_0.get ⟨0, by decide +kernel⟩

noncomputable def target24449 : List Setup.Block := part24449_0

theorem follows24449 : blockTargetsFollow source24449 0 target24449 :=
  And.intro (by
    intro index bounded
    change source24449.get? (0 + index) = destination24449_0.get? index
    have same : source24449 = destination24449_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24449 : (target24449.map Setup.Block.length).sum = source24449.length := by decide +kernel

noncomputable def source24450 : Setup.Block := original.get ⟨2, by decide +kernel⟩

column_blocks_part part24450_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24450 stop 24451
noncomputable def destination24450_0 : Setup.Block := part24450_0.get ⟨0, by decide +kernel⟩

noncomputable def target24450 : List Setup.Block := part24450_0

theorem follows24450 : blockTargetsFollow source24450 0 target24450 :=
  And.intro (by
    intro index bounded
    change source24450.get? (0 + index) = destination24450_0.get? index
    have same : source24450 = destination24450_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24450 : (target24450.map Setup.Block.length).sum = source24450.length := by decide +kernel

noncomputable def source24451 : Setup.Block := original.get ⟨3, by decide +kernel⟩

column_blocks_part part24451_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24451 stop 24452
noncomputable def destination24451_0 : Setup.Block := part24451_0.get ⟨0, by decide +kernel⟩

noncomputable def target24451 : List Setup.Block := part24451_0

theorem follows24451 : blockTargetsFollow source24451 0 target24451 :=
  And.intro (by
    intro index bounded
    change source24451.get? (0 + index) = destination24451_0.get? index
    have same : source24451 = destination24451_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24451 : (target24451.map Setup.Block.length).sum = source24451.length := by decide +kernel

noncomputable def source24452 : Setup.Block := original.get ⟨4, by decide +kernel⟩

column_blocks_part part24452_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24452 stop 24453
noncomputable def destination24452_0 : Setup.Block := part24452_0.get ⟨0, by decide +kernel⟩

noncomputable def target24452 : List Setup.Block := part24452_0

theorem follows24452 : blockTargetsFollow source24452 0 target24452 :=
  And.intro (by
    intro index bounded
    change source24452.get? (0 + index) = destination24452_0.get? index
    have same : source24452 = destination24452_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24452 : (target24452.map Setup.Block.length).sum = source24452.length := by decide +kernel

noncomputable def source24453 : Setup.Block := original.get ⟨5, by decide +kernel⟩

column_blocks_part part24453_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24453 stop 24454
noncomputable def destination24453_0 : Setup.Block := part24453_0.get ⟨0, by decide +kernel⟩

noncomputable def target24453 : List Setup.Block := part24453_0

theorem follows24453 : blockTargetsFollow source24453 0 target24453 :=
  And.intro (by
    intro index bounded
    change source24453.get? (0 + index) = destination24453_0.get? index
    have same : source24453 = destination24453_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24453 : (target24453.map Setup.Block.length).sum = source24453.length := by decide +kernel

noncomputable def source24454 : Setup.Block := original.get ⟨6, by decide +kernel⟩

column_blocks_part part24454_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24454 stop 24455
noncomputable def destination24454_0 : Setup.Block := part24454_0.get ⟨0, by decide +kernel⟩

noncomputable def target24454 : List Setup.Block := part24454_0

theorem follows24454 : blockTargetsFollow source24454 0 target24454 :=
  And.intro (by
    intro index bounded
    change source24454.get? (0 + index) = destination24454_0.get? index
    have same : source24454 = destination24454_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24454 : (target24454.map Setup.Block.length).sum = source24454.length := by decide +kernel

noncomputable def source24455 : Setup.Block := original.get ⟨7, by decide +kernel⟩

column_blocks_part part24455_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24455 stop 24456
noncomputable def destination24455_0 : Setup.Block := part24455_0.get ⟨0, by decide +kernel⟩

noncomputable def target24455 : List Setup.Block := part24455_0

theorem follows24455 : blockTargetsFollow source24455 0 target24455 :=
  And.intro (by
    intro index bounded
    change source24455.get? (0 + index) = destination24455_0.get? index
    have same : source24455 = destination24455_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24455 : (target24455.map Setup.Block.length).sum = source24455.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
