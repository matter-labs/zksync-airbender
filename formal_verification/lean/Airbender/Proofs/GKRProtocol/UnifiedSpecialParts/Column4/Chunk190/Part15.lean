import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk190.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24440 : Setup.Block := original.get ⟨120, by decide +kernel⟩

column_blocks_part part24440_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 26 stop 27
noncomputable def destination24440_0 : Setup.Block := part24440_0.get ⟨0, by decide +kernel⟩

noncomputable def target24440 : List Setup.Block := part24440_0

theorem follows24440 : blockTargetsFollow source24440 0 target24440 :=
  And.intro (by
    intro index bounded
    change source24440.get? (0 + index) = destination24440_0.get? index
    have same : source24440 = destination24440_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24440 : (target24440.map Setup.Block.length).sum = source24440.length := by decide +kernel

noncomputable def source24441 : Setup.Block := original.get ⟨121, by decide +kernel⟩

column_blocks_part part24441_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 27 stop 28
noncomputable def destination24441_0 : Setup.Block := part24441_0.get ⟨0, by decide +kernel⟩

noncomputable def target24441 : List Setup.Block := part24441_0

theorem follows24441 : blockTargetsFollow source24441 0 target24441 :=
  And.intro (by
    intro index bounded
    change source24441.get? (0 + index) = destination24441_0.get? index
    have same : source24441 = destination24441_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24441 : (target24441.map Setup.Block.length).sum = source24441.length := by decide +kernel

noncomputable def source24442 : Setup.Block := original.get ⟨122, by decide +kernel⟩

column_blocks_part part24442_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 28 stop 29
noncomputable def destination24442_0 : Setup.Block := part24442_0.get ⟨0, by decide +kernel⟩

noncomputable def target24442 : List Setup.Block := part24442_0

theorem follows24442 : blockTargetsFollow source24442 0 target24442 :=
  And.intro (by
    intro index bounded
    change source24442.get? (0 + index) = destination24442_0.get? index
    have same : source24442 = destination24442_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24442 : (target24442.map Setup.Block.length).sum = source24442.length := by decide +kernel

noncomputable def source24443 : Setup.Block := original.get ⟨123, by decide +kernel⟩

column_blocks_part part24443_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 29 stop 30
noncomputable def destination24443_0 : Setup.Block := part24443_0.get ⟨0, by decide +kernel⟩

noncomputable def target24443 : List Setup.Block := part24443_0

theorem follows24443 : blockTargetsFollow source24443 0 target24443 :=
  And.intro (by
    intro index bounded
    change source24443.get? (0 + index) = destination24443_0.get? index
    have same : source24443 = destination24443_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24443 : (target24443.map Setup.Block.length).sum = source24443.length := by decide +kernel

noncomputable def source24444 : Setup.Block := original.get ⟨124, by decide +kernel⟩

column_blocks_part part24444_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 30 stop 31
noncomputable def destination24444_0 : Setup.Block := part24444_0.get ⟨0, by decide +kernel⟩

noncomputable def target24444 : List Setup.Block := part24444_0

theorem follows24444 : blockTargetsFollow source24444 0 target24444 :=
  And.intro (by
    intro index bounded
    change source24444.get? (0 + index) = destination24444_0.get? index
    have same : source24444 = destination24444_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24444 : (target24444.map Setup.Block.length).sum = source24444.length := by decide +kernel

noncomputable def source24445 : Setup.Block := original.get ⟨125, by decide +kernel⟩

column_blocks_part part24445_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 31 stop 32
noncomputable def destination24445_0 : Setup.Block := part24445_0.get ⟨0, by decide +kernel⟩

noncomputable def target24445 : List Setup.Block := part24445_0

theorem follows24445 : blockTargetsFollow source24445 0 target24445 :=
  And.intro (by
    intro index bounded
    change source24445.get? (0 + index) = destination24445_0.get? index
    have same : source24445 = destination24445_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24445 : (target24445.map Setup.Block.length).sum = source24445.length := by decide +kernel

noncomputable def source24446 : Setup.Block := original.get ⟨126, by decide +kernel⟩

column_blocks_part part24446_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 32 stop 33
noncomputable def destination24446_0 : Setup.Block := part24446_0.get ⟨0, by decide +kernel⟩

noncomputable def target24446 : List Setup.Block := part24446_0

theorem follows24446 : blockTargetsFollow source24446 0 target24446 :=
  And.intro (by
    intro index bounded
    change source24446.get? (0 + index) = destination24446_0.get? index
    have same : source24446 = destination24446_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24446 : (target24446.map Setup.Block.length).sum = source24446.length := by decide +kernel

noncomputable def source24447 : Setup.Block := original.get ⟨127, by decide +kernel⟩

column_blocks_part part24447_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 33 stop 34
noncomputable def destination24447_0 : Setup.Block := part24447_0.get ⟨0, by decide +kernel⟩

noncomputable def target24447 : List Setup.Block := part24447_0

theorem follows24447 : blockTargetsFollow source24447 0 target24447 :=
  And.intro (by
    intro index bounded
    change source24447.get? (0 + index) = destination24447_0.get? index
    have same : source24447 = destination24447_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24447 : (target24447.map Setup.Block.length).sum = source24447.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
