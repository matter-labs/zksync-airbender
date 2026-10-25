import GKRProtocol.UnifiedSpecialParts.Column4.Chunk199.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk199
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source25512 : Setup.Block := original.get ⟨40, by decide +kernel⟩

column_blocks_part part25512_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 199 stop 200
noncomputable def destination25512_0 : Setup.Block := part25512_0.get ⟨0, by decide +kernel⟩

noncomputable def target25512 : List Setup.Block := part25512_0

theorem follows25512 : blockTargetsFollow source25512 0 target25512 :=
  And.intro (by
    intro index bounded
    change source25512.get? (0 + index) = destination25512_0.get? index
    have same : source25512 = destination25512_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25512 : (target25512.map Setup.Block.length).sum = source25512.length := by decide +kernel

noncomputable def source25513 : Setup.Block := original.get ⟨41, by decide +kernel⟩

column_blocks_part part25513_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 200 stop 201
noncomputable def destination25513_0 : Setup.Block := part25513_0.get ⟨0, by decide +kernel⟩

noncomputable def target25513 : List Setup.Block := part25513_0

theorem follows25513 : blockTargetsFollow source25513 0 target25513 :=
  And.intro (by
    intro index bounded
    change source25513.get? (0 + index) = destination25513_0.get? index
    have same : source25513 = destination25513_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25513 : (target25513.map Setup.Block.length).sum = source25513.length := by decide +kernel

noncomputable def source25514 : Setup.Block := original.get ⟨42, by decide +kernel⟩

column_blocks_part part25514_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 201 stop 202
noncomputable def destination25514_0 : Setup.Block := part25514_0.get ⟨0, by decide +kernel⟩

noncomputable def target25514 : List Setup.Block := part25514_0

theorem follows25514 : blockTargetsFollow source25514 0 target25514 :=
  And.intro (by
    intro index bounded
    change source25514.get? (0 + index) = destination25514_0.get? index
    have same : source25514 = destination25514_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25514 : (target25514.map Setup.Block.length).sum = source25514.length := by decide +kernel

noncomputable def source25515 : Setup.Block := original.get ⟨43, by decide +kernel⟩

column_blocks_part part25515_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 202 stop 203
noncomputable def destination25515_0 : Setup.Block := part25515_0.get ⟨0, by decide +kernel⟩

noncomputable def target25515 : List Setup.Block := part25515_0

theorem follows25515 : blockTargetsFollow source25515 0 target25515 :=
  And.intro (by
    intro index bounded
    change source25515.get? (0 + index) = destination25515_0.get? index
    have same : source25515 = destination25515_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25515 : (target25515.map Setup.Block.length).sum = source25515.length := by decide +kernel

noncomputable def source25516 : Setup.Block := original.get ⟨44, by decide +kernel⟩

column_blocks_part part25516_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 203 stop 204
noncomputable def destination25516_0 : Setup.Block := part25516_0.get ⟨0, by decide +kernel⟩

noncomputable def target25516 : List Setup.Block := part25516_0

theorem follows25516 : blockTargetsFollow source25516 0 target25516 :=
  And.intro (by
    intro index bounded
    change source25516.get? (0 + index) = destination25516_0.get? index
    have same : source25516 = destination25516_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25516 : (target25516.map Setup.Block.length).sum = source25516.length := by decide +kernel

noncomputable def source25517 : Setup.Block := original.get ⟨45, by decide +kernel⟩

column_blocks_part part25517_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 204 stop 205
noncomputable def destination25517_0 : Setup.Block := part25517_0.get ⟨0, by decide +kernel⟩

noncomputable def target25517 : List Setup.Block := part25517_0

theorem follows25517 : blockTargetsFollow source25517 0 target25517 :=
  And.intro (by
    intro index bounded
    change source25517.get? (0 + index) = destination25517_0.get? index
    have same : source25517 = destination25517_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25517 : (target25517.map Setup.Block.length).sum = source25517.length := by decide +kernel

noncomputable def source25518 : Setup.Block := original.get ⟨46, by decide +kernel⟩

column_blocks_part part25518_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 205 stop 206
noncomputable def destination25518_0 : Setup.Block := part25518_0.get ⟨0, by decide +kernel⟩

noncomputable def target25518 : List Setup.Block := part25518_0

theorem follows25518 : blockTargetsFollow source25518 0 target25518 :=
  And.intro (by
    intro index bounded
    change source25518.get? (0 + index) = destination25518_0.get? index
    have same : source25518 = destination25518_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25518 : (target25518.map Setup.Block.length).sum = source25518.length := by decide +kernel

noncomputable def source25519 : Setup.Block := original.get ⟨47, by decide +kernel⟩

column_blocks_part part25519_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 206 stop 207
noncomputable def destination25519_0 : Setup.Block := part25519_0.get ⟨0, by decide +kernel⟩

noncomputable def target25519 : List Setup.Block := part25519_0

theorem follows25519 : blockTargetsFollow source25519 0 target25519 :=
  And.intro (by
    intro index bounded
    change source25519.get? (0 + index) = destination25519_0.get? index
    have same : source25519 = destination25519_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25519 : (target25519.map Setup.Block.length).sum = source25519.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk199
