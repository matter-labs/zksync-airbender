import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk199.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk199
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source25472 : Setup.Block := original.get ⟨0, by decide +kernel⟩

column_blocks_part part25472_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 159 stop 160
noncomputable def destination25472_0 : Setup.Block := part25472_0.get ⟨0, by decide +kernel⟩

noncomputable def target25472 : List Setup.Block := part25472_0

theorem follows25472 : blockTargetsFollow source25472 0 target25472 :=
  And.intro (by
    intro index bounded
    change source25472.get? (0 + index) = destination25472_0.get? index
    have same : source25472 = destination25472_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25472 : (target25472.map Setup.Block.length).sum = source25472.length := by decide +kernel

noncomputable def source25473 : Setup.Block := original.get ⟨1, by decide +kernel⟩

column_blocks_part part25473_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 160 stop 161
noncomputable def destination25473_0 : Setup.Block := part25473_0.get ⟨0, by decide +kernel⟩

noncomputable def target25473 : List Setup.Block := part25473_0

theorem follows25473 : blockTargetsFollow source25473 0 target25473 :=
  And.intro (by
    intro index bounded
    change source25473.get? (0 + index) = destination25473_0.get? index
    have same : source25473 = destination25473_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25473 : (target25473.map Setup.Block.length).sum = source25473.length := by decide +kernel

noncomputable def source25474 : Setup.Block := original.get ⟨2, by decide +kernel⟩

column_blocks_part part25474_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 161 stop 162
noncomputable def destination25474_0 : Setup.Block := part25474_0.get ⟨0, by decide +kernel⟩

noncomputable def target25474 : List Setup.Block := part25474_0

theorem follows25474 : blockTargetsFollow source25474 0 target25474 :=
  And.intro (by
    intro index bounded
    change source25474.get? (0 + index) = destination25474_0.get? index
    have same : source25474 = destination25474_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25474 : (target25474.map Setup.Block.length).sum = source25474.length := by decide +kernel

noncomputable def source25475 : Setup.Block := original.get ⟨3, by decide +kernel⟩

column_blocks_part part25475_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 162 stop 163
noncomputable def destination25475_0 : Setup.Block := part25475_0.get ⟨0, by decide +kernel⟩

noncomputable def target25475 : List Setup.Block := part25475_0

theorem follows25475 : blockTargetsFollow source25475 0 target25475 :=
  And.intro (by
    intro index bounded
    change source25475.get? (0 + index) = destination25475_0.get? index
    have same : source25475 = destination25475_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25475 : (target25475.map Setup.Block.length).sum = source25475.length := by decide +kernel

noncomputable def source25476 : Setup.Block := original.get ⟨4, by decide +kernel⟩

column_blocks_part part25476_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 163 stop 164
noncomputable def destination25476_0 : Setup.Block := part25476_0.get ⟨0, by decide +kernel⟩

noncomputable def target25476 : List Setup.Block := part25476_0

theorem follows25476 : blockTargetsFollow source25476 0 target25476 :=
  And.intro (by
    intro index bounded
    change source25476.get? (0 + index) = destination25476_0.get? index
    have same : source25476 = destination25476_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25476 : (target25476.map Setup.Block.length).sum = source25476.length := by decide +kernel

noncomputable def source25477 : Setup.Block := original.get ⟨5, by decide +kernel⟩

column_blocks_part part25477_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 164 stop 165
noncomputable def destination25477_0 : Setup.Block := part25477_0.get ⟨0, by decide +kernel⟩

noncomputable def target25477 : List Setup.Block := part25477_0

theorem follows25477 : blockTargetsFollow source25477 0 target25477 :=
  And.intro (by
    intro index bounded
    change source25477.get? (0 + index) = destination25477_0.get? index
    have same : source25477 = destination25477_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25477 : (target25477.map Setup.Block.length).sum = source25477.length := by decide +kernel

noncomputable def source25478 : Setup.Block := original.get ⟨6, by decide +kernel⟩

column_blocks_part part25478_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 165 stop 166
noncomputable def destination25478_0 : Setup.Block := part25478_0.get ⟨0, by decide +kernel⟩

noncomputable def target25478 : List Setup.Block := part25478_0

theorem follows25478 : blockTargetsFollow source25478 0 target25478 :=
  And.intro (by
    intro index bounded
    change source25478.get? (0 + index) = destination25478_0.get? index
    have same : source25478 = destination25478_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25478 : (target25478.map Setup.Block.length).sum = source25478.length := by decide +kernel

noncomputable def source25479 : Setup.Block := original.get ⟨7, by decide +kernel⟩

column_blocks_part part25479_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 166 stop 167
noncomputable def destination25479_0 : Setup.Block := part25479_0.get ⟨0, by decide +kernel⟩

noncomputable def target25479 : List Setup.Block := part25479_0

theorem follows25479 : blockTargetsFollow source25479 0 target25479 :=
  And.intro (by
    intro index bounded
    change source25479.get? (0 + index) = destination25479_0.get? index
    have same : source25479 = destination25479_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25479 : (target25479.map Setup.Block.length).sum = source25479.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk199
