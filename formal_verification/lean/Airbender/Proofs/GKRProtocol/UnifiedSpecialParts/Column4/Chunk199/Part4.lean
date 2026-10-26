import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk199.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk199
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source25504 : Setup.Block := original.get ⟨32, by decide +kernel⟩

column_blocks_part part25504_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 191 stop 192
noncomputable def destination25504_0 : Setup.Block := part25504_0.get ⟨0, by decide +kernel⟩

noncomputable def target25504 : List Setup.Block := part25504_0

theorem follows25504 : blockTargetsFollow source25504 0 target25504 :=
  And.intro (by
    intro index bounded
    change source25504.get? (0 + index) = destination25504_0.get? index
    have same : source25504 = destination25504_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25504 : (target25504.map Setup.Block.length).sum = source25504.length := by decide +kernel

noncomputable def source25505 : Setup.Block := original.get ⟨33, by decide +kernel⟩

column_blocks_part part25505_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 192 stop 193
noncomputable def destination25505_0 : Setup.Block := part25505_0.get ⟨0, by decide +kernel⟩

noncomputable def target25505 : List Setup.Block := part25505_0

theorem follows25505 : blockTargetsFollow source25505 0 target25505 :=
  And.intro (by
    intro index bounded
    change source25505.get? (0 + index) = destination25505_0.get? index
    have same : source25505 = destination25505_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25505 : (target25505.map Setup.Block.length).sum = source25505.length := by decide +kernel

noncomputable def source25506 : Setup.Block := original.get ⟨34, by decide +kernel⟩

column_blocks_part part25506_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 193 stop 194
noncomputable def destination25506_0 : Setup.Block := part25506_0.get ⟨0, by decide +kernel⟩

noncomputable def target25506 : List Setup.Block := part25506_0

theorem follows25506 : blockTargetsFollow source25506 0 target25506 :=
  And.intro (by
    intro index bounded
    change source25506.get? (0 + index) = destination25506_0.get? index
    have same : source25506 = destination25506_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25506 : (target25506.map Setup.Block.length).sum = source25506.length := by decide +kernel

noncomputable def source25507 : Setup.Block := original.get ⟨35, by decide +kernel⟩

column_blocks_part part25507_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 194 stop 195
noncomputable def destination25507_0 : Setup.Block := part25507_0.get ⟨0, by decide +kernel⟩

noncomputable def target25507 : List Setup.Block := part25507_0

theorem follows25507 : blockTargetsFollow source25507 0 target25507 :=
  And.intro (by
    intro index bounded
    change source25507.get? (0 + index) = destination25507_0.get? index
    have same : source25507 = destination25507_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25507 : (target25507.map Setup.Block.length).sum = source25507.length := by decide +kernel

noncomputable def source25508 : Setup.Block := original.get ⟨36, by decide +kernel⟩

column_blocks_part part25508_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 195 stop 196
noncomputable def destination25508_0 : Setup.Block := part25508_0.get ⟨0, by decide +kernel⟩

noncomputable def target25508 : List Setup.Block := part25508_0

theorem follows25508 : blockTargetsFollow source25508 0 target25508 :=
  And.intro (by
    intro index bounded
    change source25508.get? (0 + index) = destination25508_0.get? index
    have same : source25508 = destination25508_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25508 : (target25508.map Setup.Block.length).sum = source25508.length := by decide +kernel

noncomputable def source25509 : Setup.Block := original.get ⟨37, by decide +kernel⟩

column_blocks_part part25509_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 196 stop 197
noncomputable def destination25509_0 : Setup.Block := part25509_0.get ⟨0, by decide +kernel⟩

noncomputable def target25509 : List Setup.Block := part25509_0

theorem follows25509 : blockTargetsFollow source25509 0 target25509 :=
  And.intro (by
    intro index bounded
    change source25509.get? (0 + index) = destination25509_0.get? index
    have same : source25509 = destination25509_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25509 : (target25509.map Setup.Block.length).sum = source25509.length := by decide +kernel

noncomputable def source25510 : Setup.Block := original.get ⟨38, by decide +kernel⟩

column_blocks_part part25510_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 197 stop 198
noncomputable def destination25510_0 : Setup.Block := part25510_0.get ⟨0, by decide +kernel⟩

noncomputable def target25510 : List Setup.Block := part25510_0

theorem follows25510 : blockTargetsFollow source25510 0 target25510 :=
  And.intro (by
    intro index bounded
    change source25510.get? (0 + index) = destination25510_0.get? index
    have same : source25510 = destination25510_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25510 : (target25510.map Setup.Block.length).sum = source25510.length := by decide +kernel

noncomputable def source25511 : Setup.Block := original.get ⟨39, by decide +kernel⟩

column_blocks_part part25511_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(4 : Nat)]) start 198 stop 199
noncomputable def destination25511_0 : Setup.Block := part25511_0.get ⟨0, by decide +kernel⟩

noncomputable def target25511 : List Setup.Block := part25511_0

theorem follows25511 : blockTargetsFollow source25511 0 target25511 :=
  And.intro (by
    intro index bounded
    change source25511.get? (0 + index) = destination25511_0.get? index
    have same : source25511 = destination25511_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25511 : (target25511.map Setup.Block.length).sum = source25511.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk199
