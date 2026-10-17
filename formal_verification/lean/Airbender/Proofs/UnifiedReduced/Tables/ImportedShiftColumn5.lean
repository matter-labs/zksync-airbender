import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn5Part15

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Every independently imported native output agrees with the ordinary column.
    All common prefixes and the differently compressed final cells are checked. -/
theorem shift_column5_get (n : Nat) :
    nativeShiftColumn5.get? n = byteShiftColumn5.get? n := by
  apply bridge5Part0
  intro k0
  apply bridge5Part1
  intro k1
  apply bridge5Part2
  intro k2
  apply bridge5Part3
  intro k3
  apply bridge5Part4
  intro k4
  apply bridge5Part5
  intro k5
  apply bridge5Part6
  intro k6
  apply bridge5Part7
  intro k7
  apply bridge5Part8
  intro k8
  apply bridge5Part9
  intro k9
  apply bridge5Part10
  intro k10
  apply bridge5Part11
  intro k11
  apply bridge5Part12
  intro k12
  apply bridge5Part13
  intro k13
  apply bridge5Part14
  intro k14
  apply bridge5Part15
  intro k15
  exact blocksAgree_sound _ _ tail5 _

end Airbender.UnifiedReduced.Setup.Proofs
