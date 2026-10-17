import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn7Part15

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Every independently imported native output agrees with the ordinary column.
    All common prefixes and the differently compressed final cells are checked. -/
theorem shift_column7_get (n : Nat) :
    nativeShiftColumn7.get? n = byteShiftColumn7.get? n := by
  apply bridge7Part0
  intro k0
  apply bridge7Part1
  intro k1
  apply bridge7Part2
  intro k2
  apply bridge7Part3
  intro k3
  apply bridge7Part4
  intro k4
  apply bridge7Part5
  intro k5
  apply bridge7Part6
  intro k6
  apply bridge7Part7
  intro k7
  apply bridge7Part8
  intro k8
  apply bridge7Part9
  intro k9
  apply bridge7Part10
  intro k10
  apply bridge7Part11
  intro k11
  apply bridge7Part12
  intro k12
  apply bridge7Part13
  intro k13
  apply bridge7Part14
  intro k14
  apply bridge7Part15
  intro k15
  exact blocksAgree_sound _ _ tail7 _

end Airbender.UnifiedReduced.Setup.Proofs
