import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn6Part15

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Every independently imported native output agrees with the ordinary column.
    All common prefixes and the differently compressed final cells are checked. -/
theorem shift_column6_get (n : Nat) :
    nativeShiftColumn6.get? n = byteShiftColumn6.get? n := by
  apply bridge6Part0
  intro k0
  apply bridge6Part1
  intro k1
  apply bridge6Part2
  intro k2
  apply bridge6Part3
  intro k3
  apply bridge6Part4
  intro k4
  apply bridge6Part5
  intro k5
  apply bridge6Part6
  intro k6
  apply bridge6Part7
  intro k7
  apply bridge6Part8
  intro k8
  apply bridge6Part9
  intro k9
  apply bridge6Part10
  intro k10
  apply bridge6Part11
  intro k11
  apply bridge6Part12
  intro k12
  apply bridge6Part13
  intro k13
  apply bridge6Part14
  intro k14
  apply bridge6Part15
  intro k15
  exact blocksAgree_sound _ _ tail6 _

end Airbender.UnifiedReduced.Setup.Proofs
