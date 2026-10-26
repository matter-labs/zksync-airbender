import Airbender.Proofs.GKRProtocol.FixedMembership
import Airbender.Proofs.GKRProtocol.FixedSetupNative.JumpBranchValues
import Airbender.Review.Circuits.JumpBranchSlt.Tables.Control
import Airbender.Proofs.Tables.ImportedRanges

namespace Airbender.Compiler.FixedSetupNative.JumpBranch
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem tag1_contains (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 9) = 1)
    (provided : Array (Source.BaseField × Source.BaseField)) :
    (Verification.regIsZeroTable (p := babyBearModulus)).Contains provided (nativeSetup.value row (.generic 0), nativeSetup.value row (.generic 1)) := by
  have domain := tag1_region row selected
  let index : Fin Verification.regZeroData.length := ⟨row.val - 0, by change row.val - 0 < 131072; omega⟩
  have position : row.val = 0 + index.val := by dsimp [index]; omega
  exact materialized_pair_contains nativeSetup Verification.regZeroData (by decide) (by decide)
    0 rfl rfl row index position regZeroData0_value (fun entry => by change nativeValueColumn.get? (0 + entry.val) = zeroValueColumn.get? entry.val; rw [Nat.zero_add]; exact regZeroData1_value entry) "Airbender.RegIsZero" provided

theorem tag2_contains (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 9) = 2)
    (provided : Array (Source.BaseField × Source.BaseField × Source.BaseField)) :
    (Verification.jumpCleanupTable (p := babyBearModulus)).Contains provided (nativeSetup.value row (.generic 0), nativeSetup.value row (.generic 1), nativeSetup.value row (.generic 2)) := by
  have domain := tag2_region row selected
  let index : Fin Verification.jumpCleanupData.length := ⟨row.val - 131072, by change row.val - 131072 < 65536; omega⟩
  have position : row.val = 131072 + index.val := by dsimp [index]; omega
  exact materialized_triple_contains nativeSetup Verification.jumpCleanupData (by decide) (by decide)
    131072 rfl rfl row index position jumpCleanupData0_value jumpCleanupData1_value jumpCleanupData2_value "Airbender.JumpCleanupOffset" provided

theorem tag5_contains (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 9) = 5)
    (provided : Array (Source.BaseField × Source.BaseField)) :
    (Verification.u16SignTable (p := babyBearModulus)).Contains provided (nativeSetup.value row (.generic 0), nativeSetup.value row (.generic 1)) := by
  have domain := tag5_region row selected
  let index : Fin Verification.signData.length := ⟨row.val - 196608, by change row.val - 196608 < 65536; omega⟩
  have position : row.val = 196608 + index.val := by dsimp [index]; omega
  exact materialized_pair_contains nativeSetup Verification.signData (by decide) (by decide)
    196608 rfl rfl row index position signData0_value signData1_value "Airbender.U16GetSign" provided

theorem tag31_contains (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 9) = 31)
    (provided : Array (Source.BaseField × Source.BaseField)) :
    (Verification.conditionalTable (p := babyBearModulus)).Contains provided (nativeSetup.value row (.generic 0), nativeSetup.value row (.generic 1)) := by
  have domain := tag31_region row selected
  let index : Fin Verification.conditionalData.length := ⟨row.val - 262144, by change row.val - 262144 < 4194304; omega⟩
  have position : row.val = 262144 + index.val := by dsimp [index]; omega
  exact materialized_pair_contains nativeSetup Verification.conditionalData (by decide) (by decide)
    262144 rfl rfl row index position conditionalData0_value conditionalData1_value "Airbender.ConditionalJmpBranchSlt" provided

end Airbender.Compiler.FixedSetupNative.JumpBranch
