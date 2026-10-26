import Airbender.Proofs.GKRProtocol.FixedMembership
import Airbender.Proofs.GKRProtocol.FixedSetupNative.MulDivValues
import Airbender.Review.Circuits.JumpBranchSlt.Tables.Control
import Airbender.Proofs.Tables.ImportedRanges

namespace Airbender.Compiler.FixedSetupNative.MulDiv
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem tag1_contains (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 8) = 1)
    (provided : Array (Source.BaseField × Source.BaseField)) :
    (Verification.regIsZeroTable (p := babyBearModulus)).Contains provided (nativeSetup.value row (.generic 0), nativeSetup.value row (.generic 1)) := by
  have domain := tag1_region row selected
  let index : Fin Verification.regZeroData.length := ⟨row.val - 0, by change row.val - 0 < 131072; omega⟩
  have position : row.val = 0 + index.val := by dsimp [index]; omega
  exact materialized_pair_contains nativeSetup Verification.regZeroData (by decide) (by decide)
    0 rfl rfl row index position regZeroData0_value (fun entry => by change nativeValueColumn.get? (0 + entry.val) = zeroValueColumn.get? entry.val; rw [Nat.zero_add]; exact regZeroData1_value entry) "Airbender.RegIsZero" provided

theorem tag41_contains (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 8) = 41)
    (provided : Array (Source.BaseField × Source.BaseField)) :
    (Verification.u16LowByteTable (p := babyBearModulus)).Contains provided (nativeSetup.value row (.generic 0), nativeSetup.value row (.generic 1)) := by
  have domain := tag41_region row selected
  let index : Fin Verification.lowByteData.length := ⟨row.val - 204800, by change row.val - 204800 < 65536; omega⟩
  have position : row.val = 204800 + index.val := by dsimp [index]; omega
  exact materialized_pair_contains nativeSetup Verification.lowByteData (by decide) (by decide)
    204800 rfl rfl row index position lowByteData0_value lowByteData1_value "Airbender.U16GetLowByte" provided

theorem range13_value_bound (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 8) = 26) :
    (nativeSetup.value row (.generic 0)).val < 8192 := by
  have domain := tag26_region row selected
  let index : Fin 8192 := ⟨row.val - 196608, by omega⟩
  have position : row.val = 196608 + index.val := by dsimp [index]; omega
  have cell := nativeSetup.generic_cell_value row (⟨0, by decide⟩ : Fin 9)
  change nativeSetup.value row (.generic 0) =
    ((nativeKeyColumn.get? (0 + row.val)).getD 0 : Source.BaseField) at cell
  rw [Nat.zero_add, position, range13_key_value index, Option.getD_some] at cell
  rw [cell, ZMod.val_natCast, Nat.mod_eq_of_lt]
  · exact index.isLt
  · have bound := index.isLt
    have large : 8192 < babyBearModulus := by decide +kernel
    exact lt_trans bound large

end Airbender.Compiler.FixedSetupNative.MulDiv
