import Airbender.Proofs.Tables.BinaryColumns
import Airbender.Proofs.Tables.ShiftKeys

namespace Airbender.Verification.BinaryColumns
open Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem truncation (n : Nat) (bound : n < 65536) :
    byteTruncateData.columns[2].get? n = some (n / 256 % 32) := by
  let block := Block.periodic 32 1 (Array.replicate 256 0)
  change getFromBlocks (List.replicate 8 block) n = _
  have length : block.length = 8192 := by decide
  have extent : n < 8 * block.length := by rw [length]; omega
  have repeated := ShiftKeys.repeated_get block 8 n extent
  rw [length] at repeated
  have reduced := periodic_constant 32 0 (n % 8192)
    (by have := Nat.mod_lt n (by decide : 0 < 8192); omega)
  have value : 0 + (n % 8192) / 256 = n / 256 % 32 := by omega
  exact repeated.trans (reduced.trans (congrArg some value))

end Airbender.Verification.BinaryColumns
