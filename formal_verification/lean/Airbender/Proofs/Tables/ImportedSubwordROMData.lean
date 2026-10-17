import Airbender.Proofs.Tables.ImportedROMProgram
import Airbender.Proofs.Tables.SubwordCharacterization
import Airbender.Proofs.Tables.ImportedROMReads
import Airbender.Proofs.Tables.ConstantTail

namespace Airbender.Verification.SubwordROMGeometry
open Setup Setup.Proofs
open Airbender.Trace.ROM.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def romCutoff (byte : Bool) : Nat := if byte then 32 else 16

theorem rom_tail_checked (byte : Bool) (lane : Fin 2) :
    constantTail 0 (romCutoff byte) (subwordROMData byte).columns[lane.val + 1].blocks.toList = true := by
  cases byte <;> fin_cases lane <;> decide +kernel

theorem rom_tail_extent (byte : Bool) (lane : Fin 2) :
    ((subwordROMData byte).columns[lane.val + 1].blocks.toList.map Block.length).sum =
      (subwordROMData byte).length := by
  cases byte <;> fin_cases lane <;> decide +kernel

theorem rom_early_rows (byte : Bool) (index : Fin (romCutoff byte)) :
    subwordROMRow byte index.val = subwordProgramROMRow Airbender.Trace.ROM.importedWords byte index.val := by
  cases byte <;> fin_cases index <;> decide +kernel


end Airbender.Verification.SubwordROMGeometry
