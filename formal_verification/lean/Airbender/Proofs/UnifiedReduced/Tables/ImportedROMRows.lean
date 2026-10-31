import Airbender.Data.Setup.UnifiedReduced.Native.ROMData
import Airbender.Proofs.Tables.ImportedROMProgram
import Airbender.Proofs.Tables.ImportedROMRows
import Airbender.Review.Circuits.UnifiedReduced.Tables.Setup

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private theorem word_column (lane : Fin 3) :
    nativeROMData.columns[lane.val] = Trace.ROM.nativeWordData.columns[lane.val] := by
  fin_cases lane <;> rfl

private theorem tag_column : nativeROMData.columns[9] = Trace.ROM.nativeWordData.columns[8] := rfl

private theorem zero_checked (lane : Fin 6) :
    Airbender.Setup.Proofs.zeroTail 0 nativeROMData.columns[lane.val + 3].blocks.toList = true := by
  fin_cases lane <;> decide +kernel

private theorem zero_extent (lane : Fin 6) :
    (nativeROMData.columns[lane.val + 3].blocks.toList.map Block.length).sum = 1048576 := by
  fin_cases lane <;> decide +kernel

/-- Independently imported unified ROM includes the extra physical zero lane;
    all addresses, both outputs and the native discriminator are checked. -/
theorem imported_rom_row (index : Nat) (bound : index < 1048576) :
    nativeROMData.columns.map (fun column => (column.get? index).getD 0) =
      (#v[4 * index, Trace.ROM.Proofs.selectedWord index % 65536,
        Trace.ROM.Proofs.selectedWord index / 65536, 0, 0, 0, 0, 0, 0, 34] : Vector Nat 10) := by
  have ordinary := Trace.ROM.Proofs.imported_word_rom_row index bound
  have first (lane : Fin 3) :
      (nativeROMData.columns[lane.val].get? index).getD 0 =
        (#v[4 * index, Trace.ROM.Proofs.selectedWord index % 65536,
          Trace.ROM.Proofs.selectedWord index / 65536] : Vector Nat 3)[lane] := by
    rw [word_column lane]
    have value := congrArg (fun row : Vector Nat 9 => row[lane.val]) ordinary
    fin_cases lane <;> simpa only [Vector.getElem_map, Fin.getElem_fin,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] using value
  have zero (lane : Fin 6) : (nativeROMData.columns[lane.val + 3].get? index).getD 0 = 0 := by
    have actual := Airbender.Setup.Proofs.zeroTail_sound _ _ (zero_checked lane) index
      (Nat.zero_le _) (by rw [zero_extent]; exact bound)
    exact congrArg (fun value => value.getD 0) actual
  have tag : (nativeROMData.columns[9].get? index).getD 0 = 34 := by
    rw [tag_column]
    have value := congrArg (fun row : Vector Nat 9 => row[8]) ordinary
    simpa only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ] using value
  apply Vector.ext
  intro lane hLane
  interval_cases lane
  all_goals simp only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  · exact first 0
  · exact first 1
  · exact first 2
  · exact zero 0
  · exact zero 1
  · exact zero 2
  · exact zero 3
  · exact zero 4
  · exact zero 5
  · exact tag

end Airbender.UnifiedReduced.Setup.Proofs
