import Airbender.Review.Helpers.Memory.NativeProgramData
import Airbender.Review.Circuits.WordMemory.Tables.ROMData
import Airbender.Proofs.Tables.ZeroTail
import Mathlib.Tactic.IntervalCases

namespace Airbender.Trace.ROM.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def selectedWord (n : Nat) : Nat := (nativeProgramData.image.get? n).getD 0

private theorem image_zero_tail : zeroTail 4 nativeProgramData.image.blocks.toList = true := by
  decide +kernel
private theorem image_coverage : (nativeProgramData.image.blocks.toList.map Block.length).sum =
    1048576 := by decide +kernel

theorem selectedWord_zero (n : Nat) (lower : 4 ≤ n) (bound : n < 1048576) :
    selectedWord n = 0 := by
  have value := zeroTail_sound _ _ image_zero_tail n lower (by rw [image_coverage]; exact bound)
  exact congrArg (fun item => item.getD 0) value

private theorem output_zero_tail (lane : Fin 2) :
    zeroTail 4 nativeWordData.columns[lane.val + 1].blocks.toList = true := by
  fin_cases lane <;> decide +kernel
private theorem output_coverage (lane : Fin 2) :
    (nativeWordData.columns[lane.val + 1].blocks.toList.map Block.length).sum = 1048576 := by
  fin_cases lane <;> decide +kernel
private theorem output_zero (lane : Fin 2) (n : Nat) (lower : 4 ≤ n) (bound : n < 1048576) :
    nativeWordData.columns[lane.val + 1].get? n = some 0 :=
  zeroTail_sound _ _ (output_zero_tail lane) n lower
    (by rw [output_coverage]; exact bound)

private theorem key (n : Nat) (bound : n < 1048576) :
    nativeWordData.columns[0].get? n = some (4 * n) := by
  change getFromBlocks [.affine 1048576 0 4] n = some (4 * n)
  simp only [getFromBlocks, Block.get?, Block.length, if_pos bound]
  have cast : (4 : Int) * (n : Int) = ((4 * n : Nat) : Int) := by simp
  rw [cast]
  norm_num
  rw [cast, Int.toNat_natCast]

private theorem padding (lane : Fin 5) (n : Nat) (bound : n < 1048576) :
    nativeWordData.columns[lane.val + 3].get? n = some 0 := by
  have shape : nativeWordData.columns[lane.val + 3] = Column.mk #[.affine 1048576 0 0] := by
    fin_cases lane <;> rfl
  rw [shape]
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, bound]

private theorem tag (n : Nat) (bound : n < 1048576) :
    nativeWordData.columns[8].get? n = some 34 := by
  change getFromBlocks [.affine 1048576 34 0] n = some 34
  simp [getFromBlocks, Block.get?, Block.length, bound]

/-- The complete imported word-ROM region agrees with its independently imported
    public program image, including every padded word and every physical field. -/
theorem imported_word_rom_row (n : Nat) (bound : n < 1048576) :
    nativeWordData.columns.map (fun column => (column.get? n).getD 0) =
      (#v[4 * n, selectedWord n % 65536, selectedWord n / 65536,
        0, 0, 0, 0, 0, 34] : Vector Nat 9) := by
  by_cases leading : n < 4
  · interval_cases n <;> decide +kernel
  · have lower : 4 ≤ n := by omega
    rw [selectedWord_zero n lower bound]
    apply Vector.ext
    intro lane hLane
    interval_cases lane
    all_goals simp only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, Nat.zero_mod, Nat.zero_div]
    · exact congrArg (fun value => value.getD 0) (key n bound)
    · exact congrArg (fun value => value.getD 0) (output_zero 0 n lower bound)
    · exact congrArg (fun value => value.getD 0) (output_zero 1 n lower bound)
    · exact congrArg (fun value => value.getD 0) (padding 0 n bound)
    · exact congrArg (fun value => value.getD 0) (padding 1 n bound)
    · exact congrArg (fun value => value.getD 0) (padding 2 n bound)
    · exact congrArg (fun value => value.getD 0) (padding 3 n bound)
    · exact congrArg (fun value => value.getD 0) (padding 4 n bound)
    · exact congrArg (fun value => value.getD 0) (tag n bound)

end Airbender.Trace.ROM.Proofs
