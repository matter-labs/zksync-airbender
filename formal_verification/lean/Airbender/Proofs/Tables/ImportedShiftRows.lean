import Airbender.Proofs.Tables.ShiftKeys
import Airbender.Proofs.Tables.ShiftColumnCoverage
import Airbender.Proofs.Tables.ShiftOutputCertificate0
import Airbender.Proofs.Tables.ShiftOutputCertificate1
import Airbender.Proofs.Tables.ShiftOutputCertificate2
import Airbender.Proofs.Tables.ShiftOutputCertificate3
import Mathlib.Tactic.IntervalCases

namespace Airbender.Verification.ShiftColumns
open Setup Setup.Proofs ShiftCertificate
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

private theorem checks (lane : Fin 4) :
    checkBlocks (outputByte lane.val) 0 byteShiftData.columns[lane.val + 4].blocks.toList = true := by
  fin_cases lane
  · exact output0_checks
  · exact output1_checks
  · exact output2_checks
  · exact output3_checks

theorem output (lane : Fin 4) (n : Nat) (bound : n < 262144) :
    byteShiftData.columns[lane.val + 4].get? n = some (outputByte lane.val n) := by
  have values := checkBlocks_sound _ _ 0 n (checks lane)
    (by
      have coverage := shift_coverage ⟨lane.val + 4, by omega⟩
      simp only [Fin.getElem_fin] at coverage
      rw [coverage]
      exact bound)
  simpa only [Column.get?, Nat.zero_add] using values

theorem padding (n : Nat) (bound : n < 262144) :
    byteShiftData.columns[8].get? n = some 0 := by
  change getFromBlocks [.affine 262144 0 0] n = some 0
  simp [getFromBlocks, Block.get?, Block.length, bound]

theorem tag (n : Nat) (bound : n < 262144) :
    byteShiftData.columns[9].get? n = some byteShiftDataRegion.id := by
  change getFromBlocks [.affine 262144 9 0] n = some 9
  simp [getFromBlocks, Block.get?, Block.length, bound]

/-- Every key, output byte, padding column and native tag of the imported shift region. -/
theorem row (n : Nat) (bound : n < 262144) :
    byteShiftData.columns.map (fun column => (column.get? n).getD 0) =
      let out := (shiftByteContribution (n / 65536) (n / 256 % 256)
        (n / 8 % 32) (n % 8)).toNat
      #v[n / 65536, n / 256 % 256, n / 8 % 32, n % 8,
        out % 256, out / 256 % 256, out / 65536 % 256, out / 16777216 % 256, 0, 9] := by
  have p := ShiftKeys.position n bound
  have b := ShiftKeys.byte n bound
  have a := ShiftKeys.amount n bound
  have o := ShiftKeys.operation n bound
  apply Vector.ext
  intro lane hLane
  interval_cases lane
  all_goals simp only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  · exact congrArg (fun v => v.getD 0) p
  · exact congrArg (fun v => v.getD 0) b
  · exact congrArg (fun v => v.getD 0) a
  · exact congrArg (fun v => v.getD 0) o
  · simpa only [outputByte, Nat.pow_zero, Nat.div_one, Option.getD_some] using
      congrArg (fun v => v.getD 0) (output ⟨0, by decide⟩ n bound)
  · simpa only [outputByte, Nat.pow_one, Option.getD_some] using
      congrArg (fun v => v.getD 0) (output ⟨1, by decide⟩ n bound)
  · simpa only [outputByte, Nat.reducePow, Option.getD_some] using
      congrArg (fun v => v.getD 0) (output ⟨2, by decide⟩ n bound)
  · simpa only [outputByte, Nat.reducePow, Option.getD_some] using
      congrArg (fun v => v.getD 0) (output ⟨3, by decide⟩ n bound)
  · exact congrArg (fun v => v.getD 0) (padding n bound)
  · exact congrArg (fun v => v.getD 0) (tag n bound)

end Airbender.Verification.ShiftColumns
