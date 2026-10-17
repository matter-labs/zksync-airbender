import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.SignData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ByteSignData
import Mathlib.Tactic.IntervalCases

namespace Airbender.UnifiedReduced.Setup.Proofs
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem imported_byte_sign_row (n : Fin 256) :
    nativeByteSignData.columns.map (fun column => column.get? n.val) =
      (#v[n.val, if n.val < 128 then 0 else 255, 0, 0, 0, 0, 0, 0, 0, 3] : Vector Nat 10).map some := by
  revert n
  decide +kernel

private theorem constant_get (length value n : Nat) (bound : n < length) :
    Block.get? (.affine length value 0) n = some value := by
  simp [Block.get?, Block.length, bound]

private theorem sign_key (n : Nat) (bound : n < 65536) :
    nativeSignData.columns[0].get? n = some n := by
  change getFromBlocks [.affine 65536 0 1] n = some n
  simp [getFromBlocks, Block.get?, Block.length, bound]

private theorem sign_value (n : Nat) (bound : n < 65536) :
    nativeSignData.columns[1].get? n = some (n / 32768) := by
  change getFromBlocks [.affine 32768 0 0, .affine 32768 1 0] n = _
  by_cases first : n < 32768
  · have value : n / 32768 = 0 := by omega
    simp only [getFromBlocks, Block.length, if_pos first, value]
    exact constant_get 32768 0 n first
  · have extent : n - 32768 < 32768 := by omega
    have value : n / 32768 = 1 := by omega
    simp only [getFromBlocks, Block.length, if_neg first, if_pos extent, value]
    exact constant_get 32768 1 (n - 32768) extent

private theorem sign_padding (lane : Fin 7) (n : Nat) (bound : n < 65536) :
    nativeSignData.columns[lane.val + 2].get? n = some 0 := by
  have shape : nativeSignData.columns[lane.val + 2] = Column.mk #[.affine 65536 0 0] := by
    fin_cases lane <;> rfl
  rw [shape]
  simpa only [Column.get?, getFromBlocks, Block.length, if_pos bound] using
    constant_get 65536 0 n bound

private theorem sign_tag (n : Nat) (bound : n < 65536) :
    nativeSignData.columns[9].get? n = some 5 := by
  change getFromBlocks [.affine 65536 5 0] n = some 5
  simp only [getFromBlocks, Block.length, if_pos bound]
  exact constant_get 65536 5 n bound

/-- Every physical native ID-5 field retains its original mathematical meaning. -/
theorem imported_sign_row (n : Nat) (bound : n < 65536) :
    nativeSignData.columns.map (fun column => column.get? n) =
      (#v[n, n / 32768, 0, 0, 0, 0, 0, 0, 0, 5] : Vector Nat 10).map some := by
  apply Vector.ext
  intro lane hLane
  interval_cases lane
  all_goals simp only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  · exact sign_key n bound
  · exact sign_value n bound
  · exact sign_padding 0 n bound
  · exact sign_padding 1 n bound
  · exact sign_padding 2 n bound
  · exact sign_padding 3 n bound
  · exact sign_padding 4 n bound
  · exact sign_padding 5 n bound
  · exact sign_padding 6 n bound
  · exact sign_tag n bound

end Airbender.UnifiedReduced.Setup.Proofs
