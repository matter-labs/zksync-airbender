import Airbender.Proofs.Keccak.SplitChiPatterns

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

def chi5Pattern (column : Fin 5) : Vector Nat 4096 :=
  match column.val with
  | 0 => chi5GenericBlock98Pattern
  | 1 => chi5GenericBlock104Pattern
  | 2 => chi5GenericBlock112Pattern
  | 3 => chi5GenericBlock120Pattern
  | _ => chi5GenericBlock121Pattern

def chi5Positions (column : Fin 5) : Array Nat :=
  match column.val with
  | 0 => chi5GenericBlock98Positions
  | 1 => chi5GenericBlock104Positions
  | 2 => chi5GenericBlock112Positions
  | 3 => chi5GenericBlock120Positions
  | _ => chi5GenericBlock121Positions

/-- Every actual native chi output reads its retained indexed pattern. -/
theorem chi5_output_get (column : Fin 5) (index : Fin 1048576) :
    (chi5Generic.columns[5 + column.val].get? index.val) =
      some (((chi5Pattern column).toArray[digitIndex (chi5Positions column) index.val]?).getD 0) := by
  fin_cases column
  · change chi5Generic.columns[5].get? index.val =
        some ((chi5GenericBlock98Pattern.toArray[digitIndex chi5GenericBlock98Positions index.val]?).getD 0)
    have shaped : chi5Generic.columns[5] =
        Column.mk (#[chi5GenericBlock98.block] ++ chi5GenericSuffix5.blocks) := by rfl
    rw [shaped]
    have blockShape : chi5GenericBlock98.block =
        Block.dense (Vector.ofFn (fun value : Fin 1048576 =>
          (chi5GenericBlock98Pattern.toArray[digitIndex chi5GenericBlock98Positions value.val]?).getD 0)).toArray := by rfl
    rw [blockShape]
    exact Airbender.Setup.Proofs.column_dense_ofFn_get _ _ index
  · change chi5Generic.columns[6].get? index.val =
        some ((chi5GenericBlock104Pattern.toArray[digitIndex chi5GenericBlock104Positions index.val]?).getD 0)
    have shaped : chi5Generic.columns[6] =
        Column.mk (#[chi5GenericBlock104.block] ++ chi5GenericSuffix6.blocks) := by rfl
    rw [shaped]
    have blockShape : chi5GenericBlock104.block =
        Block.dense (Vector.ofFn (fun value : Fin 1048576 =>
          (chi5GenericBlock104Pattern.toArray[digitIndex chi5GenericBlock104Positions value.val]?).getD 0)).toArray := by rfl
    rw [blockShape]
    exact Airbender.Setup.Proofs.column_dense_ofFn_get _ _ index
  · change chi5Generic.columns[7].get? index.val =
        some ((chi5GenericBlock112Pattern.toArray[digitIndex chi5GenericBlock112Positions index.val]?).getD 0)
    have shaped : chi5Generic.columns[7] =
        Column.mk (#[chi5GenericBlock112.block] ++ chi5GenericSuffix7.blocks) := by rfl
    rw [shaped]
    have blockShape : chi5GenericBlock112.block =
        Block.dense (Vector.ofFn (fun value : Fin 1048576 =>
          (chi5GenericBlock112Pattern.toArray[digitIndex chi5GenericBlock112Positions value.val]?).getD 0)).toArray := by rfl
    rw [blockShape]
    exact Airbender.Setup.Proofs.column_dense_ofFn_get _ _ index
  · change chi5Generic.columns[8].get? index.val =
        some ((chi5GenericBlock120Pattern.toArray[digitIndex chi5GenericBlock120Positions index.val]?).getD 0)
    have shaped : chi5Generic.columns[8] =
        Column.mk (#[chi5GenericBlock120.block] ++ chi5GenericSuffix8.blocks) := by rfl
    rw [shaped]
    have blockShape : chi5GenericBlock120.block =
        Block.dense (Vector.ofFn (fun value : Fin 1048576 =>
          (chi5GenericBlock120Pattern.toArray[digitIndex chi5GenericBlock120Positions value.val]?).getD 0)).toArray := by rfl
    rw [blockShape]
    exact Airbender.Setup.Proofs.column_dense_ofFn_get _ _ index
  · change chi5Generic.columns[9].get? index.val =
        some ((chi5GenericBlock121Pattern.toArray[digitIndex chi5GenericBlock121Positions index.val]?).getD 0)
    have shaped : chi5Generic.columns[9] =
        Column.mk (#[chi5GenericBlock121.block] ++ chi5GenericSuffix9.blocks) := by rfl
    rw [shaped]
    have blockShape : chi5GenericBlock121.block =
        Block.dense (Vector.ofFn (fun value : Fin 1048576 =>
          (chi5GenericBlock121Pattern.toArray[digitIndex chi5GenericBlock121Positions value.val]?).getD 0)).toArray := by rfl
    rw [blockShape]
    exact Airbender.Setup.Proofs.column_dense_ofFn_get _ _ index

end Airbender.Keccak.Split.Native.Fixed.Proofs
