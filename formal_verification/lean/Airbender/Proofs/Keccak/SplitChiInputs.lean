import Airbender.Proofs.Keccak.SplitChiRows
import Airbender.Proofs.Keccak.SplitDigitPeriodic

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 1200000

def chi5InputPattern (column : Fin 5) : Vector Nat 16 :=
  match column.val with
  | 0 | 1 => chi5GenericBlock0Pattern
  | 2 => chi5GenericBlock29Pattern
  | 3 => chi5GenericBlock78Pattern
  | _ => chi5GenericBlock92Pattern

private theorem input_patterns : ∀ column : Fin 5, ∀ value : Fin 16,
    (chi5InputPattern column)[value] = value.val := by decide +kernel

private theorem input_pattern_get (column : Fin 5) (value : Fin 16) :
    ((chi5InputPattern column).toArray[value.val]?).getD 0 = value.val := by
  rw [Array.getElem?_eq_getElem (by simpa only [Vector.size_toArray] using value.isLt),
    Option.getD_some]
  exact input_patterns column value

/-- The actual native chi input fields are the five little-endian digits. -/
theorem chi5_input_get (column : Fin 5) (index : Fin 1048576) :
    chi5Generic.columns[column.val].get? index.val =
      some (index.val / 16 ^ column.val % 16) := by
  fin_cases column
  · change chi5Generic.columns[0].get? index.val = some (index.val / 16 ^ 0 % 16)
    have shaped : chi5Generic.columns[0] =
        Column.mk (#[chi5GenericBlock0.block] ++ chi5GenericSuffix0.blocks) := by rfl
    rw [shaped]
    have blockShape : chi5GenericBlock0.block =
        Block.dense (Vector.ofFn (fun value : Fin 1048576 =>
          (chi5GenericBlock0Pattern.toArray[digitIndex chi5GenericBlock0Positions value.val]?).getD 0)).toArray := by rfl
    rw [blockShape, column_dense_ofFn_get]
    have position : digitIndex chi5GenericBlock0Positions index.val =
        index.val / 16 ^ 0 % 16 := by
      simp [chi5GenericBlock0Positions, digitIndex_singleton]
    rw [position]
    exact congrArg some (input_pattern_get 0 ⟨_, Nat.mod_lt _ (by decide)⟩)
  · change chi5Generic.columns[1].get? index.val = some (index.val / 16 ^ 1 % 16)
    have shaped : chi5Generic.columns[1] =
        Column.mk (#[chi5GenericBlock27.block] ++ chi5GenericSuffix1.blocks) := by rfl
    rw [shaped]
    have blockShape : chi5GenericBlock27.block =
        Block.periodic 4096 0 (Vector.ofFn (fun value : Fin 256 =>
          (chi5GenericBlock0Pattern.toArray[value.val / 16]?).getD 0)).toArray := by rfl
    rw [blockShape, column_periodic_ofFn_get 4096 (by decide)]
    have position : index.val % 256 / 16 = index.val / 16 % 16 := by omega
    change some ((chi5GenericBlock0Pattern.toArray[index.val % 256 / 16]?).getD 0) = _
    rw [position]
    exact congrArg some (input_pattern_get 1 ⟨_, Nat.mod_lt _ (by decide)⟩)
  · change chi5Generic.columns[2].get? index.val = some (index.val / 16 ^ 2 % 16)
    have shaped : chi5Generic.columns[2] =
        Column.mk (#[chi5GenericBlock29.block] ++ chi5GenericSuffix2.blocks) := by rfl
    rw [shaped]
    have blockShape : chi5GenericBlock29.block =
        Block.dense (Vector.ofFn (fun value : Fin 1048576 =>
          (chi5GenericBlock29Pattern.toArray[digitIndex chi5GenericBlock29Positions value.val]?).getD 0)).toArray := by rfl
    rw [blockShape, column_dense_ofFn_get]
    have position : digitIndex chi5GenericBlock29Positions index.val =
        index.val / 16 ^ 2 % 16 := by
      simp [chi5GenericBlock29Positions, digitIndex_singleton]
    rw [position]
    exact congrArg some (input_pattern_get 2 ⟨_, Nat.mod_lt _ (by decide)⟩)
  · change chi5Generic.columns[3].get? index.val = some (index.val / 16 ^ 3 % 16)
    have shaped : chi5Generic.columns[3] =
        Column.mk (#[chi5GenericBlock78.block] ++ chi5GenericSuffix3.blocks) := by rfl
    rw [shaped]
    have blockShape : chi5GenericBlock78.block =
        Block.dense (Vector.ofFn (fun value : Fin 1048576 =>
          (chi5GenericBlock78Pattern.toArray[digitIndex chi5GenericBlock78Positions value.val]?).getD 0)).toArray := by rfl
    rw [blockShape, column_dense_ofFn_get]
    have position : digitIndex chi5GenericBlock78Positions index.val =
        index.val / 16 ^ 3 % 16 := by
      simp [chi5GenericBlock78Positions, digitIndex_singleton]
    rw [position]
    exact congrArg some (input_pattern_get 3 ⟨_, Nat.mod_lt _ (by decide)⟩)
  · change chi5Generic.columns[4].get? index.val = some (index.val / 16 ^ 4 % 16)
    have shaped : chi5Generic.columns[4] =
        Column.mk (#[chi5GenericBlock92.block] ++ chi5GenericSuffix4.blocks) := by rfl
    rw [shaped]
    have blockShape : chi5GenericBlock92.block =
        Block.dense (Vector.ofFn (fun value : Fin 1048576 =>
          (chi5GenericBlock92Pattern.toArray[digitIndex chi5GenericBlock92Positions value.val]?).getD 0)).toArray := by rfl
    rw [blockShape, column_dense_ofFn_get]
    have position : digitIndex chi5GenericBlock92Positions index.val =
        index.val / 16 ^ 4 % 16 := by
      simp [chi5GenericBlock92Positions, digitIndex_singleton]
    rw [position]
    exact congrArg some (input_pattern_get 4 ⟨_, Nat.mod_lt _ (by decide)⟩)

end Airbender.Keccak.Split.Native.Fixed.Proofs
