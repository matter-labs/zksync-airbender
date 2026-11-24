module
public import Human.Compiler.NativeFixedRows
public import Human.Compiler.NativeArithmetic
public import Mathlib.Tactic.NormNum
public import Proven.KernelRfl

@[expose] public section
namespace Airbender.Compiler.NativePrimitiveRows
open Airbender NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 65536

/-- The native discriminator selects the exact fixed region. -/
theorem mul1 (row : Fin 270336)
    (selected : ((NativeFixedRows.mulDiv row)[8] : F) = 1) (provided : Array (F × F)) :
    (Verification.regIsZeroTable (p := babyBearModulus)).Contains provided (((NativeFixedRows.mulDiv row)[0] : F), ((NativeFixedRows.mulDiv row)[1] : F)) := by
  have tagValue : ((NativeFixedRows.mulDiv row)[8] : F).val =
      if row.val < 131072 then 1 else if row.val < 196608 then 10 else if row.val < 204800 then 26 else 41 := by
    unfold NativeFixedRows.mulDiv
    dsimp only
    split_ifs <;> kernel_rfl
  have selectedNat := congrArg ZMod.val selected
  rw [tagValue, show (1 : F).val = 1 from by kernel_rfl] at selectedNat
  have region : 0 ≤ row.val ∧ row.val < 131072 := by
    split_ifs at selectedNat <;> omega
  let index : Fin 131072 := ⟨row.val - 0, by have limit := row.isLt; omega⟩
  change ∃ index : Fin 131072, (((NativeFixedRows.mulDiv row)[0] : F), ((NativeFixedRows.mulDiv row)[1] : F)) = ((index.val : F), (((fun (n : Nat) => if n = 0 then 1 else 0) index.val : Nat) : F))
  refine ⟨index, ?_⟩
  have upper0 : row.val < 131072 := by omega
  simp only [NativeFixedRows.mulDiv, ite_eq_left upper0]
  apply Prod.ext
  · kernel_rfl
  · kernel_rfl

/-- The native discriminator selects the exact fixed region. -/
theorem mul41 (row : Fin 270336)
    (selected : ((NativeFixedRows.mulDiv row)[8] : F) = 41) (provided : Array (F × F)) :
    (Verification.u16LowByteTable (p := babyBearModulus)).Contains provided (((NativeFixedRows.mulDiv row)[0] : F), ((NativeFixedRows.mulDiv row)[1] : F)) := by
  have tagValue : ((NativeFixedRows.mulDiv row)[8] : F).val =
      if row.val < 131072 then 1 else if row.val < 196608 then 10 else if row.val < 204800 then 26 else 41 := by
    unfold NativeFixedRows.mulDiv
    dsimp only
    split_ifs <;> kernel_rfl
  have selectedNat := congrArg ZMod.val selected
  rw [tagValue, show (41 : F).val = 41 from by kernel_rfl] at selectedNat
  have region : 204800 ≤ row.val ∧ row.val < 270336 := by
    split_ifs at selectedNat <;> omega
  let index : Fin 65536 := ⟨row.val - 204800, by have limit := row.isLt; omega⟩
  change ∃ index : Fin 65536, (((NativeFixedRows.mulDiv row)[0] : F), ((NativeFixedRows.mulDiv row)[1] : F)) = ((index.val : F), (((fun (n : Nat) => n % 256) index.val : Nat) : F))
  refine ⟨index, ?_⟩
  have lower0 : ¬ row.val < 131072 := by omega
  have lower1 : ¬ row.val < 196608 := by omega
  have lower2 : ¬ row.val < 204800 := by omega
  simp only [NativeFixedRows.mulDiv, ite_eq_right lower0, ite_eq_right lower1, ite_eq_right lower2]
  apply Prod.ext
  · kernel_rfl
  · kernel_rfl

/-- The native discriminator selects the exact fixed region. -/
theorem mul26 (row : Fin 270336)
    (selected : ((NativeFixedRows.mulDiv row)[8] : F) = 26) :
    ((NativeFixedRows.mulDiv row)[0] : F).val < 8192 := by
  have tagValue : ((NativeFixedRows.mulDiv row)[8] : F).val =
      if row.val < 131072 then 1 else if row.val < 196608 then 10 else if row.val < 204800 then 26 else 41 := by
    unfold NativeFixedRows.mulDiv
    dsimp only
    split_ifs <;> kernel_rfl
  have selectedNat := congrArg ZMod.val selected
  rw [tagValue, show (26 : F).val = 26 from by kernel_rfl] at selectedNat
  have region : 196608 ≤ row.val ∧ row.val < 204800 := by
    split_ifs at selectedNat <;> omega
  let index : Fin 8192 := ⟨row.val - 196608, by have limit := row.isLt; omega⟩
  have before : ¬ row.val < 131072 := by omega
  have middle : ¬ row.val < 196608 := by omega
  have upper : row.val < 204800 := region.2
  simp only [NativeFixedRows.mulDiv, ite_eq_right before, ite_eq_right middle, ite_eq_left upper]
  change ((row.val - 196608 : Nat) : F).val < 8192
  rw [ZMod.val_natCast]
  exact lt_of_le_of_lt (Nat.mod_le _ _) index.isLt
