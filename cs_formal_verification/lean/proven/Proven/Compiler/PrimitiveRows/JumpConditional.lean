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
theorem jump31 (row : Fin 4456448)
    (selected : ((NativeFixedRows.jumpBranch row)[9] : F) = 31) (provided : Array (F × F)) :
    (Verification.conditionalTable (p := babyBearModulus)).Contains provided (((NativeFixedRows.jumpBranch row)[0] : F), ((NativeFixedRows.jumpBranch row)[1] : F)) := by
  have tagValue : ((NativeFixedRows.jumpBranch row)[9] : F).val =
      if row.val < 131072 then 1 else if row.val < 196608 then 2 else if row.val < 262144 then 5 else 31 := by
    unfold NativeFixedRows.jumpBranch
    dsimp only
    split_ifs <;> kernel_rfl
  have selectedNat := congrArg ZMod.val selected
  rw [tagValue, show (31 : F).val = 31 from by kernel_rfl] at selectedNat
  have region : 262144 ≤ row.val ∧ row.val < 4456448 := by
    split_ifs at selectedNat <;> omega
  let index : Fin 4194304 := ⟨row.val - 262144, by have limit := row.isLt; omega⟩
  change ∃ index : Fin 4194304, (((NativeFixedRows.jumpBranch row)[0] : F), ((NativeFixedRows.jumpBranch row)[1] : F)) = ((index.val : F), (((Verification.conditionalValue) index.val : Nat) : F))
  refine ⟨index, ?_⟩
  have lower0 : ¬ row.val < 131072 := by omega
  have lower1 : ¬ row.val < 196608 := by omega
  have lower2 : ¬ row.val < 262144 := by omega
  simp only [NativeFixedRows.jumpBranch, ite_eq_right lower0, ite_eq_right lower1, ite_eq_right lower2]
  apply Prod.ext
  · kernel_rfl
  · kernel_rfl
