import Slop.MulDiv.Claims
import Slop.BabyBear
import Slop.Verification.StaticLookup
import Mathlib.Tactic.IntervalCases

namespace Tests.MulDivProduct
open Airbender

-- MUL/MULHU: (2^32-1)^2, with three nonzero byte carries.
-- DIVU/REMU: (2^32-1) / 65537 = 65535, remainder zero.
private def row (operation : Fin 4) : Nat → ZMod babyBearModulus
  | 4 => 1
  | 5 | 7 => 1
  | 6 => 2
  | 10 => if operation = 0 then 1 else 0
  | 11 => if operation = 1 then 1 else 0
  | 12 => if operation = 2 then 1 else 0
  | 13 => if operation = 3 then 1 else 0
  | 14 | 16 => 4
  | 20 | 21 | 49 => 65535
  | 24 | 25 | 53 | 54 => if operation.val < 2 then 65535 else 1
  | 28 => if operation = 0 then 1 else if operation = 1 then 65534 else
      if operation = 2 then 65535 else 0
  | 29 => if operation = 1 then 65535 else 0
  | 33 | 34 | 58 | 59 => if operation.val < 2 then 255 else 1
  | 35 | 60 => 255
  | 36 | 61 => if operation.val < 2 then 255 else 0
  | 37 => if operation = 0 then 65534 else if operation = 1 then 1 else
      if operation = 3 then 65535 else 0
  | 38 => if operation = 0 then 65535 else 0
  | 39 | 56 => if operation.val < 2 then 1 else 65535
  | 40 | 57 => if operation.val < 2 then 0 else 65534
  | 41 | 62 => if operation.val < 2 then 509 else 0
  | 42 | 63 => if operation.val < 2 then 1019 else 0
  | 43 | 64 => if operation.val < 2 then 510 else 0
  | 45 => if operation.val < 2 then 1 else 65535
  | 46 => if operation.val < 2 then 0 else 65535
  | 47 => if operation.val < 2 then 65534 else 0
  | 48 | 50 => if operation.val < 2 then 65535 else 0
  | 55 => if operation.val < 2 then 0 else 1
  | _ => 0

set_option maxHeartbeats 800000 in
private theorem satisfies (operation : Fin 4) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row operation))
      Airbender.MulDiv.importedConstraints := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · fin_cases operation <;> decide
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 16 := by simpa only [Airbender.MulDiv.lookup_count] using bound
    interval_cases i
    all_goals first
      | exact Verification.range16_contains (by fin_cases operation <;> decide)
      | exact Verification.range13_contains (by fin_cases operation <;> decide)
      | exact Verification.static_lookup_contains _ _ _ (by fin_cases operation <;> decide +kernel)
          (by fin_cases operation <;> decide +kernel)

-- Apply the generic theorem to actual imported rows in all four selector cases.
example (operation : Fin 4) :
    (⟨(row operation 49).val, (row operation 50).val⟩ : Arithmetic.Word).value *
        (⟨(row operation 24).val, (row operation 25).val⟩ : Arithmetic.Word).value =
      (⟨(row operation 45).val, (row operation 46).val⟩ : Arithmetic.Word).value +
        Arithmetic.wordModulus *
          (⟨(row operation 47).val, (row operation 48).val⟩ : Arithmetic.Word).value := by
  have result := Airbender.MulDiv.Proofs.product_with_remainder (by decide) (by decide)
    (satisfies operation) operation
    (by intro i; fin_cases operation <;> fin_cases i <;> rfl)
    (by fin_cases operation <;> constructor <;> decide)
  simpa [row, Arithmetic.Word.value] using result

private def opcode : Fin 4 → Airbender.MulDiv.Operation
  | 0 => .mul | 1 => .mulhu | 2 => .divu | 3 => .remu

private def input (operation : Fin 4) : Airbender.MulDiv.Input where
  operation := opcode operation
  left := ⟨65535, 65535⟩
  right := if operation.val < 2 then ⟨65535, 65535⟩ else ⟨1, 1⟩
  pc := ⟨0, 0⟩
  rs1 := .Regidx 1
  rs2 := .Regidx 2
  rd := .Regidx 1
  before := { (default : Reference.RiscV.Sail.State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (4294967295 : BitVec 32)
      |>.insert .x2 (if operation.val < 2 then 4294967295 else 65537 : BitVec 32)
      |>.insert .PC (0 : BitVec 32)) }

private def output (operation : Fin 4) : Reference.RiscV.Sail.Output :=
  ⟨match operation with
    | 0 => ⟨1, 0⟩ | 1 => ⟨65534, 65535⟩ | 2 => ⟨65535, 0⟩ | 3 => ⟨0, 0⟩, ⟨4, 0⟩⟩

-- Native Sail in all four routes, with rd = rs1. MUL executes the original
-- signed low-product clause: both unsigned-looking inputs are signed -1.
example (operation : Fin 4) : Airbender.MulDiv.spec (input operation) (output operation) := by
  apply Airbender.MulDiv.Proofs.soundness (by decide) (by decide) (input operation) (output operation) (row operation)
  refine ⟨?_, satisfies operation, ?_⟩
  · constructor
    all_goals solve
      | (intro i; fin_cases operation <;> fin_cases i <;>
         dsimp [input, opcode, Airbender.MulDiv.Operation.selector, row] <;> decide)
      | (apply Reference.RiscV.Sail.read_register
         fin_cases operation <;> simp [input, Arithmetic.Word.toBitVec, Arithmetic.Word.value,
           Arithmetic.limbBase, Std.ExtDHashMap.get?_insert])
      | (constructor <;> fin_cases operation <;> dsimp [input, row] <;> decide)
  · constructor <;> fin_cases operation <;> dsimp [input, output, opcode, row] <;> decide

end Tests.MulDivProduct
