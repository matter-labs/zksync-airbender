module
public import Human.Circuits.Bigint.Memory
public import Slop.Bigint.Addresses
public import Slop.Bigint.NativeExecution
public import Slop.Bigint.WitnessCheck
public import Slop.KernelRfl

@[expose] public section

namespace Tests.BigintAbi
open Airbender
set_option warningAsError true

def row (withOpcode : Bool) (high : Nat) : Nat → ZMod babyBearModulus
  | 0 | 212 | 214 | 215 => 1
  | 55 | 59 => if withOpcode then 1 else 0
  | 56 => high
  | _ => 0

abbrev setup : Table (ZMod babyBearModulus) (fields 3) := Bigint.setupTable

theorem abiRowsSatisfy (withOpcode : Bool) (high : Nat) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row withOpcode high))
      (Bigint.importedConstraints setup) := by
  cases withOpcode <;> exact Bigint.holds_of_check (by kernel_rfl)

theorem noOpcodeSatisfies (high : Nat) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row false high))
      (Bigint.importedConstraints setup) := abiRowsSatisfy false high

theorem activeWithoutOpcode :
    row false 0 Bigint.Variables.controlBits[0] = 0 ∧ row false 0 0 = 1 ∧
    (row false 0 55).val = 0 ∧
    (∑ i : Fin 7, (row false 0 Bigint.Variables.operations[i]).val) = 0 := by
  simp [row, Bigint.Variables.controlBits, Bigint.Variables.operations, Fin.sum_univ_succ]

theorem validOpcodeHighAccepted :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row true 1))
      (Bigint.importedConstraints setup) ∧
    (row true 1 55).val = 1 ∧ (row true 1 56).val = 1 :=
  ⟨abiRowsSatisfy true 1, by decide, by decide⟩

end Tests.BigintAbi
