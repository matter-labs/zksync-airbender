import Airbender.Proofs.Keccak.SplitParityRegisters

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384
variable [Fact babyBearModulus.Prime]

/-- The actual readonly pointer-register port. -/
def parityPointerPort (cached : Bool) : MemoryPort :=
  let ports := (⟨.columnParity, fun _ => 0⟩ : Row babyBearModulus).ports cached
  ports[1]'(by cases cached <;> change 1 < 14 <;> decide)

/-- Register eleven refreshes its exact raw pointer value. -/
theorem parity_pointer_port (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    (parityPointerPort cached).address = .constantRegister 11 ∧
      (parityPointerPort cached).readCode w = Nat.pair (parityPointer cached w)[0].val (parityPointer cached w)[1].val ∧
      (parityPointerPort cached).writeCode w = (parityPointerPort cached).readCode w := by
  cases cached <;> exact ⟨rfl, rfl, rfl⟩

/-- The complete native port array contains exactly both registers and all twelve lane halves. -/
theorem parity_ports_enumeration (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    ((⟨.columnParity, w⟩ : Row babyBearModulus).ports cached).toList =
      [parityControlPort cached, parityPointerPort cached] ++
        (List.finRange 6).flatMap (fun lane => [parityLanePort cached lane false, parityLanePort cached lane true]) := by
  cases cached <;> rfl

end Airbender.Keccak.Split.Native.Proofs
