import Airbender.Proofs.Keccak.SplitChiRegisters

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384
variable [Fact babyBearModulus.Prime]

/-- The actual readonly pointer-register port. -/
def chi5PointerPort (cached : Bool) : MemoryPort :=
  let ports := (⟨.chi5, fun _ => 0⟩ : Row babyBearModulus).ports cached
  ports[1]'(by cases cached <;> change 1 < 12 <;> decide)

/-- Register eleven refreshes its exact raw pointer value. -/
theorem chi5_pointer_port (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    (chi5PointerPort cached).address = .constantRegister 11 ∧
      (chi5PointerPort cached).readCode w = Nat.pair (chi5Pointer cached w)[0].val (chi5Pointer cached w)[1].val ∧
      (chi5PointerPort cached).writeCode w = (chi5PointerPort cached).readCode w := by
  cases cached <;> exact ⟨rfl, rfl, rfl⟩

/-- The complete native port array contains exactly both registers and all ten lane halves. -/
theorem chi5_ports_enumeration (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    ((⟨.chi5, w⟩ : Row babyBearModulus).ports cached).toList =
      [chi5ControlPort cached, chi5PointerPort cached] ++
        (List.finRange 5).flatMap (fun lane => [chi5LanePort cached lane false, chi5LanePort cached lane true]) := by
  cases cached <;> rfl

end Airbender.Keccak.Split.Native.Proofs
