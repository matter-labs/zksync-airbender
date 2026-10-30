import Airbender.Proofs.Keccak.SplitThetaRegisters

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
variable [Fact babyBearModulus.Prime]

/-- The actual readonly pointer-register port. -/
def thetaPointerPort (cached : Bool) : MemoryPort :=
  let ports := (⟨.thetaRho, fun _ => 0⟩ : Row babyBearModulus).ports cached
  ports[1]'(by cases cached <;> change 1 < 16 <;> decide)

/-- Register eleven refreshes its exact raw pointer value. -/
theorem theta_pointer_port (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    (thetaPointerPort cached).address = .constantRegister 11 ∧
      (thetaPointerPort cached).readCode w = Nat.pair (thetaPointer cached w)[0].val (thetaPointer cached w)[1].val ∧
      (thetaPointerPort cached).writeCode w = (thetaPointerPort cached).readCode w := by
  cases cached <;> exact ⟨rfl, rfl, rfl⟩

/-- The complete native port array contains exactly both registers and all fourteen lane halves. -/
theorem theta_ports_enumeration (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    ((⟨.thetaRho, w⟩ : Row babyBearModulus).ports cached).toList =
      [thetaControlPort cached, thetaPointerPort cached] ++
        (List.finRange 7).flatMap (fun lane => [thetaLanePort cached lane false, thetaLanePort cached lane true]) := by
  cases cached <;> rfl

end Airbender.Keccak.Split.Native.Proofs
