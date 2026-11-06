import Airbender.Review.Circuits.ReducedMachine.ShiftWrite
import Airbender.Review.Helpers.Core.Word

namespace Airbender.ReducedMachine.Native
open Arithmetic

/-- Incoming and outgoing PC words at the actual imported native columns. -/
def initialPCWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 0).val,(w 1).val⟩

def finalPCWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 13).val,(w 14).val⟩

/-- Numerical PC increment only; original preparation, retirement and fetched
    instruction execution remain separate from this RV32 successor property. -/
def ShiftPCSuccessor (w : Nat → ZMod mersenne31Modulus) : Prop :=
  (initialPCWord w).Bounded ∧ (initialPCWord w).lo % 4 = 0 ∧
  (finalPCWord w).Bounded ∧ (finalPCWord w).toBitVec = (initialPCWord w).toBitVec + 4

end Airbender.ReducedMachine.Native
