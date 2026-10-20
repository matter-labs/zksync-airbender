import Airbender.Review.Circuits.ShiftBinop.Decoder
import Airbender.Review.Circuits.ShiftBinop.Artifact

namespace Airbender.ShiftBinop
open Arithmetic
set_option autoImplicit false

/-- Original RV32 funct3, distinct from the six-bit native operation mask. -/
def Operation.funct3 : Operation → Nat
  | .sll => 1 | .srl | .sra => 5 | .xor => 4 | .or => 6 | .and => 7

def Operation.isBinary : Operation → Bool
  | .xor | .or | .and => true | _ => false

/-- Actual native slot order: SRA's sign-fill precedes its two logical contributions. -/
def Operation.lookupTags : Operation → Vector Nat 4
  | .sll => #v[47,48,49,0]
  | .srl => #v[47,50,51,0]
  | .sra => #v[47,52,50,51]
  | .xor => #v[4,4,4,4]
  | .or => #v[6,6,6,6]
  | .and => #v[7,7,7,7]

abbrev decoderQuery {p : Nat} (w : Nat → ZMod p) :=
  Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

/-- Native routing observables. These are conclusions derived from acceptance and
    public original decoding, never extra circuit-acceptance premises. -/
structure Routing (w : Nat → ZMod mersenne31Modulus) (entry : ProgramEntry) : Prop where
  tags : ∀ slot : Fin 4, w (42 + 4 * slot.val) = entry.data.family.lookupTags[slot.val]
  operandLow : w 27 = if 32 ≤ entry.data.mask then w 9 else w 25
  operandHigh : w 28 = if 32 ≤ entry.data.mask then w 10 else w 26
  delegationDisabled : w 37 = 0

end Airbender.ShiftBinop
