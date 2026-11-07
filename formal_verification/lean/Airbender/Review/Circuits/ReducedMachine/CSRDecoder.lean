import Airbender.Review.Circuits.ReducedMachine.CSR
import Airbender.Review.Circuits.ReducedMachine.Decoder

namespace Airbender.ReducedMachine.Native
open Arithmetic
abbrev CSRMode := Unit

/-- Original register CSRRW only, with raw rs1/rd, readonly rs2=x0 and the
    unsigned 12-bit CSR index. This projection does not assert CSR execution,
    a runtime allow-list or equality with the retained native ROM image. -/
def csrDecoderFields : SailRV32.instruction → Option (Trace.DecoderData CSRMode)
  | .CSRReg (index,.Regidx rs1,.Regidx rd,.CSRRW) =>
    some ⟨(),rs1,0,rd,⟨index.toNat,0⟩,csrMask,1⟩
  | _ => none

abbrev CSRProgramEntry := Trace.ProgramEntry CSRMode
abbrev csrDecoderSetupImage := Trace.sparseDecoderSetupImageRunWith csrDecoderFields

/-- All actual native fields at a recovered original public CSR entry. -/
structure CSRDecoded (w : Nat → ZMod mersenne31Modulus) (entry : CSRProgramEntry) : Prop where
  mask : w 12 = (csrMask : ZMod mersenne31Modulus)
  rs1 : w 5 = (entry.data.rs1.toNat : ZMod mersenne31Modulus)
  rs2 : w 6 = 0
  rd : rdIndex w = (entry.data.rd.toNat : ZMod mersenne31Modulus)
  zero : rdZeroFlag w = (if entry.data.rd = 0 then 1 else 0)
  immediate : #v[w 9,w 10] = #v[(entry.data.immediate.lo : ZMod mersenne31Modulus),0]
  funct3 : w 11 = 1
end Airbender.ReducedMachine.Native
