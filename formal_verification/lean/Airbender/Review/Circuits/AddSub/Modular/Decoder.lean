import Airbender.Review.Circuits.AddSub.Modular
import Airbender.Review.Helpers.Decoder.Program

namespace Airbender.AddSub.Modular
open Trace

def Opcode.mop : Opcode → BitVec 3
  | .add => 0 | .sub => 1 | .mul => 2 | .fma => 3

def opcodeOfMop (mop : BitVec 3) : Option Opcode :=
  if mop = 0 then some .add else if mop = 1 then some .sub
  else if mop = 2 then some .mul else if mop = 3 then some .fma else none

/-- Original Sail Zimop AST selecting the pinned project's arithmetic. -/
def instruction (opcode : Opcode) (rs1 rs2 rd : BitVec 5) : SailRV32.instruction :=
  .ZIMOP_MOP_RR (opcode.mop, .Regidx rs2, .Regidx rs1, .Regidx rd)

/-- Native ADD/SUB selector bits 3–6; discarded writes use its existing NOP. -/
def nativeData (opcode : Opcode) (rs1 rs2 rd : BitVec 5) : DecoderData :=
  arithmeticFields rs1 rs2 rd 0 (2 ^ (opcode.selector - 10))

/-- Public Sail decoding supplies MOP.RR.0–3. Only native metadata is added;
    arithmetic behavior remains the pinned project specification. -/
def decoderFields : SailRV32.instruction → Option DecoderData
  | .ZIMOP_MOP_RR (mop, .Regidx rs2, .Regidx rs1, .Regidx rd) => do
    let opcode ← opcodeOfMop mop
    pure (nativeData opcode rs1 rs2 rd)
  | original => Trace.decoderFields original

/-- The existing custom execution body depends only on this decoded AST. -/
abbrev clause (opcode : Opcode) (rs1 rs2 rd : BitVec 5) :=
  execution ⟨opcode, 0, 0, 0, .Regidx rs1, .Regidx rs2, .Regidx rd, ⟨0, 0⟩, default⟩

end Airbender.AddSub.Modular
