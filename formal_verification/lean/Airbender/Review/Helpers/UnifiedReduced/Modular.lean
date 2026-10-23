import Airbender.Review.Helpers.UnifiedReduced.Program
import Airbender.Review.Circuits.AddSub.Modular.Decoder

namespace Airbender.UnifiedReduced.Modular
open Trace

/-- Unified F1 retains standalone modular selector bits 3–6 and x0 preprocessing. -/
def mopData (opcode : AddSub.Modular.Opcode) (rs1 rs2 rd : BitVec 5) : DecoderData UnifiedFamily :=
  (AddSub.Modular.nativeData opcode rs1 rs2 rd).mapFamily (fun _ => .machine)

def mopDecoderFields : SailRV32.instruction → Option (DecoderData UnifiedFamily)
  | .ZIMOP_MOP_RR (mop, .Regidx rs2, .Regidx rs1, .Regidx rd) => do
    let opcode ← AddSub.Modular.opcodeOfMop mop
    pure (mopData opcode rs1 rs2 rd)
  | _ => none

/-- One public registry for existing standard/TRIADD/XORROT and all four modular forms. -/
def decoderFields (instruction : SailRV32.instruction) : Option (DecoderData UnifiedFamily) :=
  Mixed.decoderFields instruction <|> mopDecoderFields instruction

abbrev programImage := programImageRunWith decoderFields
abbrev Inputs {p : Nat} [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] :=
  ExecutionInputsWith (p := p) decoderFields

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

def mopClause : SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult)
  | .ZIMOP_MOP_RR (mop, .Regidx rs2, .Regidx rs1, .Regidx rd) => do
    let opcode ← AddSub.Modular.opcodeOfMop mop
    pure (AddSub.Modular.clause opcode rs1 rs2 rd)
  | _ => none

def clauseFor (instruction : SailRV32.instruction) : Option (SailRV32.SailM SailRV32.ExecutionResult) :=
  Mixed.clauseFor instruction <|> mopClause instruction

end Airbender.UnifiedReduced.Modular
