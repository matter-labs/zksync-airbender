import Airbender.Review.Circuits.AddSub.Modular.Decoder
import Airbender.Review.Helpers.Decoder.PooledProgram
import Airbender.Review.Helpers.Decoder.Instruction

namespace Airbender.AddSub.Modular.Pooled
open Trace

/-- Extend the six-family registry with the four modular ADD/SUB operations. -/
def decoderFields (instruction : SailRV32.instruction) : Option (DecoderData PooledFamily) :=
  (Modular.decoderFields instruction).map (DecoderData.mapFamily pooledArithmeticFamily) <|>
  pooledDecoderFields instruction

abbrev programImage := programImageRunWith decoderFields

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Use project modular semantics for MOP.RR.0–3 and original Sail elsewhere. -/
def clauseFor (instruction : SailRV32.instruction) :
    Option (SailRV32.SailM SailRV32.ExecutionResult) :=
  match instruction with
  | .ZIMOP_MOP_RR (mop, .Regidx rs2, .Regidx rs1, .Regidx rd) => do
    let opcode ← opcodeOfMop mop
    pure (clause opcode rs1 rs2 rd)
  | original => instructionClause original

end Airbender.AddSub.Modular.Pooled
