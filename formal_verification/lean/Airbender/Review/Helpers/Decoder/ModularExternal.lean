import Airbender.Review.Helpers.Decoder.ModularProgram
import Airbender.Review.Helpers.Decoder.PooledExternalInput

namespace Airbender.AddSub.Modular.External
open Trace

/-- Public MOP.RR.0–3 metadata and the existing external-input CSR forms. -/
def arithmeticDecoderFields : SailRV32.instruction → Option DecoderData
  | original@(.ZIMOP_MOP_RR _) => Modular.decoderFields original
  | original => NonDeterminism.decoderFields original

/-- One registry for modular arithmetic, reads/hints and all six ordinary families. -/
def decoderFields (instruction : SailRV32.instruction) : Option (DecoderData PooledFamily) :=
  (arithmeticDecoderFields instruction).map (DecoderData.mapFamily pooledArithmeticFamily) <|>
    pooledDecoderFields instruction

abbrev programImage := programImageRunWith decoderFields
abbrev isRead {p : Nat} [Fact p.Prime] := NonDeterminism.Pooled.isRead (p := p)
abbrev response {p : Nat} [Fact p.Prime] := NonDeterminism.Pooled.response (p := p)
abbrev readIndex {p : Nat} [Fact p.Prime] := NonDeterminism.Pooled.readIndex (p := p)
abbrev readCount {p : Nat} [Fact p.Prime] := NonDeterminism.Pooled.readCount (p := p)
abbrev StreamPorts {p : Nat} [Fact p.Prime] := NonDeterminism.Pooled.StreamPorts (p := p)

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Modular instructions preserve the stream position; reads/hints retain their
    existing pinned clauses and standard instructions retain original Sail. -/
def clause (stream : List (BitVec 32)) (position : Nat) : SailRV32.instruction →
    Option (SailRV32.SailM SailRV32.ExecutionResult × Nat)
  | .ZIMOP_MOP_RR (mop, .Regidx rs2, .Regidx rs1, .Regidx rd) => do
    let opcode ← opcodeOfMop mop
    pure (Modular.clause opcode rs1 rs2 rd, position)
  | original => NonDeterminism.clause stream position original .sail

end Airbender.AddSub.Modular.External
