import Airbender.Review.UnifiedReduced.XorRotate
import Airbender.Review.Trace.Execution

namespace Airbender.UnifiedReduced.Custom
open Trace Reference.RiscV.Sail

/-- The pinned project operations, dispatched from original Sail MOP constructors.
    The bodies are the same clauses used by the per-circuit soundness claims.
    Unsupported MOPs have no clause; this does not substitute Zimop's fallback. -/
def clauseFor : SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult)
  | .ZIMOP_MOP_RR (mop, rs2, rs1, rd) =>
    if mop = 4 then some (TriAdd.clause rs1 rs2 rd) else none
  | .ZIMOP_MOP_R (mop, rs1, rd) =>
    if mop = 16 ∨ mop = 12 ∨ mop = 8 ∨ mop = 7 then
      some (XorRotate.clause mop.toNat rs1 rd) else none
  | _ => none

/-- Actual public fetch, original Sail decoding and retirement of one supported
    project instruction. The reference clause depends only on the fetched AST. -/
abbrev Step := StepWith customDecoderFields clauseFor

/-- Public initialization, actual program bytes/decoding, clocks and modeled
    tables. Code addresses lie in aligned readonly ROM. Initialized history
    supplies reads, word ranges, instruction order and terminal values. The
    admitted custom decoder profile excludes discarded x0 destinations. -/
structure Inputs [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry) : Prop where
  initialization : NativeInputs customDecoderFields trace initial cells program
  setup : trace.rom = Setup.table initial
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0

end Airbender.UnifiedReduced.Custom
