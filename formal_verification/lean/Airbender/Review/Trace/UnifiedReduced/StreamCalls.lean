import Airbender.Review.Trace.NonDeterminism
import Airbender.Review.Trace.UnifiedReduced.Modular
import Airbender.Review.Trace.UnifiedReduced.FullCalls
import Airbender.Review.Helpers.Decoder.ExternalInput

namespace Airbender.UnifiedReduced.Caller.Stream
open Airbender.Trace Reference.RiscV.Sail Reference.Sail

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Only the external-input CSR forms are added to the unified modular registry.
Other CSR addresses, including delegation, remain in their separate caller
registry. The shared unified circuit uses one family tag for every operation. -/
def externalDecoderFields : SailRV32.instruction → Option (DecoderData UnifiedFamily)
  | instruction@(.CSRReg (csr, _, _, .CSRRW)) =>
    if csr = 0x7C0 then
      (NonDeterminism.decoderFields instruction).map
        (DecoderData.mapFamily (fun _ => .machine))
    else none
  | _ => none

/-- The combined noncaller metadata registry. The external CSR branch has no
overlap with the ordinary/modular branch; disjointness is a proof obligation. -/
def decoderFields (instruction : SailRV32.instruction) : Option (DecoderData UnifiedFamily) :=
  UnifiedReduced.Modular.decoderFields instruction <|> externalDecoderFields instruction

def externalClause (stream : List (BitVec 32)) (position : Nat) :
    SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult × Nat)
  | instruction@(.CSRReg (csr, _, _, .CSRRW)) =>
    if csr = 0x7C0 then NonDeterminism.clause stream position instruction .sail else none
  | _ => none

/-- Ordinary and modular instructions preserve the stream position; only a
successful external read advances it. -/
def clauseFor (stream : List (BitVec 32)) (position : Nat)
    (instruction : SailRV32.instruction) :
    Option (SailRV32.SailM SailRV32.ExecutionResult × Nat) :=
  (UnifiedReduced.Modular.clauseFor instruction).map (fun clause => (clause, position)) <|>
    externalClause stream position instruction

/-- A caller retires its complete custom-operation reference and leaves the
external-input stream position unchanged. -/
def CallStep (callers : List Delegation.Caller.ProgramEntry)
    (before after : State × Nat) : Prop :=
  before.2 = after.2 ∧
    ∃ entry ∈ callers, entry.SourceWith before.1 Delegation.Caller.decoderFields ∧
      run (SailRV32.Functions.get_arch_pc ()) before.1 = .ok entry.pc before.1 ∧
      FullRetirement entry.data.family before.1 after.1

/-- Unified machine step with one stream and the existing complete caller
reference. Caller and noncaller branches share the same public fetch state. -/
def Step (stream : List (BitVec 32))
    (program : List (Trace.ProgramEntry UnifiedFamily))
    (callers : List Delegation.Caller.ProgramEntry)
    (before after : State × Nat) : Prop :=
  NonDeterminism.StepWithClause decoderFields clauseFor stream program before after ∨
    CallStep callers before after

/-- A finite unified execution with explicit stream consumption and the same
terminal PC and tracked-cell agreement as `Trace.Realizes`. The machine target
must bind `consumed` to the native external-read rows. -/
def Realizes {p : Nat} [Fact p.Prime] (stream : List (BitVec 32))
    (program : List (Trace.ProgramEntry UnifiedFamily))
    (callers : List Delegation.Caller.ProgramEntry)
    (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (consumed : Nat)
    (view : MemoryToken p → MemoryToken p := id) : Prop :=
  ∃ after, Relation.ReflTransGen (Step stream program callers)
      (initial, 0) (after, consumed) ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.read after = .ok (view sink).word.toBitVec after

end Airbender.UnifiedReduced.Caller.Stream
