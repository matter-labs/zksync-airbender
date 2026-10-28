import Airbender.Review.Trace.NonDeterminism
import Airbender.Review.Trace.UnifiedReduced.Modular
import Airbender.Review.Trace.UnifiedReduced.FullCalls
import Airbender.Review.Trace.UnifiedReduced.DelegationUse
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

/-- Native selector bit eight marks the external-input read. The unified
artifact has nineteen decoder flags; this bit has the same meaning as in the
ADD/SUB family. -/
def isRead {p : Nat} (row : Trace.Row p UnifiedFamily) : Bool :=
  row.assignment UnifiedReduced.importedConstraintsDecoderColumns.flags[8] == 1

/-- The selected read's native destination port carries the external word. -/
def response {p : Nat} (row : Trace.Row p UnifiedFamily) : BitVec 32 :=
  (writeToken UnifiedReduced.importedConstraintsTraceColumns row.assignment
    UnifiedReduced.importedConstraintsMemoryPorts[2]).word.toBitVec

/-- Count external reads in native clock order, independently of witness-list
order. Complete calls and ordinary instructions consume no stream words. -/
def readCount {p : Nat} [Fact p.Prime] (trace : UnifiedTrace p) : Nat :=
  ExternalStream.count isRead trace.rows

/-- Bind native read responses to one independently supplied stream. This is
an explicit input boundary; native constraints do not authenticate the stream. -/
def StreamPorts {p : Nat} [Fact p.Prime] (trace : UnifiedTrace p)
    (stream : List (BitVec 32)) : Prop :=
  ExternalStream.Ports Trace.Row.clock isRead response trace.rows stream

/-- A finite unified execution with explicit stream consumption and the same
terminal PC and tracked-cell agreement as `Trace.Realizes`. -/
def Realizes {p : Nat} [Fact p.Prime] (stream : List (BitVec 32))
    (program : List (Trace.ProgramEntry UnifiedFamily))
    (callers : List Delegation.Caller.ProgramEntry)
    (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell)
    (view : MemoryToken p → MemoryToken p := id) : Prop :=
  ∃ after, Relation.ReflTransGen (Step stream program callers)
      (initial, 0) (after, readCount trace) ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.read after = .ok (view sink).word.toBitVec after

/-- Public reachability for a fixed stream, with the consumed position carried
through every instruction and complete delegated call. -/
def Reachable (stream : List (BitVec 32)) (program : DelegationUse.Program)
    (initial : State) (state : State × Nat) : Prop :=
  Relation.ReflTransGen (Step stream program.ordinary program.callers) (initial, 0) state

/-- Supported wrapper use for every possible external stream. The quantified
stream is not a witness premise: public code and initial state must satisfy the
entry and argument conditions regardless of external input values. The current
wrapper registry contains bigint, BLAKE2 G and extended round; split Keccak
requires its separate full unsigned extension. -/
structure ValidDelegationUse (program : DelegationUse.Program) (initial : State) : Prop where
  shapes : DelegationUse.Shapes program
  initialEntry : ∀ bundle ∈ program.bundles, ∀ index : Fin bundle.instructions,
    0 < index.val → ¬ DelegationUse.AtPC initial (bundle.instructionPC index.val)
  entry : ∀ stream before after, Reachable stream program initial before →
    Step stream program.ordinary program.callers before after →
    ∀ bundle ∈ program.bundles, ∀ index : Fin bundle.instructions,
      0 < index.val → DelegationUse.AtPC after.1 (bundle.instructionPC index.val) →
        DelegationUse.AtPC before.1 (bundle.instructionPC (index.val - 1))
  arguments : ∀ stream state, Reachable stream program initial state →
    ∀ bundle ∈ program.bundles, ∀ index : Fin bundle.kind.calls,
      DelegationUse.AtPC state.1 (bundle.callPC index.val) →
        DelegationUse.ArgumentsAt bundle index.val state.1

end Airbender.UnifiedReduced.Caller.Stream
