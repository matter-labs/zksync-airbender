import Airbender.Review.Trace.Modular.External
import Airbender.Review.Trace.UnifiedReduced.FullCalls

namespace Airbender.AddSub.Modular.External.Caller
open Trace Reference.RiscV.Sail Reference.Sail

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- A pooled delegated call retires the existing complete custom-operation
reference without consuming an external-input word. `allowed` selects the
public machine's supported worker families; split Keccak needs a distinct
reference branch when its native workers are modeled. -/
def CallStep (allowed : Delegation.Family → Prop)
    (callers : List Delegation.Caller.ProgramEntry)
    (before after : State × Nat) : Prop :=
  before.2 = after.2 ∧
    ∃ entry ∈ callers, allowed entry.data.family ∧
      entry.SourceWith before.1 Delegation.Caller.decoderFields ∧
      run (SailRV32.Functions.get_arch_pc ()) before.1 = .ok entry.pc before.1 ∧
      UnifiedReduced.Caller.FullRetirement entry.data.family before.1 after.1

/-- Ordinary pooled instructions, modular MOPs and external reads use the
existing stream clause. Complete delegated calls share the same Sail state and
preserve the stream position. -/
def Step (allowed : Delegation.Family → Prop)
    (stream : List (BitVec 32)) (program : List PooledProgramEntry)
    (callers : List Delegation.Caller.ProgramEntry)
    (before after : State × Nat) : Prop :=
  NonDeterminism.StepWithClause AddSub.Modular.External.decoderFields
      AddSub.Modular.External.clause stream program before after ∨
    CallStep allowed callers before after

/-- The unrolled reduced machine supports only the extended-round worker. -/
def reducedCall (family : Delegation.Family) : Prop := family = .blakeRound

/-- Only the four ordinary circuits present in the unrolled reduced setup may
produce a reduced-machine decoder row. The full pooled registry also contains
MUL/DIV and subword memory, so reusing it directly would overstate coverage. -/
def reducedFamily : PooledFamily → Bool
  | .addSub | .jumpBranchSlt | .shiftBinop | .wordMemory => true
  | .mulDiv | .subwordMemory => false

def reducedDecoderFields (instruction : SailRV32.instruction) :
    Option (DecoderData PooledFamily) :=
  (AddSub.Modular.External.decoderFields instruction).filter
    (fun data => reducedFamily data.family)

/-- The reduced setup admits the pooled stream/MOP/external clause and the
extended-round caller, but only after the native four-family filter. -/
def ReducedStep (stream : List (BitVec 32))
    (program : List PooledProgramEntry)
    (callers : List Delegation.Caller.ProgramEntry)
    (before after : State × Nat) : Prop :=
  NonDeterminism.StepWithClause reducedDecoderFields AddSub.Modular.External.clause
      stream program before after ∨
    CallStep reducedCall callers before after

/-- Both unrolled machines retain the exact external-read count and native
terminal observations. The full unsigned target must extend this relation with
the three blessed split Keccak workers before claiming production coverage. -/
def Realizes {p : Nat} [Fact p.Prime] (allowed : Delegation.Family → Prop)
    (stream : List (BitVec 32)) (program : List PooledProgramEntry)
    (callers : List Delegation.Caller.ProgramEntry)
    (trace : PooledTrace p) (initial : State) (cells : List Cell)
    (view : MemoryToken p → MemoryToken p := id) : Prop :=
  ∃ after, Relation.ReflTransGen (Step allowed stream program callers)
      (initial, 0) (after, NonDeterminism.Pooled.readCount trace) ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.read after = .ok (view sink).word.toBitVec after

/-- Reduced execution uses the same native stream count and terminal memory
observations, with no step from the absent MUL/DIV or subword circuits. -/
def ReducedRealizes {p : Nat} [Fact p.Prime]
    (stream : List (BitVec 32)) (program : List PooledProgramEntry)
    (callers : List Delegation.Caller.ProgramEntry)
    (trace : PooledTrace p) (initial : State) (cells : List Cell)
    (view : MemoryToken p → MemoryToken p := id) : Prop :=
  ∃ after, Relation.ReflTransGen (ReducedStep stream program callers)
      (initial, 0) (after, NonDeterminism.Pooled.readCount trace) ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.read after = .ok (view sink).word.toBitVec after

end Airbender.AddSub.Modular.External.Caller
