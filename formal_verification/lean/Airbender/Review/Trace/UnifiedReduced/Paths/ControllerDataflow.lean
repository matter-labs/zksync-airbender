import Airbender.Review.Helpers.UnifiedReduced.PathDataflow
import Airbender.Review.Helpers.Delegation.SpanABI
import Airbender.Review.Trace.Workers.Blake2Round.Call
import Airbender.Review.Trace.Workers.Keccak.Call

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic Reference.RiscV.Sail

/-- A public position in any complete existing hash protocol. Every controller
    index is admitted; native reads and supported masks are derived separately. -/
structure HashCallPosition where
  span : Delegation.Caller.HashSpan
  index : Fin span.callCount

def HashCallPosition.keccakControl (index : Fin 649) : Keccak.ControlState :=
  Keccak.scheduleControl ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩

def HashCallPosition.word : HashCallPosition → Word
  | ⟨.blakeG reduced, index⟩ => Blake2G.controlAt reduced index.val
  | ⟨.blakeRound flags, index⟩ => Blake2Round.controlAt flags index.val
  | ⟨.keccak, index⟩ => ⟨(HashCallPosition.keccakControl index).packed, 0⟩

def HashCallPosition.nextWord : HashCallPosition → Word
  | ⟨.blakeG reduced, index⟩ => (Blake2G.Control.step (Blake2G.controllerAt reduced index.val)).register
  | ⟨.blakeRound flags, index⟩ => Blake2Round.Control.next (Blake2Round.controlAt flags index.val)
  | ⟨.keccak, index⟩ => ⟨(HashCallPosition.keccakControl index).nextPacked, 0⟩

/-- The only GPR a worker can change. Pointer reads and RAM writes retain their
    own native effects; this name does not assert any frame theorem. -/
def callerControlRegister : Delegation.Family → BitVec 5
  | .keccak => 10
  | .bigint | .blakeG | .blakeRound => 12

/-- Public CSR code at an actual clock/PC occurrence. Original byte decoding,
    caller selection, family matching and the unique worker are proof outputs. -/
structure PathCallerPreparation [Fact p.Prime] (data : RequestTrace p)
    (cut : Nat) (family : Delegation.Family) : Prop where
  code : ∀ row ∈ data.machine.rows, Delegation.Caller.startClock row + 4 = cut →
    ∃ entry ∈ data.program, entry.pc = row.start.word.toBitVec ∧ entry.data.family = family
  afterInitial : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut
  beforeTerminal : cut ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- Public controller computations with genuine native calls between ordinary
    gaps. Hash advancement records the independent controller function, whose
    actual read/write token binding must be proved from accepted matching.
    No constructor accepts a desired native read, valid mask or complete call. -/
inductive PathControllerDataflow [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) : Nat → BitVec 5 → BitVec 32 → Prop where
  | ordinary {cut register value}
      (flow : PathRegisterDataflow data program cut register value) :
      PathControllerDataflow data program cut register value
  | addi {cut source register value immediate}
      (prior : PathControllerDataflow data program (cut - 4) source value)
      (scope : PathInstructionPreparation data program cut
        (.ITYPE (immediate, .Regidx source, .Regidx register, .ADDI)))
      (sourceNonzero : source ≠ 0) :
      PathControllerDataflow data program cut register (registerImmediateValue value immediate)
  | frame {cut register value instruction}
      (prior : PathControllerDataflow data program (cut - 4) register value)
      (scope : PathInstructionPreparation data program cut instruction)
      (form : PathRegisterFrame register instruction) :
      PathControllerDataflow data program cut register value
  | callerFrame {cut register value family}
      (prior : PathControllerDataflow data program (cut - 4) register value)
      (scope : PathCallerPreparation data cut family)
      (different : register ≠ callerControlRegister family) :
      PathControllerDataflow data program cut register value
  | hashAdvance {cut} (position : HashCallPosition)
      (prior : PathControllerDataflow data program (cut - 4)
        position.span.controlRegister position.word.toBitVec)
      (scope : PathCallerPreparation data cut position.span.family) :
      PathControllerDataflow data program cut position.span.controlRegister position.nextWord.toBitVec

end Airbender.UnifiedReduced.Caller
