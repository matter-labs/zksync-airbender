import Airbender.Review.Helpers.UnifiedReduced.ControlPreparation

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic Reference.RiscV.Sail

/-- Original public writes whose value comes from the instruction and, for
    AUIPC, the actual occurrence's PC. -/
inductive PathWrite where
  | literal (literal : ControlLiteral)
  | auipc (immediate : BitVec 20)

def PathWrite.instruction (write : PathWrite) (register : BitVec 5) : SailRV32.instruction :=
  match write with
  | .literal payload => payload.instruction register
  | .auipc immediate => .UTYPE (immediate, .Regidx register, .AUIPC)

def PathWrite.value (write : PathWrite) (pc : BitVec 32) : BitVec 32 :=
  match write with
  | .literal payload => payload.value
  | .auipc immediate => pc + (immediate ++ (0 : BitVec 12))

/-- Public decoded code covers the actual occurrence ending at this cut.
    Distinct cuts may revisit the same PC. No affine PC/clock registry, native
    selector, worker-free window, operand read or expected output is supplied. -/
structure PathPreparation [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (cut : Nat)
    (register : BitVec 5) (write : PathWrite) : Prop where
  /-- Syntactic code coverage at the actual accepted PC/clock occurrence. -/
  code : ∀ row ∈ data.machine.rows, Delegation.Caller.startClock row + 4 = cut →
    ∃ entry ∈ program, entry.pc = row.start.word.toBitVec ∧
      entry.instruction = write.instruction register
  afterInitial : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut
  beforeTerminal : cut ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- A preparation's actual public instruction address, canonical control token
    and architectural read. These are conclusions of the native path and memory
    adapters, including the token's exact write timestamp. -/
def PathPreparedControl [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (tokens : List (MemoryToken p))
    (state : State) (cut : Nat) (register : BitVec 5) (write : PathWrite) : Prop :=
  ∃ row ∈ data.machine.rows, Delegation.Caller.startClock row + 4 = cut ∧
    ∃ entry ∈ program, entry.pc = row.start.word.toBitVec ∧
      entry.instruction = write.instruction register ∧
      (Cell.register register).read state = .ok (write.value entry.pc) state ∧
      ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧
        (timeOfPair token.time).value = cut - 2 ∧
        token.word = Word.ofBitVec (write.value entry.pc)

end Airbender.UnifiedReduced.Caller
