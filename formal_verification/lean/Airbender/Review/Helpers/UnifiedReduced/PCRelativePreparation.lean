import Airbender.Review.Helpers.UnifiedReduced.ControlPreparation
import Airbender.Review.Helpers.UnifiedReduced.WindowSchedule

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic Reference.RiscV.Sail

/-- The prepared word is RV32 addition of the derived public instruction address
    and the U-immediate. It is computed from code, never supplied as an output. -/
def pcRelativeControl [Fact p.Prime] (data : RequestTrace p) (cut : Nat) (immediate : BitVec 20) : BitVec 32 :=
  wrappedProgramAddress data (cut - 4) + (immediate ++ (0 : BitVec 12))

/-- Public modular sequential/comparison code identifies a final AUIPC. Only its
    final cycle is worker-free; earlier issued and unissued effects remain. -/
structure PCRelativePreparation [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (cut : Nat) (register : BitVec 5) (immediate : BitVec 20) : Prop where
  registry : WrappedSequentialProgram program
  atCut : ∀ entry ∈ program, entry.pc = wrappedProgramAddress data (cut - 4) →
    entry.instruction = .UTYPE (immediate, .Regidx register, .AUIPC)
  prefixScope : data.workers.windowRows (cut - 4) cut = []
  afterInitial : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut
  beforeTerminal : cut ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- The actual AUIPC cut state and canonical native token retain the write clock.
    No desired read, row selector or control-validity condition is an input. -/
def PCRelativePreparedControl [Fact p.Prime] (data : RequestTrace p)
    (tokens : List (MemoryToken p)) (state : State) (cut : Nat) (register : BitVec 5) (immediate : BitVec 20) : Prop :=
  (Cell.register register).read state = .ok (pcRelativeControl data cut immediate) state ∧
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧
      (timeOfPair token.time).value = cut - 2 ∧ token.word = Word.ofBitVec (pcRelativeControl data cut immediate)

end Airbender.UnifiedReduced.Caller
