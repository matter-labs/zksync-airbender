import Airbender.Review.Trace.Execution
import Airbender.Review.Helpers.Memory.ShadowImage
import Airbender.Review.Helpers.Decoder.Instruction
import Airbender.Review.Helpers.Decoder.WordMemory

namespace Airbender.WordMemory
open Trace Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem

/-- Original fetched/decoded Sail LW/SW, including actual memory reads for x0. -/
abbrev SailStep [MemoryPlatform SailRV32.exception] := StepWith WordMemory.decoderFields instructionClause

/-- Finite original Sail execution with the native terminal PC and architectural
    terminal cells. ROM-shadow tokens stay in accepted native matching; their
    independent values are not interpreted as architectural ROM bytes. -/
def Realizes [MemoryPlatform SailRV32.exception] {p : Nat} [Fact p.Prime]
    (program : List (ProgramEntry WordMemoryFamily)) (trace : Data p WordMemoryFamily)
    (initial : State) (cells : List Cell) : Prop :=
  ∃ after, Relation.ReflTransGen (WordMemory.SailStep program) initial after ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
    ∀ sink ∈ trace.terminalMemory, architecturalAddress sink.address = true →
      ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok sink.word.toBitVec after

end Airbender.WordMemory
