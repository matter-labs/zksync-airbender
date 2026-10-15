import Airbender.Review.Helpers.Decoder.ModularExternal
import Airbender.Review.Trace.NonDeterminism
import Airbender.Review.Helpers.Context.PooledBoundary

namespace Airbender.AddSub.Modular.External
open Trace
variable {p : Nat} [Fact p.Prime]
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- One actual decoded instruction, with the same independent stream throughout. -/
abbrev Step := NonDeterminism.StepWithClause decoderFields clause

abbrev ExecutionTrace (stream : List (BitVec 32)) (program : List PooledProgramEntry) :=
  Relation.ReflTransGen (Step stream program)

/-- Whole execution and exact input consumption, realizing native terminal cells. -/
def Realizes (stream : List (BitVec 32)) (program : List PooledProgramEntry)
    (trace : PooledTrace p) (initial : Reference.RiscV.Sail.State) (cells : List Cell)
    (view : MemoryToken p → MemoryToken p := id) : Prop :=
  ∃ after, ExecutionTrace stream program (initial, 0) (after, readCount trace) ∧
    Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) after =
      .ok trace.terminal.word.toBitVec after ∧
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.read after = .ok (view sink).word.toBitVec after

end Airbender.AddSub.Modular.External
