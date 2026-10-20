import Human.Helpers.Decoder.Instruction
import Human.Helpers.Context.Boundary
import Mathlib.Logic.Relation

namespace Airbender.Trace
open Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

/-- One successful instruction from Sail state `before` to `after`. `program`
    holds entries built from public bytes; `projection` selects native decoder
    metadata and `clauseFor` selects the original Sail execution clause or a
    named profile deviation.

    Fetch/decoding must succeed in `before`, its PC must match the entry, and
    Sail preparation, execution and retirement must reach `after`. This is the
    reference relation proved by soundness, not an assumed circuit result. -/
def StepWith {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (clauseFor : SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult))
    (program : List (ProgramEntry Kind)) (before after : State) : Prop :=
  ∃ entry ∈ program, entry.SourceWith before projection ∧
    run (SailRV32.Functions.get_arch_pc ()) before = .ok entry.pc before ∧
    ∃ clause, clauseFor entry.instruction = some clause ∧
      run (normalStep clause) before = .ok SailRV32.Functions.RETIRE_SUCCESS after

/-- The shared conclusion of trace soundness. Starting at public Sail state
    `initial`, a finite sequence of `step` reaches an `after` state whose PC
    and tracked register/RAM values match `trace`'s terminal tokens.

    `cells` is the public tracked address domain. `view` normally leaves tokens
    unchanged; native boot uses `ROMView.token initial` to interpret zero ROM
    shadow tokens as the actual public bytes. This definition adds no assumptions. -/
def Realizes {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime]
    (step : State → State → Prop) (trace : Data p Kind) (initial : State)
    (cells : List Cell) (view : MemoryToken p → MemoryToken p := id) : Prop :=
  ∃ after, Relation.ReflTransGen step initial after ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.read after = .ok (view sink).word.toBitVec after

end Airbender.Trace
