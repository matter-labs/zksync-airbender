import Airbender.Review.Helpers.UnifiedReduced.FullCallReference
import Airbender.Review.Trace.UnifiedReduced.BigintCycles
import Airbender.Review.Trace.UnifiedReduced.MixedCycles
import Airbender.Review.Circuits.Blake2G.Call
import Airbender.Review.Circuits.Blake2Round.Call
import Airbender.Review.Circuits.Keccak.Call

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail Reference.Sail

/-- A successful caller cycle in its actual shared-history states. The raw
    call effect is retained so the first step starts at the original public
    state even when its initial nextPC differs from PC. -/
def FullCallerCycle [Fact p.Prime] (data : RequestTrace p) (initial finalState : State)
    (domain : List Cell) (events : List MemoryAccess) (row : Trace.Row p UnifiedFamily) : Prop :=
  ∃ before after,
    SailHistory domain (events.filter fun event => decide (event.1 ≤ Delegation.Caller.startClock row)) initial before ∧
    SailHistory domain (events.filter fun event => decide
      (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)) before after ∧
    SailHistory domain (events.filter fun event => decide (Delegation.Caller.finishClock row < event.1)) after finalState ∧
    ∃ entry ∈ data.program, row.decoderQuery = Delegation.Caller.query entry ∧
      row.start.word.toBitVec = entry.pc ∧
      entry.SourceWith before Delegation.Caller.decoderFields ∧
      FullCall entry.data.family before after ∧
      FullRetirement entry.data.family (retiredState before row.start.word.toBitVec)
        (retiredState after row.finish.word.toBitVec)

/-- Original ordinary clauses and the pinned complete custom-call references
    in one successful instruction relation. Every step fetches public bytes at
    the actual current PC. Exceptional custom execution is outside this scope. -/
def FullStep [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (program : List UnifiedReduced.ProgramEntry) (callers : List Delegation.Caller.ProgramEntry)
    (before after : State) : Prop :=
  Mixed.Step program before after ∨
    ∃ entry ∈ callers, entry.SourceWith before Delegation.Caller.decoderFields ∧
      run (SailRV32.Functions.get_arch_pc ()) before = .ok entry.pc before ∧
      FullRetirement entry.data.family before after

end Airbender.UnifiedReduced.Caller
