import Human.Helpers.UnifiedReduced.RVMixedMemory
import Human.Trace.Delegation.RequestEffects

/-! RV siblings of `CallerCycles.lean` and `MixedFetch.lean` (`CurrentFetch`): caller cycles inside one shared RV
    history from a public `RV.State`. Fetch reads the RV program table (the ROM image, `rom`, which no history step
    changes); PC retirement is the spec's `nextInstr`. A RAM cell is RAM at any address, INCLUDING READ-WRITE ACCESS TO
    THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Sail's readonly-code profile (`CodeProfile`: tracked RAM
    above the ROM boundary, entries in aligned ROM words) has no RV counterpart: the ROM image is separate from RAM, and
    the RV program table's fetch guard already places every entry in aligned ROM words. -/

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- RV sibling of `CycleFetch`: at an actual instruction cycle of the shared RV history, the matched public entry is the
    RV table entry read from the ROM image (`rvProgramEntryWith`) in every reachable pre-state. -/
structure RVCycleFetch {NativeKind EntryKind : Type} [CircuitLayout NativeKind]
    (initial : RV.State) (cells : List Cell) (events : List MemoryAccess)
    (row : Trace.Row p NativeKind) (program : List (Trace.RVProgramEntry EntryKind))
    (projection : RV.Instr → Option (DecoderData EntryKind))
    (entryQuery : Trace.RVProgramEntry EntryKind → Vector (ZMod p) 9) : Prop where
  reachable : ∃ before, RVHistory cells (events.filter fun event => decide (event.1 ≤ row.clock)) initial before
  instruction : ∃ entry ∈ program, row.decoderQuery = entryQuery entry ∧
    row.start.word.toBitVec = entry.pc ∧
    ∀ before, RVHistory cells (events.filter fun event => decide (event.1 ≤ row.clock)) initial before →
      rvProgramEntryWith projection before entry.pc = some entry

/-- RV sibling of `CurrentFetch`: every ordinary row and every caller fetches and decodes its public RV entry. -/
structure RVCurrentFetch [Fact p.Prime] (data : RVRequestTrace p)
    (program : List UnifiedReduced.RVProgramEntry) (initial : RV.State)
    (cells : List Cell) (events : List MemoryAccess) : Prop where
  ordinary : ∀ row ∈ data.machine.rows, row ∉ data.callers →
    RVCycleFetch initial cells events row program UnifiedReduced.rvDecoderFields (fun entry => entry.query)
  callers : ∀ row ∈ data.callers,
    RVCycleFetch initial cells events row data.program rvCallerFields rvCallerQuery

/-- RV sibling of `CallerCycle`: actual caller cycle RV states, public RV fetch (the entry decodes to `.delegate k`
    of its family, and `RV.step` at the cycle's pre-state is that call), the matched worker's port reads at the cycle
    boundaries, and the spec's PC retirement. -/
def RVCallerCycle [Fact p.Prime] (data : RVRequestTrace p) (initial finalState : RV.State)
    (cells : List Cell) (events : List MemoryAccess) (row : Trace.Row p UnifiedFamily) : Prop :=
  ∃ before after,
    RVHistory cells (events.filter fun event => decide (event.1 ≤ Delegation.Caller.startClock row)) initial before ∧
    RVHistory cells (events.filter fun event => decide
      (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)) before after ∧
    RVHistory cells (events.filter fun event => decide (Delegation.Caller.finishClock row < event.1)) after finalState ∧
    (∃ entry ∈ data.program, row.decoderQuery = rvCallerQuery entry ∧
      row.start.word.toBitVec = entry.pc ∧
      rvProgramEntryWith rvCallerFields before entry.pc = some entry ∧
      RV.decode entry.bits = some (.delegate (familyKind entry.data.family)) ∧
      RV.step (before.setPC entry.pc) = RV.exec (before.setPC entry.pc) (.delegate (familyKind entry.data.family)) ∧
      ∃ worker ∈ data.workers.rows, Delegation.Requests.fulfillment worker = request row.assignment ∧
      worker.family = entry.data.family ∧ Delegation.Caller.WorkerEffect worker ∧
      ∀ port ∈ worker.ports, ∃ cell ∈ cells,
        cell.addressCode = port.address.code worker.assignment ∧
        cell.readRV before = some (readToken worker.assignment port).word.toBitVec ∧
        cell.readRV after = some (worker.writeToken port).word.toBitVec) ∧
    (after.setPC row.start.word.toBitVec).nextInstr = after.setPC row.finish.word.toBitVec

/-- RV sibling of `CallerCycleEffects`: one shared initialized RV history supplies every caller cycle and terminal
    read. -/
structure RVCallerCycleEffects [Fact p.Prime] (data : RVRequestTrace p)
    (program : List UnifiedReduced.RVProgramEntry) (initial : RV.State) (cells : List Cell) : Prop where
  requests : RVRequestBinding data initial
  execution : ∃ events finalState, events.Perm (data.mixedSteps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧ RVHistory cells events initial finalState ∧
    RVCurrentFetch data program initial cells events ∧
    (∀ row ∈ data.callers, RVCallerCycle data initial finalState cells events row) ∧
    ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
      cell.addressCode = token.address ∧ cell.readRV finalState = some token.word.toBitVec

end Airbender.UnifiedReduced.Caller
