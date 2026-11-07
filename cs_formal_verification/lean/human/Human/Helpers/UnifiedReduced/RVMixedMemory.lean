import Human.Helpers.UnifiedReduced.RVRequestTrace
import Human.Helpers.UnifiedReduced.MixedMemory
import Human.Helpers.UnifiedReduced.RVProgram
import Human.Helpers.Memory.RVHistory
import Human.Circuits.UnifiedReduced.Tables.SetupRV

/-! RV siblings of `MixedMemory.lean` (helpers): the shared unified/worker architecture over `RVRequestTrace`, executed
    as RV cell reads/writes (`RVHistory`) from a public `RV.State`. The ordinary program is the unified RV program table
    (`rvDecoderFields`). A RAM cell is RAM at any address, INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW
    `ROM_END` (`RV.State.delegationRAM`). Native ports (`machinePorts`) are unchanged. -/

namespace Airbender.UnifiedReduced.Caller
open Trace

def RVRequestTrace.mixedSteps [Fact p.Prime] (data : RVRequestTrace p) :=
  data.machine.rows.flatMap (fun row => (machinePorts row).toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)) ++ data.workers.steps

def RVRequestTrace.cycleWorkers [Fact p.Prime] (data : RVRequestTrace p) (row : Trace.Row p UnifiedFamily) :=
  if Selected row.assignment then
    data.workers.rows.filter fun worker => decide (Delegation.Requests.fulfillment worker = request row.assignment)
  else []

def RVRequestTrace.cycleSteps [Fact p.Prime] (data : RVRequestTrace p) (row : Trace.Row p UnifiedFamily) :=
  (machinePorts row).toList.map (fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)) ++
    (data.cycleWorkers row).flatMap Delegation.Row.memorySteps

/-- RV sibling of `CycleExecution`: actual instruction-cycle RV states inside the one shared RV history. -/
def RVCycleExecution [Fact p.Prime] (data : RVRequestTrace p) (cells : List Cell)
    (events : List MemoryAccess) (initial finalState : RV.State)
    (row : Trace.Row p UnifiedFamily) : Prop :=
  ∃ earlier current newer before after,
    events = newer ++ current ++ earlier ∧
    current.Perm (data.cycleSteps row |>.map transferEvent) ∧
    RVHistory cells earlier initial before ∧
    RVHistory cells current before after ∧
    RVHistory cells newer after finalState

/-- RV sibling of `MixedMemoryAccepted`: native request checks, every noncaller in the unified RV program table, and
    one architectural permutation. -/
structure RVMixedMemoryAccepted [Fact p.Prime] (data : RVRequestTrace p)
    (program : List UnifiedReduced.RVProgramEntry) : Prop extends RVRequestChecks data where
  ordinaryDecoded : ∀ row ∈ data.machine.rows, row ∉ data.callers →
    (UnifiedReduced.rvDecoderTable program).Contains #[] row.decoderQuery
  memory : (data.machine.initialMemory ++ data.mixedSteps.map Prod.snd).Perm
    (data.machine.terminalMemory ++ data.mixedSteps.map Prod.fst)

/-- RV sibling of `MixedMemoryInputs`: public cells read from an `RV.State`, the caller and ordinary RV program tables
    read from its ROM image, initial clocks and modeled setup. No `Configured`. -/
structure RVMixedMemoryInputs [Fact p.Prime] (data : RVRequestTrace p)
    (program : List UnifiedReduced.RVProgramEntry) (before : RV.State)
    (callerAddresses ordinaryAddresses : List (BitVec 32)) (cells : List Cell) : Prop where
  publicProgram : RVRequestInputs data before callerAddresses
  ordinaryProgram : rvProgramImageWith UnifiedReduced.rvDecoderFields before ordinaryAddresses = some program
  initialization : initialImageRV before cells = some data.machine.initialMemory
  distinct : (cells.map Cell.addressCode).Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  setup : data.machine.rom = Setup.tableRV before
  tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows
  rounds : ∀ row ∈ data.workers.rows, row.family = .blakeRound →
    ∃ round, Blake2Round.Memory.RoundMask row.assignment round

end Airbender.UnifiedReduced.Caller
