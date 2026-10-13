import Airbender.Review.Helpers.UnifiedReduced.RequestTrace
import Airbender.Review.Helpers.UnifiedReduced.Program
import Airbender.Review.Helpers.Delegation.SharedOperations
import Airbender.Review.Helpers.Memory.SailHistory

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- Caller rs1/rd access architectural x0. Its middle port carries the virtual
    CSR token and belongs to request matching, not initialized GPR/RAM history. -/
def architecturalPorts : Array MemoryPort :=
  #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[2]]

/-- Ordinary standard/custom rows retain all three native ports. The imported
    caller selector excludes only the virtual port, with public decoding checked below. -/
def machinePorts (row : Trace.Row p UnifiedFamily) : Array MemoryPort :=
  if Selected row.assignment then architecturalPorts else row.ports

/-- One shared architecture contains unified instructions, callers and workers.
    Worker-only initial/terminal tokens are unused. -/
def RequestTrace.mixedSteps [Fact p.Prime] (data : RequestTrace p) :=
  data.machine.rows.flatMap (fun row => (machinePorts row).toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)) ++ data.workers.steps

/-- Workers attached to this actual caller by full CSR/time matching.
    Ordinary instructions have no issued workers. This reads the native pool;
    unique fulfillment and placement are proved by request soundness. -/
def RequestTrace.cycleWorkers [Fact p.Prime] (data : RequestTrace p) (row : Trace.Row p UnifiedFamily) :=
  if Selected row.assignment then
    data.workers.rows.filter fun worker => decide (Delegation.Requests.fulfillment worker = request row.assignment)
  else []

/-- The instruction's architectural ports followed by its issued worker ports.
    Virtual CSR ports remain in request matching. No port values or results are added. -/
def RequestTrace.cycleSteps [Fact p.Prime] (data : RequestTrace p) (row : Trace.Row p UnifiedFamily) :=
  (machinePorts row).toList.map (fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)) ++
    (data.cycleWorkers row).flatMap Delegation.Row.memorySteps

/-- Actual instruction-cycle states inside the one shared memory history.
    The middle accesses are exactly this instruction and its issued workers;
    earlier/later accesses stay connected to the same public initial/final state.
    This is memory execution; the Sail instruction/retirement proof is separate. -/
def CycleExecution [Fact p.Prime] (data : RequestTrace p) (cells : List Cell)
    (events : List MemoryAccess) (initial finalState : Reference.RiscV.Sail.State)
    (row : Trace.Row p UnifiedFamily) : Prop :=
  ∃ earlier current newer before after,
    events = newer ++ current ++ earlier ∧
    current.Perm (data.cycleSteps row |>.map transferEvent) ∧
    Trace.SailHistory cells earlier initial before ∧
    Trace.SailHistory cells current before after ∧
    Trace.SailHistory cells newer after finalState

/-- Native request checks plus ordinary public decoding and one architectural
    permutation. No desired reads, operand ranges or worker outputs are supplied. -/
structure MixedMemoryAccepted [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) : Prop extends RequestChecks data where
  /-- Every noncaller uses the public standard/TRIADD/XORROT metadata table. -/
  ordinaryDecoded : ∀ row ∈ data.machine.rows, row ∉ data.callers →
    (UnifiedReduced.decoderTable program).Contains #[] row.decoderQuery
  /-- All actual GPR/RAM transfers share the same public seed and terminal tokens. -/
  memory : (data.machine.initialMemory ++ data.mixedSteps.map Prod.snd).Perm
    (data.machine.terminalMemory ++ data.mixedSteps.map Prod.fst)

/-- Public physical cells, instruction bytes, initial clocks and modeled setup.
    Native zero ROM shadows need separate public-byte transport; this interface
    binds successful actual cell reads and does not claim boot-ROM retirement. -/
structure MixedMemoryInputs [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (before : Reference.RiscV.Sail.State)
    (callerAddresses ordinaryAddresses : List (BitVec 32)) (cells : List Cell) : Prop where
  /-- Original public CSR decoding and the initial nineteen-bit, four-aligned clock. -/
  publicProgram : RequestInputs data before callerAddresses
  /-- Original Sail decoding constructs the ordinary standard/custom program. -/
  ordinaryProgram : Mixed.programImage before ordinaryAddresses = some program
  /-- Successful public cell reads construct the shared native seed. -/
  initialization : initialImage before cells = some data.machine.initialMemory
  /-- Each physical address is initialized once. -/
  distinct : (cells.map Cell.addressCode).Nodup
  /-- RAM uses aligned four-byte words; register cells require no extra condition. -/
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- Unified modeled tables use this same public physical memory. -/
  setup : data.machine.rom = Setup.table before
  /-- Existing modeled worker tables, including the concrete Keccak controller. -/
  tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows
  /-- Extended BLAKE uses one admitted public round mask; span ABI is separate. -/
  rounds : ∀ row ∈ data.workers.rows, row.family = .blakeRound →
    ∃ round, Blake2Round.Memory.RoundMask row.assignment round


end Airbender.UnifiedReduced.Caller
