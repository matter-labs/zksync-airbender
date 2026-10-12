import Airbender.Review.UnifiedReduced.RequestTrace
import Airbender.Review.UnifiedReduced.MixedExecution
import Airbender.Review.Delegation.SharedOperations
import Airbender.Review.Trace.SailHistory

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

/-- An original instruction retires between its actual cycle states in the
    shared history. The three windows retain earlier and later machine/worker
    effects. The clause is original Sail execution, not an expected output. -/
def RetiresCycle (cells : List Cell) (events : List MemoryAccess)
    (initial finalState : Reference.RiscV.Sail.State) (row : Trace.Row p UnifiedFamily)
    (clause : SailRV32.SailM SailRV32.ExecutionResult) : Prop :=
  ∃ before after,
    Trace.SailHistory cells (events.filter fun event => decide
      (event.1 ≤ (timeOfPair row.start.timestamp).value)) initial before ∧
    Trace.SailHistory cells (events.filter fun event => decide
      ((timeOfPair row.start.timestamp).value < event.1 ∧
        event.1 ≤ (timeOfPair row.finish.timestamp).value)) before after ∧
    Trace.SailHistory cells (events.filter fun event => decide
      ((timeOfPair row.finish.timestamp).value < event.1)) after finalState ∧
    Reference.Sail.run (Reference.RiscV.Sail.normalStep clause)
      (Trace.retiredState before row.start.word.toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (Trace.retiredState after row.finish.word.toBitVec)

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

/-- Actual unified/worker transport through one initialized history. This derives
    every native read/write/terminal word bound and architectural x0 value, then
    realizes the pool in Sail and reuses existing worker operation references.
    Issued workers have actual call boundaries inside that same history.
    Whole instruction retirement, ROM shadows and hash-span segmentation remain separate. -/
structure MixedMemoryEffects [Fact p.Prime] (data : RequestTrace p)
    (before : Reference.RiscV.Sail.State) (cells : List Cell) : Prop where
  /-- Public decoding and native requests identify each issued worker and its cycle. -/
  requests : RequestBinding data before
  /-- Architectural x0 reads are canonical zero, derived from initialization and writes. -/
  zeroReads : ∀ edge ∈ data.mixedSteps, edge.1.address = (Cell.register 0).addressCode → edge.1.value = 0
  /-- All unified/caller/worker reads and writes have sixteen-bit limbs. -/
  words : ∀ edge ∈ data.mixedSteps, edge.1.word.Bounded ∧ edge.2.word.Bounded
  /-- Every shared terminal word is canonical as well. -/
  terminal : ∀ token ∈ data.machine.terminalMemory, token.word.Bounded
  /-- Every native address selects an actually initialized canonical Sail cell. -/
  addresses : ∀ edge ∈ data.mixedSteps, ∃ cell ∈ cells,
    cell.addressCode = edge.1.address ∧ cell.addressWord.Bounded
  /-- Existing bigint/Clean hash references use these same actual native reads. -/
  operations : ∀ row ∈ data.workers.rows, Delegation.Caller.WorkerEffect row
  /-- Each transfer executes once in native time order and reaches all terminal cells.
      Every issued worker reads/writes one actual call pre/post-state inside this
      same history. From a nonzero public initial clock, every instruction also
      has derived cycle states containing its architectural and issued-worker ports.
      Native boot starts at clock four; surplus zero-clock workers stay exposed
      outside the issued-cycle guarantee. -/
  execution : ∃ (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
    events.Perm (data.mixedSteps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧
    Trace.SailHistory cells events before after ∧
    (∀ worker ∈ data.workers.rows, Delegation.Requests.Live (Delegation.Requests.fulfillment worker) →
      Delegation.CallExecution cells events before after worker) ∧
    (0 < (timeOfPair data.machine.initial.timestamp).value →
      ∀ row ∈ data.machine.rows, CycleExecution data cells events before after row) ∧
    ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
      cell.addressCode = token.address ∧ cell.read after = .ok token.word.toBitVec after

end Airbender.UnifiedReduced.Caller
