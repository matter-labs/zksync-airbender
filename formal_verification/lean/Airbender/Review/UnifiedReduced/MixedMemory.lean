import Airbender.Review.UnifiedReduced.RequestTrace
import Airbender.Review.UnifiedReduced.MixedExecution
import Airbender.Review.Delegation.SharedOperations

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
      same history. Zero-clock surplus workers remain outside this call guarantee. -/
  execution : ∃ (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
    events.Perm (data.mixedSteps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧
    Trace.Proofs.SailHistory cells events before after ∧
    (∀ worker ∈ data.workers.rows, Delegation.Requests.Live (Delegation.Requests.fulfillment worker) →
      Delegation.CallExecution cells events before after worker) ∧
    ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
      cell.addressCode = token.address ∧ cell.read after = .ok token.word.toBitVec after

end Airbender.UnifiedReduced.Caller
