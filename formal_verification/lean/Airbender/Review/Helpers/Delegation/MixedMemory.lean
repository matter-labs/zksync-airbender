import Airbender.Review.Helpers.Delegation.SharedOperations
import Airbender.Review.Helpers.Decoder.PooledProgram
import Airbender.Review.Helpers.Memory.ROM
import Airbender.Review.Helpers.Tables.Subword

namespace Airbender.Delegation.Caller
open Trace

/-- Architectural ports of a participating machine row. Ordinary rows keep all
    native ports; a selected caller excludes its virtual CSR request port. The
    selector is read from the assignment and checked against public decoding. -/
def machinePorts (row : Trace.Row p PooledFamily) : Array MemoryPort :=
  if row.family == .addSub && decide (Requests.Selected row.assignment) then
    architecturalPorts else row.ports

/-- One initialized pool contains ordinary instructions, delegation callers and
    all worker transfers. Separate worker memory boundaries are unused. -/
def RequestTrace.mixedSteps [Fact p.Prime] (data : RequestTrace p) :=
  data.machine.rows.flatMap (fun row => (machinePorts row).toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)) ++ data.workers.steps

/-- Native constraints, decoder membership and logical matching for the same
    mixed architecture. The two decoder tables retain their native schemas:
    ordinary ISA metadata and full-width delegation CSR addresses. -/
structure MixedMemoryAccepted [Fact p.Prime] (data : RequestTrace p)
    (program : List PooledProgramEntry) : Prop extends RequestChecks data where
  /-- Every noncaller uses the ordinary public Sail decoder table. -/
  ordinaryDecoded : ∀ row ∈ data.machine.rows, row ∉ data.callers →
    (Trace.decoderTable program row.family).Contains #[] row.decoderQuery
  /-- All architectural transfers share one public seed and terminal image. -/
  memory : (data.machine.initialMemory ++ data.mixedSteps.map Prod.snd).Perm
    (data.machine.terminalMemory ++ data.mixedSteps.map Prod.fst)

/-- Public initialization, actual instruction bytes and modeled setup. Both
    address lists select bytes in the same public state, for the two distinct
    decoder schemas. No read, operand bound, worker result or schedule is given. -/
structure MixedMemoryInputs [Fact p.Prime] (data : RequestTrace p)
    (program : List PooledProgramEntry) (before : Reference.RiscV.Sail.State)
    (callerAddresses ordinaryAddresses : List (BitVec 32)) (cells : List Cell) : Prop
    extends SharedMemoryInputs data before callerAddresses cells where
  /-- Original Sail decoding constructs the ordinary six-family table. -/
  ordinaryProgram : pooledProgramImage before ordinaryAddresses = some program
  /-- Word-ROM setup is bound to the same public initialized cells. -/
  wordTable : data.machine.rom.wordMemory = ROM.table cells data.machine.initialMemory
  /-- Subword setup uses bytes of the same public initial state. -/
  subwordTable : data.machine.rom.subwordMemory = Verification.subwordTable (ROM.words before)
  /-- Existing modeled worker tables, including the concrete Keccak controller. -/
  tables : data.workers.setup = modeledSetup Keccak.Controller.rows
  /-- Extended BLAKE workers use one admitted round mask; span ABI is separate. -/
  rounds : ∀ row ∈ data.workers.rows, row.family = .blakeRound →
    ∃ round, Blake2Round.Memory.RoundMask row.assignment round

end Airbender.Delegation.Caller
