import Human.Helpers.Delegation.RequestTrace

namespace Airbender.Delegation.Caller
open Trace

/-- The two architectural caller ports: rs1 and rd. The intervening full-width
    CSR port belongs to the request permutation, so it is excluded from GPR/RAM
    matching. Placements come from the imported ADD/SUB descriptors. -/
def architecturalPorts : Array MemoryPort :=
  #[AddSub.importedConstraintsMemoryPorts[0], AddSub.importedConstraintsMemoryPorts[2]]

def architecturalSteps (w : Nat → ZMod p) : List (MemoryToken p × MemoryToken p) :=
  architecturalPorts.toList.map fun port =>
    (readToken w port, writeToken AddSub.importedConstraintsTraceColumns w port)

/-- One pool of native architectural accesses. Caller x0 transfers and worker
    register/RAM transfers are matched together; worker-only boundary tokens
    are unused. This admits interactions across successive worker invocations. -/
def RequestTrace.sharedSteps [Fact p.Prime] (data : RequestTrace p) :=
  data.machine.rows.flatMap (fun row => architecturalSteps row.assignment) ++ data.workers.steps

/-- Imported equations and request checks, with one architectural permutation.
    This milestone admits caller machine rows only; standard/custom rows will
    enter the same pool in the subsequent machine-composition claim. -/
structure SharedMemoryAccepted [Fact p.Prime] (data : RequestTrace p) : Prop
    extends RequestChecks data where
  /-- Every participating machine row belongs to the decoded caller scope. -/
  callerRows : data.callers = data.machine.rows
  /-- Native architectural reads/writes share public seed and terminal tokens. -/
  memory : (data.machine.initialMemory ++ data.sharedSteps.map Prod.snd).Perm
    (data.machine.terminalMemory ++ data.sharedSteps.map Prod.fst)

/-- Public caller bytes, starting clock and initialized architectural cells.
    No source value, worker read, per-row bound or expected output is supplied. -/
structure SharedMemoryInputs [Fact p.Prime] (data : RequestTrace p)
    (before : Reference.RiscV.Sail.State) (addresses : List (BitVec 32))
    (cells : List Cell) : Prop where
  /-- Original Sail decoding and public initial-clock conditions. -/
  publicProgram : RequestInputs data before addresses
  /-- Successful public Sail reads construct the single shared seed image. -/
  initialization : initialImage before cells = some data.machine.initialMemory
  /-- One initialized cell per native architectural address. -/
  distinct : (cells.map Cell.addressCode).Nodup
  /-- RAM uses aligned four-byte cells; registers need no extra condition. -/
  aligned : ∀ cell ∈ cells, cell.Aligned

end Airbender.Delegation.Caller
