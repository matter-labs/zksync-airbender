import Human.Helpers.Delegation.Memory
import Human.Helpers.Memory.SailHistory
import Human.Helpers.Memory.Platform

namespace Airbender.Delegation
open Trace

/-- Canonical values observed at an imported port. The row supplies its family,
    placement-resolved columns and assignment; these observations impose no
    bounds or expected behavior. Shared history proves their actual Sail values. -/
def Row.readWord (row : Row p) (index : Fin row.ports.size) : Arithmetic.Word :=
  (readToken row.assignment row.ports[index.val]).word

def Row.writtenWord (row : Row p) (index : Fin row.ports.size) : Arithmetic.Word :=
  (row.writeToken row.ports[index.val]).word

/-- One native port's actual read/write position in the shared Sail history.
    Earlier accesses produce `middle`; this port reads there and writes `later`;
    remaining accesses produce the final state. Timestamp ties are still ordered
    internally. This is memory transport, separate from a whole delegation call. -/
def PortExecution (cells : List Cell) (events : List MemoryAccess)
    (before after : Reference.RiscV.Sail.State) (edge : MemoryToken p × MemoryToken p) : Prop :=
  ∃ cell ∈ cells, ∃ earlier middle later newer,
    events = newer ++ transferEvent edge :: earlier ∧
    SailHistory cells earlier before middle ∧
    cell.addressCode = edge.1.address ∧
    cell.read middle = .ok edge.1.word.toBitVec middle ∧
    Reference.Sail.run (cell.write edge.2.word.toBitVec) middle = .ok () later ∧
    SailHistory cells newer later after

/-- One complete worker call inside the shared initialized history.
    Its ports read from one actual pre-state and produce one actual post-state;
    earlier and later machine/worker accesses remain in the same history.
    These states and the grouping are conclusions, not supplied inputs. -/
def CallExecution (cells : List Cell) (events : List MemoryAccess)
    (before after : Reference.RiscV.Sail.State) (row : Row p) : Prop :=
  ∃ earlier current newer start finish,
    events = newer ++ current ++ earlier ∧
    current.Perm (row.memorySteps.map transferEvent) ∧
    SailHistory cells earlier before start ∧
    SailHistory cells current start finish ∧
    SailHistory cells newer finish after ∧
    ∀ port ∈ row.ports, ∃ cell ∈ cells,
      cell.addressCode = port.address.code row.assignment ∧
      cell.read start = .ok (readToken row.assignment port).word.toBitVec start ∧
      cell.read finish = .ok (row.writeToken port).word.toBitVec finish

end Airbender.Delegation
