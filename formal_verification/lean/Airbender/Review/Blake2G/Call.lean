import Airbender.Review.Blake2G.Control
import Airbender.Review.Blake2G.Execution
import Airbender.Review.Delegation.Memory
import Airbender.Review.Delegation.Operations
import Airbender.Review.Keccak.Controller

namespace Airbender.Blake2G
open Trace Reference.RiscV.Sail

/-- The pinned G-only caller performs eight G operations per round, over
    seven reduced rounds or ten full rounds. -/
def callCount (reduced : Bool) : Nat := if reduced then 56 else 80

/-- Expected x12 after `i` calls. Bit seven selects reduced rounds; the
    counter returns to zero after the complete request. Later control words
    are derived from imported lookups and initialized matching. -/
def controlAt (reduced : Bool) (i : Nat) : Arithmetic.Word :=
  ⟨(if reduced then 128 else 0) + i % callCount reduced, 0⟩

/-- One uninterrupted G-only request span, from the pinned project caller in
    `common_constants/src/delegation_types/blake2s_g_function.rs`. This supplies public
    initialization and the span's boundary, not per-call reads or results.
    Binding the span to calling instructions remains a separate task. -/
structure CallInputs [Fact p.Prime] (data : Delegation.MemoryData p) (initial : State)
    (cells : List Cell) (reduced : Bool) : Prop where
  /-- Public initialized cells and native logical matching boundaries. -/
  memory : Delegation.MemoryInputs data initial cells
  /-- The existing modeled tables; setup-generator fidelity is unproved. -/
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  /-- The active G calls assigned to this request span. -/
  family : ∀ row ∈ data.rows, row.family = .blakeG
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  /-- The caller starts its counter at zero with the public round mode. -/
  controlStart : (Cell.register 12).read initial =
    .ok (if reduced then 128 else 0) initial
  /-- The complete span has exactly the pinned caller's call count. -/
  calls : data.rows.length = callCount reduced

/-- Write time of the imported x12 control port, in native clock units. -/
def callWriteTime (row : Delegation.Row p) : Nat :=
  (timeOfPair (row.writeToken importedConstraintsMemoryPorts[8]).time).value

/-- Actual rows can be ordered by native time. Every control read/write in
    that order follows the pinned schedule, and the terminal counter is zero
    with the public mode retained. These are conclusions of initialized history. -/
def CallSchedule (data : Delegation.MemoryData p) (reduced : Bool) : Prop :=
  ∃ ordered : List (Delegation.Row p), ordered.Perm data.rows ∧
    ordered.Pairwise (fun a b => callWriteTime a < callWriteTime b) ∧
    (∀ (i : Nat) (bound : i < ordered.length),
      (readToken (ordered[i]'bound).assignment importedConstraintsMemoryPorts[8]).word = controlAt reduced i ∧
      ((ordered[i]'bound).writeToken importedConstraintsMemoryPorts[8]).word = controlAt reduced (i + 1)) ∧
    ∃ sink ∈ data.terminal, sink.address = (Cell.register 12).addressCode ∧
      sink.word = controlAt reduced 0

/-- All G calls retain the actual initial x10/x11 pointers. This is proved
    from readonly matching; no pointer value, bound or per-call mapping is supplied. -/
def CallPointers (data : Delegation.MemoryData p) (initial : State) : Prop :=
  ∃ statePointer messagePointer : BitVec 32,
    (Cell.register 10).read initial = .ok statePointer initial ∧
    (Cell.register 11).read initial = .ok messagePointer initial ∧
    ∀ row ∈ data.rows, Native.statePointer row.assignment = Arithmetic.Word.ofBitVec statePointer ∧
      Native.messagePointer row.assignment = Arithmetic.Word.ofBitVec messagePointer

end Airbender.Blake2G
