import Human.Circuits.KeccakSplit.Native
import Human.Helpers.Core.BabyBearPrime
import Human.Helpers.Memory.SailHistory

/- What the trace-level proofs need from each split worker's circuit, as one
   contract (lean-strategies 2.2): the per-kind circuit proofs establish it, the
   memory and 361-call proofs only use it. Field: BabyBear (the claims' serialized
   inverse fixes it). -/

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Reference.RiscV.Sail

/-- Native facts of one active split row whose imported constraints hold (the state-free part, used by the RV
    proofs). -/
structure RowFacts : Prop where
  /-- Every write is a canonical word, given canonical reads. -/
  writes : ∀ row : Row babyBearModulus,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) row.constraints →
    row.assignment row.columns.execute = 1 →
    (∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) →
    ∀ port ∈ row.ports, (row.writeToken port).word.Bounded
  /-- The row is a call of the schedule: control in/out and lane results. -/
  effects : ∀ row : Row babyBearModulus,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) row.constraints →
    row.assignment row.columns.execute = 1 →
    (∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) →
    RowEffects row
  /-- The state pointer read through x11 is 256-byte aligned. -/
  aligned : ∀ row : Row babyBearModulus,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) row.constraints →
    (row.readWord 1).value % 256 = 0
  /-- Each lane half of call `index` is accessed by one of the row's ports, at the
      RAM word of its slot relative to the pointer read through x11. -/
  addresses : ∀ (row : Row babyBearModulus) (index : Fin 361),
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) row.constraints →
    row.assignment row.columns.execute = 1 →
    row.readWord 0 = ⟨controlAt index.val, 0⟩ →
    (row.readWord 1).Bounded →
    ∀ lane : Fin 7, lane.val < Call.slotCount (kindAt index.val) → ∀ high : Bool,
      ∃ port ∈ row.ports, port.address.code row.assignment =
        (Call.laneCell (row.readWord 1).toBitVec (Call.slots index)[lane] high).addressCode
/-- `RowFacts` plus the row's Sail execution. -/
structure RowContract : Prop extends RowFacts where
  /-- In a Sail history of exactly the row's accesses, from a state where every
      port reads its native value and call `index`'s arguments hold, the row
      executes call `index`. -/
  executes : ∀ (row : Row babyBearModulus) (index : Fin 361) {before after : State}
    {cells : List Cell} {events : List MemoryAccess},
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) row.constraints →
    row.assignment row.columns.execute = 1 →
    Call.ArgumentsAt index.val before →
    (∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) →
    SailHistory cells events before after →
    events.Perm (row.memorySteps.map transferEvent) →
    (∀ port ∈ row.ports, ∃ cell : Cell, cell.addressCode = port.address.code row.assignment ∧
      cell.read before = .ok (readToken row.assignment port).word.toBitVec before) →
    Call.ExecutesAt index before after

end Airbender.Keccak.Split.Native.Proofs
