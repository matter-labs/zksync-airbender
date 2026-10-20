import Human.Helpers.Delegation.Memory
import Human.Circuits.Keccak.Addresses
import Human.Circuits.Keccak.ControlUpdate

namespace Airbender.Keccak
open Trace Reference.RiscV.Sail Reference.Sail

/-- Control expected by the pinned caller: 24 rounds of 27 micro-operations,
    followed by the final Iota. The initialized-history proof derives these
    values for the actual imported rows; they are not inputs to that proof. -/
def scheduleControl (i : Fin 650) : ControlState :=
  let stage := i.val % 27
  ⟨⟨if stage < 5 then 0 else if stage < 7 then stage - 4 else if stage < 12 then 3
      else if stage < 17 then 4 else if (stage - 17) % 2 = 0 then 5 else 6,
      by split_ifs <;> omega⟩,
    ⟨if stage < 5 then stage else if stage < 7 then 0 else if stage < 12 then stage - 7
      else if stage < 17 then stage - 12 else (stage - 17) / 2,
      by have bound : stage < 27 := Nat.mod_lt _ (by decide); split_ifs <;> omega⟩,
    ⟨i.val / 27, by have := i.isLt; omega⟩⟩

/-- Public boundary for one uninterrupted Keccak request span. The pinned caller
    performs 649 calls with x10 initially zero (`common_constants/src/delegation_types/keccak_special5.rs`).
    Shared initialized matching proves every later control read. Connecting this
    span to the calling instruction trace remains the request-binding task. -/
structure CallInputs [Fact p.Prime] (data : Delegation.MemoryData p) (initial : State)
    (cells : List Cell) : Prop where
  memory : Delegation.MemoryInputs data initial cells
  controlCell : Cell.register 10 ∈ cells
  controlStart : (Cell.register 10).read initial = .ok 0 initial
  /-- This span contains the active calls of this one request. -/
  family : ∀ row ∈ data.rows, row.family = .keccak
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  calls : data.rows.length = 649

/-- The declared final x10 token is the caller's completion value 1544. This
    is a proved result, never an assumed response or per-row control sequence. -/
def CallControl (data : Delegation.MemoryData p) : Prop :=
  ∃ sink ∈ data.terminal, sink.address = (Cell.register 10).addressCode ∧
    sink.word = Arithmetic.Word.ofBitVec 1544

/-- Every call uses the public initial x11 pointer, and its terminal token
    preserves that pointer. Shared matching supplies the actual initial read;
    no pointer value, bound or per-row mapping is assumed. -/
def CallPointer (data : Delegation.MemoryData p) (initial : State) : Prop :=
  ∃ pointer, (Cell.register 11).read initial = .ok pointer initial ∧
    (∀ row ∈ data.rows, statePointer row.assignment = Arithmetic.Word.ofBitVec pointer) ∧
    ∃ sink ∈ data.terminal, sink.address = (Cell.register 11).addressCode ∧
      sink.word = Arithmetic.Word.ofBitVec pointer

/-- The native control port's write time. This observes the imported clock
    descriptor, including its offset; it does not assign a new clock. -/
def callWriteTime (row : Delegation.Row p) : Nat :=
  (timeOfPair (row.writeToken importedConstraintsMemoryPorts[0]).time).value

/-- All 649 actual rows can be ordered by their native write clocks. In that
    order, each reads the caller's expected control and writes the next one.
    No ordering, intermediate controls or expected responses are assumed. -/
def CallSchedule (data : Delegation.MemoryData p) : Prop :=
  ∃ ordered : List (Delegation.Row p), ∃ count : ordered.length = 649,
    ordered.Perm data.rows ∧
    ordered.Pairwise (fun a b => callWriteTime a < callWriteTime b) ∧
    ∀ i : Fin 649,
      let w := (ordered[i.val]'(by have := i.isLt; omega)).assignment
      Arithmetic.Word.mk (w Variables.controlReadLo).val (w Variables.controlReadHi).val =
        ⟨(scheduleControl ⟨i.val, by have := i.isLt; omega⟩).packed, 0⟩ ∧
      Arithmetic.Word.mk (w Variables.controlWriteLo).val (w Variables.controlWriteHi).val =
        ⟨(scheduleControl ⟨i.val + 1, by have := i.isLt; omega⟩).packed, 0⟩

end Airbender.Keccak
