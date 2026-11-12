module
public import Human.Helpers.Delegation.Memory
public import Human.Circuits.Keccak.Addresses
public import Human.Circuits.Keccak.ControlUpdate
public import Slop.Defs.Circuits.Keccak.Artifact

/-! Definitions only the proofs use, moved from `human/Human/Trace/Workers/Keccak/Call.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Keccak
open Trace
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
