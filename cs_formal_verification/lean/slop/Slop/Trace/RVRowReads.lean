module
public import Slop.Trace.RVHistory
public import Slop.Defs.Helpers.Memory.Ports
public import Slop.Defs.Helpers.Memory.RowEvents

@[expose] public section

/-! Reads of a three-port row whose first two ports are read-only (`WordMemory.Proofs.rv_row_port_reads` for all
    three ports): the read-only ports leave the RV state unchanged, so every port reads the row's pre-state. -/

namespace Airbender.Trace.Proofs
open Arithmetic

/-- All three ports of a three-port row whose first two ports are read-only read the row's pre-state: each reads a
    public cell at its address. -/
theorem rv_row_port_reads3 {p : Nat} {cells : List Cell} {columns : TraceColumns}
    {first second destination : MemoryPort} {w : Nat → ZMod p} (epoch : Nat)
    (firstReadonly : first.writeValue = none) (secondReadonly : second.writeValue = none)
    {before after : RV.State}
    (history : RVHistory cells
      (nativeRowEvents epoch columns #[first, second, destination] w).reverse before after) :
    (∃ cell ∈ cells, cell.addressCode = first.address.code w ∧
      cell.readRV before = some (memoryWord (first.readCode w))) ∧
    (∃ cell ∈ cells, cell.addressCode = second.address.code w ∧
      cell.readRV before = some (memoryWord (second.readCode w))) ∧
    (∃ cell ∈ cells, cell.addressCode = destination.address.code w ∧
      cell.readRV before = some (memoryWord (destination.readCode w))) := by
  have firstSame : first.readCode w = first.writeCode w := by
    simp [MemoryPort.readCode, MemoryPort.writeCode, firstReadonly]
  have secondSame : second.readCode w = second.writeCode w := by
    simp [MemoryPort.readCode, MemoryPort.writeCode, secondReadonly]
  dsimp [nativeRowEvents] at history
  cases history with
  | cons past destinationCell dm da dr dw =>
    cases past with
    | cons past rightCell rm ra rr rw =>
      cases past with
      | cons empty leftCell lm la lr lw =>
        cases empty with
        | nil =>
          have lr' : leftCell.readRV before = some (memoryWord (first.readCode w)) := lr
          have leftUnchanged : leftCell.applyRV (memoryWord (first.writeCode w)) before = some before := by
            rw [← firstSame]
            simp [Cell.applyRV, lr']
          have hm := (Option.some.inj (lw.symm.trans leftUnchanged)).symm
          subst hm
          have rr' : rightCell.readRV before = some (memoryWord (second.readCode w)) := rr
          have rightUnchanged : rightCell.applyRV (memoryWord (second.writeCode w)) before = some before := by
            rw [← secondSame]
            simp [Cell.applyRV, rr']
          have hm := (Option.some.inj (rw.symm.trans rightUnchanged)).symm
          subst hm
          exact ⟨⟨leftCell, lm, la, lr'⟩, ⟨rightCell, rm, ra, rr'⟩, ⟨destinationCell, dm, da, dr⟩⟩

end Airbender.Trace.Proofs
