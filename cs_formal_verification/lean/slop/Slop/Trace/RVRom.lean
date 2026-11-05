import Slop.Trace.RVHistory
import Slop.Trace.RVCells

/-! ROM bytes are fixed by the RV write history: every RV update of a tracked cell keeps the bytes below `ROM_END`
    (register writes change no byte; RAM writes are `writable`, hence at or above `ROM_END`). This is the `agree`
    premise of the fetch lemmas (`rv_step_fetch`). -/

namespace Airbender.Trace
open Arithmetic

theorem applyRV_rom {cell : Cell} {value : BitVec 32} {before after : RV.State}
    (update : cell.applyRV value before = some after) :
    ∀ a : BitVec 32, a.toNat < RV.ROM_END → after.mem a = before.mem a := by
  intro a rom
  unfold Cell.applyRV at update
  split at update
  · cases update
    rfl
  · cases cell with
    | register index =>
      simp only [Cell.writeRV] at update
      cases update
      rfl
    | ram address =>
      exact Airbender.Trace.Proofs.writeRV_rom update rom

theorem rvWriteHistory_rom {cells : List Cell} {events : List (Nat × Nat)} {before after : RV.State}
    (history : RVWriteHistory cells events before after) :
    ∀ a : BitVec 32, a.toNat < RV.ROM_END → after.mem a = before.mem a := by
  induction history with
  | nil before =>
    intro a _
    rfl
  | @cons address value rest before middle after past cell member atAddress write ih =>
    intro a rom
    rw [applyRV_rom write a rom, ih a rom]

end Airbender.Trace
