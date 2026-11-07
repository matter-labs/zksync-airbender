import Slop.Trace.RVHistory
import Slop.Trace.RVCells

/-! The ROM image never changes along the RV write history: cell updates write registers or RAM (`mem`), never
    `rom`. This is the `agree` premise of the fetch lemmas (`rv_step_fetch`) and what ties a LOAD below `ROM_END`
    (`RV.State.loadView`) to the starting ROM image. -/

namespace Airbender.Trace
open Arithmetic

theorem applyRV_rom {cell : Cell} {value : BitVec 32} {before after : RV.State}
    (update : cell.applyRV value before = some after) : after.rom = before.rom := by
  unfold Cell.applyRV at update
  split at update
  · cases update
    rfl
  · exact Airbender.Trace.Proofs.writeRV_rom update

theorem rvWriteHistory_rom {cells : List Cell} {events : List (Nat × Nat)} {before after : RV.State}
    (history : RVWriteHistory cells events before after) : after.rom = before.rom := by
  induction history with
  | nil before => rfl
  | @cons address value rest before middle after past cell member atAddress write ih =>
    rw [applyRV_rom write, ih]

end Airbender.Trace
