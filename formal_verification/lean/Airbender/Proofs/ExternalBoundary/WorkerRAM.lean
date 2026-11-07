import Airbender.Review.Helpers.Context.ExternalBoundary.WorkerRAM
import Airbender.Proofs.Trace.ROMView

namespace Airbender.ExternalBoundary.WorkerRAM.Proofs
open Trace Arithmetic
set_option warningAsError true

theorem location_not_shadow (location : Location) :
    ¬ Trace.ROMView.shadow location.cell.addressCode := by
  cases location with
  | register index => simp [Location.cell, Cell.addressCode, Trace.ROMView.shadow]
  | ram address outside =>
    simp only [Location.cell, Cell.addressCode, Trace.ROMView.shadow, Nat.unpair_pair,
      true_and, Word.ofBitVec]
    dsimp [ROM.limit, limbBase] at *
    omega

theorem port_not_shadow {workers : List (Delegation.Row p)} (binding : Binding workers)
    {row : Delegation.Row p} (member : row ∈ workers) {port : MemoryPort} (present : port ∈ row.ports) :
    ¬ Trace.ROMView.shadow (port.address.code row.assignment) := by
  obtain ⟨location, equal⟩ := binding row member port present
  rw [equal]
  exact location_not_shadow location

theorem transfers_unchanged (before : Reference.RiscV.Sail.State)
    {workers : List (Delegation.Row p)} (binding : Binding workers)
    {row : Delegation.Row p} (member : row ∈ workers) :
    row.memorySteps.map (fun edge => (Trace.ROMView.token before edge.1, Trace.ROMView.token before edge.2)) =
      row.memorySteps := by
  unfold Delegation.Row.memorySteps
  rw [List.map_map]
  apply List.map_congr_left
  intro port present
  have outside := port_not_shadow binding member (by simpa using present)
  simp only [Function.comp_apply, Trace.ROMView.token, readToken, Delegation.Row.writeToken,
    outside, if_false]

theorem pool_transfers_unchanged (before : Reference.RiscV.Sail.State)
    {data : Delegation.MemoryData p} (binding : Binding data.rows) :
    data.steps.map (fun edge => (Trace.ROMView.token before edge.1, Trace.ROMView.token before edge.2)) =
      data.steps := by
  simp only [Delegation.MemoryData.steps, List.map_flatMap]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro row member
  exact transfers_unchanged before binding member

end Airbender.ExternalBoundary.WorkerRAM.Proofs
