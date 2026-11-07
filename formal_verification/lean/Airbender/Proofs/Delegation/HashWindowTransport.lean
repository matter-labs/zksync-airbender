import Airbender.Review.Trace.Delegation.HashWindows
import Airbender.Proofs.Trace.InitialImage
import Airbender.Proofs.Delegation.NativeSegments

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true

theorem empty_prefix_state {data : MemoryData p} {lower : Nat}
    {cells : List Cell} {events : List MemoryAccess} {before after : State}
    (empty : data.prefixRows lower = [])
    (permutation : events.Perm ((Trace.Proofs.Transfer.beforeSteps (transferData data) lower).map transferEvent))
    (history : SailHistory cells events before after) : after = before := by
  rw [← native_prefix_steps, empty] at permutation
  have emptyEvents : events = [] := by
    cases events with
    | nil => rfl
    | cons event rest =>
      have count := permutation.length_eq
      simp at count
  subst events
  cases history
  rfl

theorem terminal_mapping_read [Fact p.Prime] {data : MemoryData p}
    {before first last : State} {cells : List Cell}
    (source : TraceMapping data before first cells) (target : TraceMapping data before last cells)
    (addresses : (data.terminal.map MemoryToken.address).Perm (cells.map Cell.addressCode))
    {cell : Cell} (member : cell ∈ cells) {value : BitVec 32}
    (read : cell.read first = .ok value first) : cell.read last = .ok value last := by
  obtain ⟨token, present, code⟩ := List.mem_map.mp
    (addresses.mem_iff.mpr (List.mem_map.mpr ⟨cell, member, rfl⟩))
  obtain ⟨other, _, otherCode, otherRead⟩ := source.finalCells token present
  have equal := cell_address_injective (otherCode.trans code)
  subst other
  have same := (EStateM.Result.ok.inj (read.symm.trans otherRead)).1
  obtain ⟨other, _, otherCode, otherRead⟩ := target.finalCells token present
  have equal := cell_address_injective (otherCode.trans code)
  subst other
  simpa only [← same] using otherRead

end Airbender.Delegation.Proofs
