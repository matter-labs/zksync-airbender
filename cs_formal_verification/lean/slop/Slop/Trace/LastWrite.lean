module
public import Human.Helpers.Memory.RowEvents
public import Slop.Defs.Helpers.Memory.History
public import Slop.Trace.MemoryHistory
public import Mathlib.Tactic.FinCases
public import Slop.Arithmetic.Bytes
public import Slop.KernelRfl
public import Slop.Trace.InitialImage

@[expose] public section

namespace Airbender.Trace.Proofs
open Arithmetic

theorem last_write_unique (history : MemoryAccessList)
    (sorted : history.isTimestampSorted)
    (unique : (history.map (fun event => event.2.1)).Nodup)
    {event : MemoryAccess} (member : List.Mem event history) :
    MemoryAccessList.lastWriteValue history sorted event.2.1 = event.2.2.2 := by
  induction history with
  | nil => cases member
  | cons head rest ih =>
    obtain ⟨time, key, old, value⟩ := head
    rcases List.mem_cons.mp member with rfl | member
    · simp [MemoryAccessList.lastWriteValue]
    · have distinct : key ≠ event.2.1 := by
        have pair := List.nodup_cons.mp unique
        intro equal
        exact pair.1 (List.mem_map.mpr ⟨event, member, equal.symm⟩)
      simpa only [MemoryAccessList.lastWriteValue, ite_eq_right distinct] using
        ih (List.Pairwise.of_cons sorted) (List.nodup_cons.mp unique).2 member

end Airbender.Trace.Proofs
