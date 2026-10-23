import Airbender.Proofs.Sail.WordMemoryState
import Std.Data.ExtHashMap.Lemmas

namespace Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem

/-- A finite initialized byte image exists for every symbolic size. This proof
uses range membership, not evaluation of a concrete native memory domain. -/
theorem zeroMemory_exists (size : Nat) :
    ∃ memory : Std.ExtHashMap Nat (BitVec 8),
      ∀ address < size, memory[address]? = some 0 := by
  refine ⟨Std.ExtHashMap.ofList ((List.range size).map fun key => (key, (0 : BitVec 8))), ?_⟩
  intro address bound
  apply Std.ExtHashMap.getElem?_ofList_of_mem (k := address) (by simp)
  · apply List.pairwise_map.mpr
    exact (List.nodup_range : (List.range size).Nodup).imp (fun different => by simpa using different)
  · exact List.mem_map.mpr ⟨address, List.mem_range.mpr bound, rfl⟩

/-- Noncomputable public image: importing the proof cannot allocate a GiB of
native backing memory. Missing bytes outside the declared interval stay absent
from the claim; the pinned runtime's read semantics are unchanged. -/
noncomputable def zeroMemory (size : Nat) : Std.ExtHashMap Nat (BitVec 8) :=
  Classical.choose (zeroMemory_exists size)

theorem zeroMemory_byte {size address : Nat} (bound : address < size) :
    (zeroMemory size)[address]? = some 0 :=
  Classical.choose_spec (zeroMemory_exists size) address bound

/-- Actual runtime reads from a wholly initialized zero word. -/
theorem zeroMemory_word {before : State} {size address : Nat}
    (memory : before.mem = zeroMemory size) (bound : address + 4 ≤ size) :
    (readBytes (ue := SailRV32.exception) 4 address).run before = .ok 0 before := by
  apply read_word_of_bytes
  intro i
  rw [memory, zeroMemory_byte (by have small := i.isLt; omega)]
  simp

end Airbender.Reference.RiscV.Sail
