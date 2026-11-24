module
public import Human.Compiler.NativeArithmetic

@[expose] public section
namespace Airbender.Compiler.NativePlacementWitness
open NativeArithmetic
set_option warningAsError true

def assignment (entries : List (Nat × GKRAddress)) (physical : GKRAddress → F) (index : Nat) : F :=
  match entries with
  | [] => 0
  | (key, address) :: rest => if index = key then physical address else assignment rest physical index

/-- Distinct variable names give a logical assignment for every physical address interpretation. -/
theorem agrees (entries : List (Nat × GKRAddress)) (unique : (entries.map Prod.fst).Nodup)
    (physical : GKRAddress → F) :
    ∀ entry ∈ entries, assignment entries physical entry.1 = physical entry.2 := by
  induction entries with
  | nil => intro entry member; cases member
  | cons head tail ih =>
    have distinct := List.nodup_cons.mp unique
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · simp [assignment]
    · have different : entry.1 ≠ head.1 := by
        intro equal
        exact distinct.1 (equal ▸ List.mem_map.mpr ⟨entry, member, rfl⟩)
      simpa only [assignment, ite_eq_right different] using ih distinct.2 entry member

end Airbender.Compiler.NativePlacementWitness
