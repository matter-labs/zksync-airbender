module
import all Mathlib.Data.List.Sort
public import Proven.GKRCompiler.Wiring
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Nodup

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.AddressUniqueChecks

/-- Numerical keys are used only as a sufficient uniqueness check. -/
def addressCode : GKRAddress → Nat
  | .BaseLayerWitness index => Nat.pair 0 index
  | .BaseLayerMemory index => Nat.pair 1 index
  | .InnerLayer layer offset => Nat.pair 2 (Nat.pair layer offset)
  | .Setup index => Nat.pair 3 index
  | .VirtualSetup kind => Nat.pair 4 (match kind with
      | .RangeCheck16Bits => 0
      | .RangeCheckTimestamp => 1
      | .InitsAndTeardownsLow => 2
      | .InitsAndTeardownsHigh => 3)
  | .ScratchSpace index => Nat.pair 5 index
  | .Cached layer offset => Nat.pair 6 (Nat.pair layer offset)

def ascendingFrom : Nat → List Nat → Bool
  | _, [] => true
  | previous, next :: rest => decide (previous < next) && ascendingFrom next rest

theorem ascendingFrom_sound (previous : Nat) (items : List Nat)
    (checked : ascendingFrom previous items = true) :
    items.Nodup ∧ ∀ item ∈ items, previous < item := by
  induction items generalizing previous with
  | nil => simp
  | cons next rest ih =>
      simp only [ascendingFrom, Bool.and_eq_true, decide_eq_true_eq] at checked
      have tail := ih next checked.2
      refine ⟨List.nodup_cons.mpr ⟨?_, tail.1⟩, ?_⟩
      · intro member
        exact Nat.lt_irrefl next (tail.2 next member)
      · intro item member
        rcases List.mem_cons.mp member with same | member
        · subst item; exact checked.1
        · exact Nat.lt_trans checked.1 (tail.2 item member)

def ascending : List Nat → Bool
  | [] => true
  | first :: rest => ascendingFrom first rest

theorem ascending_sound (items : List Nat) (checked : ascending items = true) : items.Nodup := by
  cases items with
  | nil => exact List.nodup_nil
  | cons first rest =>
      have facts := ascendingFrom_sound first rest checked
      refine List.nodup_cons.mpr ⟨?_, facts.1⟩
      intro member
      exact Nat.lt_irrefl first (facts.2 first member)

def check (addresses : List GKRAddress) : Bool :=
  ascending ((addresses.map addressCode).insertionSort (fun first second => first ≤ second))

theorem check_sound (addresses : List GKRAddress) (checked : check addresses = true) : addresses.Nodup := by
  have sorted := ascending_sound _ checked
  have original := (List.perm_insertionSort (fun first second : Nat => first ≤ second)
    (addresses.map addressCode)).nodup_iff.mp sorted
  exact List.Nodup.of_map addressCode original

/-- Preserve the original per-index Boolean statement from list uniqueness. -/
theorem distinctAt_complete {α : Type} [BEq α] [LawfulBEq α]
    (items : List α) (unique : items.Nodup) (index : Fin items.length) :
    distinctAt items index = true := by
  revert unique index
  induction items with
  | nil => intro _ index; exact Fin.elim0 index
  | cons first rest ih =>
      intro unique index
      cases index with
      | mk value within =>
        cases value with
        | zero => simpa [distinctAt] using (List.nodup_cons.mp unique).1
        | succ value =>
            have inside : value < rest.length := by simpa using within
            have checked := ih (List.nodup_cons.mp unique).2 ⟨value, inside⟩
            simpa [distinctAt, Nat.add_assoc] using checked

end Airbender.Compiler.AddressUniqueChecks
