import Airbender.Proofs.GKRProtocol.BaseAssignment
import Airbender.Proofs.GKRProtocol.AddressUniqueChecks
import Airbender.Proofs.GKRProtocol.NumericLookupTable

namespace Airbender.Compiler.CleanPlacementChecks
open NumericPolynomialChecks
set_option warningAsError true

theorem addressCode_injective : Function.Injective AddressUniqueChecks.addressCode := by
  intro left right same
  cases left <;> cases right <;> simp_all [AddressUniqueChecks.addressCode, Nat.pair_eq_pair]
  case VirtualSetup.VirtualSetup first second => cases first <;> cases second <;> simp_all

structure Capture where
  bank : LookupTable Nat
  references : List (Nat × Nat)

def check (data : Capture) : Bool :=
  data.bank.valid && data.references.all (fun (expected, index) =>
    decide (index < data.bank.size) && data.bank.getD index 0 == expected)

theorem reference_mem (data : Capture) (checked : check data = true)
    (reference : Nat × Nat) (member : reference ∈ data.references) :
    reference.1 ∈ data.bank.toList := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at checked
  have found := checked.2 reference member
  simp only [decide_eq_true_eq, beq_iff_eq] at found
  have inside : reference.2 < data.bank.toList.length := by
    rw [← LookupTable.size_eq_length data.bank checked.1]
    exact found.1
  have same := found.2
  rw [LookupTable.getD_eq data.bank checked.1,
    List.getElem?_eq_getElem inside, Option.getD_some] at same
  rw [← same]
  exact List.getElem_mem inside

theorem member_sound (entries placements : List GKRAddress) (data : Capture)
    (bankBinding : data.bank.toList = entries.map AddressUniqueChecks.addressCode)
    (placementBinding : data.references.map Prod.fst = placements.map AddressUniqueChecks.addressCode)
    (checked : check data = true) : ∀ address ∈ placements, address ∈ entries := by
  intro address included
  have codeMember : AddressUniqueChecks.addressCode address ∈ data.references.map Prod.fst := by
    rw [placementBinding]
    exact List.mem_map.mpr ⟨address, included, rfl⟩
  rcases List.mem_map.mp codeMember with ⟨reference, referenceMember, expected⟩
  have nativeMember := reference_mem data checked reference referenceMember
  rw [bankBinding, expected] at nativeMember
  rcases List.mem_map.mp nativeMember with ⟨actual, actualMember, same⟩
  exact addressCode_injective same ▸ actualMember

theorem address_placement_of_mem (entries : List GKRAddress) (nonempty : 0 < entries.length)
    (unique : entries.Nodup) (address : GKRAddress) (member : address ∈ entries) :
    (WireBank.ofList entries nonempty).address ((WireBank.ofList entries nonempty).placement address) = address := by
  rcases List.mem_iff_get.mp member with ⟨index, same⟩
  rw [← same]
  change (WireBank.ofList entries nonempty).address
    ((WireBank.ofList entries nonempty).placement ((WireBank.ofList entries nonempty).address index)) = _
  rw [WireBank.ofList_roundTrip entries nonempty unique index]
  rfl

theorem check_sound (entries : List GKRAddress) (nonempty : 0 < entries.length) (unique : entries.Nodup)
    (placements : List GKRAddress) (data : Capture)
    (bankBinding : data.bank.toList = entries.map AddressUniqueChecks.addressCode)
    (placementBinding : data.references.map Prod.fst = placements.map AddressUniqueChecks.addressCode)
    (checked : check data = true) :
    placements.all (fun address => decide ((WireBank.ofList entries nonempty).address
      ((WireBank.ofList entries nonempty).placement address) = address)) = true := by
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro address member
  exact address_placement_of_mem entries nonempty unique address (member_sound entries placements data bankBinding placementBinding checked address member)

theorem placement_at (bank : WireBank n) (placements : List GKRAddress)
    (checked : placements.all (fun address => decide (bank.address (bank.placement address) = address)) = true)
    (index : Fin placements.length) :
    decide (bank.address (bank.placement (placements.get index)) = placements.get index) = true :=
  List.all_eq_true.mp checked _ (List.get_mem _ _)



theorem placement_from_lookup (bank : WireBank n) (placements : List GKRAddress)
    (checked : placements.all (fun address => decide (bank.address (bank.placement address) = address)) = true)
    (index : Nat) (address : GKRAddress) (found : placements[index]? = some address) :
    decide (bank.address (bank.placement address) = address) = true := by
  obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp found
  exact List.all_eq_true.mp checked _ (same ▸ List.getElem_mem within)



theorem all_lookup (predicate : GKRAddress → Bool) (placements : List GKRAddress)
    (checked : placements.all predicate = true) (index : Nat) (address : GKRAddress)
    (found : placements[index]? = some address) : predicate address = true := by
  obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp found
  exact List.all_eq_true.mp checked _ (same ▸ List.getElem_mem within)

end Airbender.Compiler.CleanPlacementChecks
