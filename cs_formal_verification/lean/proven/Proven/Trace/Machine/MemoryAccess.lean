module
public import Proven.Trace.Machine.MemoryClocks
public import Proven.Trace.SeedAddressClocks
public import Proven.Delegation.RVSharedImage

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- A distinct public seed domain gives unique native address/clock access keys in the complete shared history. -/
theorem shared_access_keys_unique {data : Transfer.Data babyBearModulus} {initial : RV.State} {cells : List Cell}
    (facts : Transfer.Facts data) (image : initialImageRV initial cells = some data.initial)
    (distinct : (cells.map Cell.addressCode).Nodup) :
    ((data.steps.map transferEvent).map fun event => (event.1, event.2.1)).Nodup := by
  have boundary := Transfer.rv_boundary_inputs image distinct
  have unique := SeedTransfer.raw_address_clocks_distinct facts boundary.toSeedInputs
  have native : (data.steps.map transferEvent).Sublist (Transfer.rawEvents data) := List.sublist_append_right _ _
  exact unique.sublist (native.map (fun event => (event.1, event.2.1)))

/-- Transfers in one native worker tick have distinct addresses. -/
theorem same_tick_addresses_distinct {data : Transfer.Data babyBearModulus}
    (unique : ((data.steps.map transferEvent).map fun event => (event.1, event.2.1)).Nodup)
    {edges : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)} {clock : Nat}
    (included : edges.Sublist data.steps) (same : ∀ edge ∈ edges, (transferEvent edge).1 = clock) :
    (edges.map fun edge => edge.1.address).Nodup := by
  have localKeys := unique.sublist ((included.map transferEvent).map (fun event => (event.1, event.2.1)))
  have constant : (edges.map transferEvent).map (fun event => (event.1, event.2.1)) =
      (edges.map fun edge => edge.1.address).map (fun address => (clock, address)) := by
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro edge present
    exact congrArg (fun time => (time, edge.1.address)) (same edge present)
  rw [constant] at localKeys
  exact localKeys.of_map _

end Airbender.Trace.Machine.Proofs
