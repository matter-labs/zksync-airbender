module
public import Proven.Trace.Machine.SharedHistory

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Trace.Proofs
set_option warningAsError true

/-- The shared x0 induction gives zero-valued writes in every native event at x0. -/
theorem shared_zero_writes {data : Transfer.Data babyBearModulus} {initial : RV.State} {cells : List Cell}
    (facts : Transfer.Facts data) (image : initialImageRV initial cells = some data.initial)
    (rules : Transfer.CellWriteRules data (Cell.register 0).addressCode 0) :
    ∀ event ∈ data.steps.map transferEvent, event.2.1 = (Cell.register 0).addressCode → memoryWord event.2.2.2 = 0 := by
  have reads := Transfer.read_cell_values_of_rules facts _ _ (Transfer.rv_initial_zero image) rules
  intro event present address
  obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
  have value := rules edge member address (fun source included _ same => reads source included same)
  change memoryWord edge.2.value = 0
  rw [value]
  rfl

end Airbender.Trace.Machine.Proofs
