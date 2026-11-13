module
public import Human.Circuits.Bigint.RVTheorems
public import Proven.NonVacuous.BigintPool

@[expose] public section
namespace Airbender.Bigint.Memory
open NonVacuous.Bigint
set_option warningAsError true

theorem rv_addresses_soundness_witness : RVAddressesSoundnessSatisfiableClaim := by
  refine ⟨data, before, cells,
    ⟨⟨(row 3).val, (row 4).val⟩, ⟨(row 37).val, (row 38).val⟩⟩,
    importedConstraintsIndirectPorts.map (fun port => port.address row), row, ?_, accepted,
    ⟨⟨rfl, rfl, rfl⟩, List.mem_singleton_self _⟩⟩
  refine ⟨inputs, ?_, rfl⟩
  intro current member
  simp only [data, List.mem_singleton] at member
  subst current
  rfl
end Airbender.Bigint.Memory
