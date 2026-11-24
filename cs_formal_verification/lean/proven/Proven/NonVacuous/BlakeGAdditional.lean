module
public import Human.Circuits.Blake2G.Theorems
public import Proven.NonVacuous.Blake2GPool

@[expose] public section
namespace Airbender.Blake2G
open NonVacuous.Blake2G

theorem soundness_witness : SoundnessSatisfiableClaim := by
  refine ⟨Control.controllerRows,
    ⟨⟨⟨(row 15).val, (row 16).val⟩, ⟨(row 19).val, (row 20).val⟩,
      ⟨(row 23).val, (row 24).val⟩, ⟨(row 27).val, (row 28).val⟩⟩,
      ⟨(row 33).val, (row 34).val⟩, ⟨(row 35).val, (row 36).val⟩⟩,
    ⟨⟨(row 17).val, (row 18).val⟩, ⟨(row 21).val, (row 22).val⟩,
      ⟨(row 25).val, (row 26).val⟩, ⟨(row 29).val, (row 30).val⟩⟩,
    row, ?_, core, ⟨rfl, rfl, rfl, rfl⟩⟩
  constructor <;> constructor <;> decide +kernel
end Airbender.Blake2G
