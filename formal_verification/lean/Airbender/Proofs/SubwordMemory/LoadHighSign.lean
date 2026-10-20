import Airbender.Proofs.SubwordMemory.LoadTemplates.HighSignPart00
import Airbender.Proofs.SubwordMemory.LoadTemplates.HighSignPart01
import Airbender.Proofs.SubwordMemory.LoadTemplates.HighSignPart02
import Airbender.Proofs.SubwordMemory.LoadTemplates.HighSignPart03
import Airbender.Proofs.SubwordMemory.LoadTemplates.HighSignPart04
import Airbender.Proofs.SubwordMemory.LoadTemplates.HighSignPart05
import Airbender.Proofs.SubwordMemory.LoadTemplates.HighSignPart06
import Airbender.Proofs.SubwordMemory.LoadTemplates.HighSignPart07
import Airbender.Proofs.SubwordMemory.LoadTemplates.HighSignPart08
import Airbender.Proofs.SubwordMemory.LoadTemplates.HighSignPart09
import Airbender.Proofs.SubwordMemory.LoadTemplates.HighSignPart10
import Airbender.Proofs.SubwordMemory.LoadTemplates.HighSignPart11
import Airbender.Proofs.SubwordMemory.LoadTemplates.HighSignPart12
import Airbender.Proofs.SubwordMemory.LoadTemplates.HighSignPart13
import Airbender.Proofs.SubwordMemory.LoadTemplates.HighSignPart14
import Airbender.Proofs.SubwordMemory.LoadTemplates.HighSignPart15
import Mathlib.Tactic.IntervalCases

namespace Airbender.SubwordMemory.LoadProofs
set_option autoImplicit false

theorem highSignValues_samples (i : Fin 256) :
    (highSignValues[i.val]?.getD 0) = (if i.val < 128 then 0 else 65535) := by
  have groupBound : i.val / 16 < 16 := by omega
  generalize groupEq : i.val / 16 = group at *
  interval_cases group
  · have same : i.val = 0 + i.val % 16 := by omega
    rw [same]
    exact highSignValues_sample_00 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 16 + i.val % 16 := by omega
    rw [same]
    exact highSignValues_sample_01 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 32 + i.val % 16 := by omega
    rw [same]
    exact highSignValues_sample_02 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 48 + i.val % 16 := by omega
    rw [same]
    exact highSignValues_sample_03 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 64 + i.val % 16 := by omega
    rw [same]
    exact highSignValues_sample_04 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 80 + i.val % 16 := by omega
    rw [same]
    exact highSignValues_sample_05 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 96 + i.val % 16 := by omega
    rw [same]
    exact highSignValues_sample_06 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 112 + i.val % 16 := by omega
    rw [same]
    exact highSignValues_sample_07 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 128 + i.val % 16 := by omega
    rw [same]
    exact highSignValues_sample_08 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 144 + i.val % 16 := by omega
    rw [same]
    exact highSignValues_sample_09 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 160 + i.val % 16 := by omega
    rw [same]
    exact highSignValues_sample_10 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 176 + i.val % 16 := by omega
    rw [same]
    exact highSignValues_sample_11 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 192 + i.val % 16 := by omega
    rw [same]
    exact highSignValues_sample_12 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 208 + i.val % 16 := by omega
    rw [same]
    exact highSignValues_sample_13 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 224 + i.val % 16 := by omega
    rw [same]
    exact highSignValues_sample_14 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 240 + i.val % 16 := by omega
    rw [same]
    exact highSignValues_sample_15 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩

end Airbender.SubwordMemory.LoadProofs
