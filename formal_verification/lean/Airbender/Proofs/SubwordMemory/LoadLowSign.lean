import Airbender.Proofs.SubwordMemory.LoadTemplates.LowSignPart00
import Airbender.Proofs.SubwordMemory.LoadTemplates.LowSignPart01
import Airbender.Proofs.SubwordMemory.LoadTemplates.LowSignPart02
import Airbender.Proofs.SubwordMemory.LoadTemplates.LowSignPart03
import Airbender.Proofs.SubwordMemory.LoadTemplates.LowSignPart04
import Airbender.Proofs.SubwordMemory.LoadTemplates.LowSignPart05
import Airbender.Proofs.SubwordMemory.LoadTemplates.LowSignPart06
import Airbender.Proofs.SubwordMemory.LoadTemplates.LowSignPart07
import Airbender.Proofs.SubwordMemory.LoadTemplates.LowSignPart08
import Airbender.Proofs.SubwordMemory.LoadTemplates.LowSignPart09
import Airbender.Proofs.SubwordMemory.LoadTemplates.LowSignPart10
import Airbender.Proofs.SubwordMemory.LoadTemplates.LowSignPart11
import Airbender.Proofs.SubwordMemory.LoadTemplates.LowSignPart12
import Airbender.Proofs.SubwordMemory.LoadTemplates.LowSignPart13
import Airbender.Proofs.SubwordMemory.LoadTemplates.LowSignPart14
import Airbender.Proofs.SubwordMemory.LoadTemplates.LowSignPart15
import Mathlib.Tactic.IntervalCases

namespace Airbender.SubwordMemory.LoadProofs
set_option autoImplicit false

theorem lowSignValues_samples (i : Fin 256) :
    (lowSignValues[i.val]?.getD 0) = (if i.val < 128 then i.val else i.val + 65280) := by
  have groupBound : i.val / 16 < 16 := by omega
  generalize groupEq : i.val / 16 = group at *
  interval_cases group
  · have same : i.val = 0 + i.val % 16 := by omega
    rw [same]
    exact lowSignValues_sample_00 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 16 + i.val % 16 := by omega
    rw [same]
    exact lowSignValues_sample_01 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 32 + i.val % 16 := by omega
    rw [same]
    exact lowSignValues_sample_02 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 48 + i.val % 16 := by omega
    rw [same]
    exact lowSignValues_sample_03 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 64 + i.val % 16 := by omega
    rw [same]
    exact lowSignValues_sample_04 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 80 + i.val % 16 := by omega
    rw [same]
    exact lowSignValues_sample_05 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 96 + i.val % 16 := by omega
    rw [same]
    exact lowSignValues_sample_06 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 112 + i.val % 16 := by omega
    rw [same]
    exact lowSignValues_sample_07 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 128 + i.val % 16 := by omega
    rw [same]
    exact lowSignValues_sample_08 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 144 + i.val % 16 := by omega
    rw [same]
    exact lowSignValues_sample_09 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 160 + i.val % 16 := by omega
    rw [same]
    exact lowSignValues_sample_10 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 176 + i.val % 16 := by omega
    rw [same]
    exact lowSignValues_sample_11 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 192 + i.val % 16 := by omega
    rw [same]
    exact lowSignValues_sample_12 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 208 + i.val % 16 := by omega
    rw [same]
    exact lowSignValues_sample_13 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 224 + i.val % 16 := by omega
    rw [same]
    exact lowSignValues_sample_14 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  · have same : i.val = 240 + i.val % 16 := by omega
    rw [same]
    exact lowSignValues_sample_15 ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩

end Airbender.SubwordMemory.LoadProofs
