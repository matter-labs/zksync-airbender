import Airbender.Proofs.Keccak.SplitChiPattern0Part0
import Airbender.Proofs.Keccak.SplitChiPattern0Part1
import Airbender.Proofs.Keccak.SplitChiPattern0Part2
import Airbender.Proofs.Keccak.SplitChiPattern0Part3
import Airbender.Proofs.Keccak.SplitChiPattern3Part0
import Airbender.Proofs.Keccak.SplitChiPattern3Part1
import Airbender.Proofs.Keccak.SplitChiPattern3Part2
import Airbender.Proofs.Keccak.SplitChiPattern3Part3
import Airbender.Proofs.Keccak.SplitChiPattern4Part0
import Airbender.Proofs.Keccak.SplitChiPattern4Part1
import Airbender.Proofs.Keccak.SplitChiPattern4Part2
import Airbender.Proofs.Keccak.SplitChiPattern4Part3
import Airbender.Proofs.Keccak.SplitDigitColumns

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

private theorem pattern_0 (index : Fin 4096) :
    let a := index.val % 16
    let b := index.val / 16 % 16
    let c := index.val / 256 % 16
    chi5GenericBlock98Pattern[index] = a ^^^ ((15 ^^^ b) &&& c) := by
  by_cases first : index.val < 1024
  · have found := ChiPattern0Part0.spec ⟨index.val, first⟩
    dsimp only at found
    simpa only [Nat.zero_add] using found
  by_cases second : index.val < 2048
  · have same : 1024 + (index.val - 1024) = index.val := by omega
    have found := ChiPattern0Part1.spec ⟨index.val - 1024, by omega⟩
    dsimp only at found
    simpa only [same] using found
  by_cases third : index.val < 3072
  · have same : 2048 + (index.val - 2048) = index.val := by omega
    have found := ChiPattern0Part2.spec ⟨index.val - 2048, by omega⟩
    dsimp only at found
    simpa only [same] using found
  · have same : 3072 + (index.val - 3072) = index.val := by omega
    have found := ChiPattern0Part3.spec ⟨index.val - 3072, by omega⟩
    dsimp only at found
    simpa only [same] using found

private theorem pattern_3 (index : Fin 4096) :
    let a := index.val % 16
    let b := index.val / 16 % 16
    let c := index.val / 256 % 16
    chi5GenericBlock120Pattern[index] = b ^^^ ((15 ^^^ c) &&& a) := by
  by_cases first : index.val < 1024
  · have found := ChiPattern3Part0.spec ⟨index.val, first⟩
    dsimp only at found
    simpa only [Nat.zero_add] using found
  by_cases second : index.val < 2048
  · have same : 1024 + (index.val - 1024) = index.val := by omega
    have found := ChiPattern3Part1.spec ⟨index.val - 1024, by omega⟩
    dsimp only at found
    simpa only [same] using found
  by_cases third : index.val < 3072
  · have same : 2048 + (index.val - 2048) = index.val := by omega
    have found := ChiPattern3Part2.spec ⟨index.val - 2048, by omega⟩
    dsimp only at found
    simpa only [same] using found
  · have same : 3072 + (index.val - 3072) = index.val := by omega
    have found := ChiPattern3Part3.spec ⟨index.val - 3072, by omega⟩
    dsimp only at found
    simpa only [same] using found

private theorem pattern_4 (index : Fin 4096) :
    let a := index.val % 16
    let b := index.val / 16 % 16
    let c := index.val / 256 % 16
    chi5GenericBlock121Pattern[index] = c ^^^ ((15 ^^^ a) &&& b) := by
  by_cases first : index.val < 1024
  · have found := ChiPattern4Part0.spec ⟨index.val, first⟩
    dsimp only at found
    simpa only [Nat.zero_add] using found
  by_cases second : index.val < 2048
  · have same : 1024 + (index.val - 1024) = index.val := by omega
    have found := ChiPattern4Part1.spec ⟨index.val - 1024, by omega⟩
    dsimp only at found
    simpa only [same] using found
  by_cases third : index.val < 3072
  · have same : 2048 + (index.val - 2048) = index.val := by omega
    have found := ChiPattern4Part2.spec ⟨index.val - 2048, by omega⟩
    dsimp only at found
    simpa only [same] using found
  · have same : 3072 + (index.val - 3072) = index.val := by omega
    have found := ChiPattern4Part3.spec ⟨index.val - 3072, by omega⟩
    dsimp only at found
    simpa only [same] using found

/-- All retained output patterns implement the exact four-bit chi operation. -/
theorem chi5_output_patterns : ∀ index : Fin 4096,
    let a := index.val % 16
    let b := index.val / 16 % 16
    let c := index.val / 256 % 16
    chi5GenericBlock98Pattern[index] = a ^^^ ((15 ^^^ b) &&& c) ∧
    chi5GenericBlock104Pattern[index] = a ^^^ ((15 ^^^ b) &&& c) ∧
    chi5GenericBlock112Pattern[index] = a ^^^ ((15 ^^^ b) &&& c) ∧
    chi5GenericBlock120Pattern[index] = b ^^^ ((15 ^^^ c) &&& a) ∧
    chi5GenericBlock121Pattern[index] = c ^^^ ((15 ^^^ a) &&& b) := by
  intro index
  have secondValue : chi5GenericBlock104PatternValue = chi5GenericBlock98PatternValue := rfl
  have thirdValue : chi5GenericBlock112PatternValue = chi5GenericBlock98PatternValue := rfl
  have second : chi5GenericBlock104Pattern = chi5GenericBlock98Pattern :=
    congrArg Vector.ofFn secondValue
  have third : chi5GenericBlock112Pattern = chi5GenericBlock98Pattern :=
    congrArg Vector.ofFn thirdValue
  rw [second, third]
  exact ⟨pattern_0 index, pattern_0 index, pattern_0 index, pattern_3 index, pattern_4 index⟩

end Airbender.Keccak.Split.Native.Fixed.Proofs
