import Mathlib.Tactic.IntervalCases
import Airbender.Proofs.FullUnsigned.ThetaSourceLowZero
import Airbender.Proofs.FullUnsigned.ThetaSourceLowOne
import Airbender.Proofs.FullUnsigned.ThetaSourceLowTwo
import Airbender.Proofs.FullUnsigned.ThetaSourceLowThree
import Airbender.Proofs.FullUnsigned.ThetaSourceLowFour
import Airbender.Proofs.FullUnsigned.ThetaSourceLowFive
import Airbender.Proofs.FullUnsigned.ThetaSourceLowSix
import Airbender.Proofs.FullUnsigned.ThetaSourceLowSeven
import Airbender.Proofs.FullUnsigned.ThetaSourceHighZero
import Airbender.Proofs.FullUnsigned.ThetaSourceHighOne
import Airbender.Proofs.FullUnsigned.ThetaSourceHighTwo
import Airbender.Proofs.FullUnsigned.ThetaSourceHighThree
import Airbender.Proofs.FullUnsigned.ThetaSourceHighFour
import Airbender.Proofs.FullUnsigned.ThetaSourceHighFive
import Airbender.Proofs.FullUnsigned.ThetaSourceHighSix
import Airbender.Proofs.FullUnsigned.ThetaSourceHighSeven
import Airbender.Proofs.FullUnsigned.ThetaSourceSplitKeys
import Airbender.Proofs.FullUnsigned.ThetaSourceXorMembership
import Airbender.Proofs.FullUnsigned.ThetaSourceControlSlots
import Airbender.Proofs.FullUnsigned.PaddingMembership

namespace Airbender.Setup.SourceCaptureThetaProofs
set_option warningAsError true
set_option Elab.async false

/-- The zero-shift low source fragment equals its original native value. -/
theorem source_split_low_zero_match (index : Fin 65536) :
    (((SourceCaptureTheta.columns[3]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[3]).value index.val := by
  rw [source_split_low_zero_get, Option.getD_some]
  have native := Airbender.Keccak.Split.Native.Fixed.Proofs.theta_fragment_low_value
    ⟨index.val, by change index.val < 524288; have bound := index.isLt; omega⟩
  have shift : index.val / 65536 = 0 := by omega
  rw [shift] at native
  simp only [Nat.pow_zero, Nat.mul_one] at native
  change _ = ((index.val / 256 % 256) ^^^ (index.val % 256)) % 256 at native
  rw [native]
  have bound : ((index.val / 256 % 256) ^^^ (index.val % 256)) < 256 :=
    Nat.xor_lt_two_pow (n := 8) (by omega) (by omega)
  exact (Nat.mod_eq_of_lt bound).symm

/-- All shift cases prove this complete source output fragment. -/
theorem source_split_low_match {artifact : Artifact}
    (parsed : parse SourceCaptureTheta.source = .ok artifact) (index : Fin 524288) :
    (((SourceCaptureTheta.columns[3]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[3]).value index.val := by
  have shiftBound : index.val / 65536 < 8 := by omega
  generalize shiftEq : index.val / 65536 = shift at *
  interval_cases shift
  · let localIndex : Fin 65536 := ⟨index.val % 65536, Nat.mod_lt _ (by decide +kernel)⟩
    have value := source_split_low_zero_match localIndex
    have physical : 65536 + localIndex.val = 65536 + index.val := by dsimp [localIndex]; omega
    have original : 0 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simp only [Nat.zero_add] at original
    simpa only [physical, original] using value
  · let localIndex : Fin 65536 := ⟨index.val % 65536, Nat.mod_lt _ (by decide +kernel)⟩
    have value := source_split_low_one_match parsed localIndex
    have physical : 131072 + localIndex.val = 65536 + index.val := by dsimp [localIndex]; omega
    have original : 65536 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [physical, original] using value
  · let localIndex : Fin 65536 := ⟨index.val % 65536, Nat.mod_lt _ (by decide +kernel)⟩
    have value := source_split_low_two_match parsed localIndex
    have physical : 196608 + localIndex.val = 65536 + index.val := by dsimp [localIndex]; omega
    have original : 131072 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [physical, original] using value
  · let localIndex : Fin 65536 := ⟨index.val % 65536, Nat.mod_lt _ (by decide +kernel)⟩
    have value := source_split_low_three_match parsed localIndex
    have physical : 262144 + localIndex.val = 65536 + index.val := by dsimp [localIndex]; omega
    have original : 196608 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [physical, original] using value
  · let localIndex : Fin 65536 := ⟨index.val % 65536, Nat.mod_lt _ (by decide +kernel)⟩
    have value := source_split_low_four_match parsed localIndex
    have physical : 327680 + localIndex.val = 65536 + index.val := by dsimp [localIndex]; omega
    have original : 262144 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [physical, original] using value
  · let localIndex : Fin 65536 := ⟨index.val % 65536, Nat.mod_lt _ (by decide +kernel)⟩
    have value := source_split_low_five_match parsed localIndex
    have physical : 393216 + localIndex.val = 65536 + index.val := by dsimp [localIndex]; omega
    have original : 327680 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [physical, original] using value
  · let localIndex : Fin 65536 := ⟨index.val % 65536, Nat.mod_lt _ (by decide +kernel)⟩
    have value := source_split_low_six_match parsed localIndex
    have physical : 458752 + localIndex.val = 65536 + index.val := by dsimp [localIndex]; omega
    have original : 393216 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [physical, original] using value
  · let localIndex : Fin 65536 := ⟨index.val % 65536, Nat.mod_lt _ (by decide +kernel)⟩
    have value := source_split_low_seven_match parsed localIndex
    have physical : 524288 + localIndex.val = 65536 + index.val := by dsimp [localIndex]; omega
    have original : 458752 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [physical, original] using value

/-- All shift cases prove this complete source output fragment. -/
theorem source_split_high_match (index : Fin 524288) :
    (((SourceCaptureTheta.columns[4]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[4]).value index.val := by
  have shiftBound : index.val / 65536 < 8 := by omega
  generalize shiftEq : index.val / 65536 = shift at *
  interval_cases shift
  · let localIndex : Fin 65536 := ⟨index.val % 65536, Nat.mod_lt _ (by decide +kernel)⟩
    have value := source_split_high_zero_match localIndex
    have physical : 65536 + localIndex.val = 65536 + index.val := by dsimp [localIndex]; omega
    have original : 0 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simp only [Nat.zero_add] at original
    simpa only [physical, original] using value
  · let localIndex : Fin 65536 := ⟨index.val % 65536, Nat.mod_lt _ (by decide +kernel)⟩
    have value := source_split_high_one_match localIndex
    have physical : 131072 + localIndex.val = 65536 + index.val := by dsimp [localIndex]; omega
    have original : 65536 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [physical, original] using value
  · let localIndex : Fin 65536 := ⟨index.val % 65536, Nat.mod_lt _ (by decide +kernel)⟩
    have value := source_split_high_two_match localIndex
    have physical : 196608 + localIndex.val = 65536 + index.val := by dsimp [localIndex]; omega
    have original : 131072 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [physical, original] using value
  · let localIndex : Fin 65536 := ⟨index.val % 65536, Nat.mod_lt _ (by decide +kernel)⟩
    have value := source_split_high_three_match localIndex
    have physical : 262144 + localIndex.val = 65536 + index.val := by dsimp [localIndex]; omega
    have original : 196608 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [physical, original] using value
  · let localIndex : Fin 65536 := ⟨index.val % 65536, Nat.mod_lt _ (by decide +kernel)⟩
    have value := source_split_high_four_match localIndex
    have physical : 327680 + localIndex.val = 65536 + index.val := by dsimp [localIndex]; omega
    have original : 262144 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [physical, original] using value
  · let localIndex : Fin 65536 := ⟨index.val % 65536, Nat.mod_lt _ (by decide +kernel)⟩
    have value := source_split_high_five_match localIndex
    have physical : 393216 + localIndex.val = 65536 + index.val := by dsimp [localIndex]; omega
    have original : 327680 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [physical, original] using value
  · let localIndex : Fin 65536 := ⟨index.val % 65536, Nat.mod_lt _ (by decide +kernel)⟩
    have value := source_split_high_six_match localIndex
    have physical : 458752 + localIndex.val = 65536 + index.val := by dsimp [localIndex]; omega
    have original : 393216 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [physical, original] using value
  · let localIndex : Fin 65536 := ⟨index.val % 65536, Nat.mod_lt _ (by decide +kernel)⟩
    have value := source_split_high_seven_match localIndex
    have physical : 524288 + localIndex.val = 65536 + index.val := by dsimp [localIndex]; omega
    have original : 458752 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [physical, original] using value

/-- Every split arithmetic source field equals its original native field. -/
theorem source_split_columns_match {artifact : Artifact}
    (parsed : parse SourceCaptureTheta.source = .ok artifact) (column : Fin 9) (index : Fin 524288) :
    (((SourceCaptureTheta.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[column.val]).value index.val := by
  fin_cases column
  · exact source_split_keys_match (⟨0, by decide +kernel⟩ : Fin 3) index
  · exact source_split_keys_match (⟨1, by decide +kernel⟩ : Fin 3) index
  · exact source_split_keys_match (⟨2, by decide +kernel⟩ : Fin 3) index
  · exact source_split_low_match parsed index
  · exact source_split_high_match index
  · have source := source_split_padding_get (⟨0, by decide +kernel⟩ : Fin 3) index
    have native := Airbender.Keccak.Split.Native.Fixed.Proofs.theta_split_padding_value
      (⟨0, by decide +kernel⟩ : Fin 3) index.val
    change ((SourceCaptureTheta.columns[5]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val) = some 0 at source
    change (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[5]).value index.val = 0 at native
    exact (congrArg (fun value : Option Nat => value.getD 0) source).trans native.symm
  · have source := source_split_padding_get (⟨1, by decide +kernel⟩ : Fin 3) index
    have native := Airbender.Keccak.Split.Native.Fixed.Proofs.theta_split_padding_value
      (⟨1, by decide +kernel⟩ : Fin 3) index.val
    change ((SourceCaptureTheta.columns[6]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val) = some 0 at source
    change (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[6]).value index.val = 0 at native
    exact (congrArg (fun value : Option Nat => value.getD 0) source).trans native.symm
  · have source := source_split_padding_get (⟨2, by decide +kernel⟩ : Fin 3) index
    have native := Airbender.Keccak.Split.Native.Fixed.Proofs.theta_split_padding_value
      (⟨2, by decide +kernel⟩ : Fin 3) index.val
    change ((SourceCaptureTheta.columns[7]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val) = some 0 at source
    change (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[7]).value index.val = 0 at native
    exact (congrArg (fun value : Option Nat => value.getD 0) source).trans native.symm
  · exact (congrArg (fun value : Option Nat => value.getD 0) (source_split_tag_get index)).trans
      (Airbender.Keccak.Split.Native.Fixed.Proofs.theta_split_tag_value ⟨index.val, index.isLt⟩).symm

/-- Every split arithmetic source row equals its original native row. -/
theorem source_split_rows {artifact : Artifact}
    (parsed : parse SourceCaptureTheta.source = .ok artifact) (index : Fin 524288) :
    (Vector.ofFn fun column : Fin 9 => signedValue
      ((((SourceCaptureTheta.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val)).getD 0)) =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.row ⟨index.val, by
        change index.val < 524288; exact index.isLt⟩).map signedValue := by
  apply Vector.ext
  intro column bound
  simp only [Vector.getElem_ofFn, Vector.getElem_map, LiteralTree.Region.row]
  change signedValue _ = signedValue ((Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[column]).value index.val)
  exact congrArg signedValue (source_split_columns_match parsed ⟨column, bound⟩ index)

end Airbender.Setup.SourceCaptureThetaProofs

namespace Airbender.Compiler.MachineTargets.Proofs
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false

/-- The complete split arithmetic source region has canonical membership. -/
theorem theta_source_split_member [Fact babyBearModulus.Prime] {artifact : Artifact}
    (parsed : parse SourceCaptureTheta.source = .ok artifact) (_shape : artifact.columns.size = 9)
    (index : Fin artifact.trace_len) (lower : 65536 ≤ index.val) (upper : index.val < 589824)
    (row : Vector F 9)
    (values : ∀ column : Fin 9,
      row[column] = (signedValue
        ((((artifact.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0) : F)) :
    Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericTable.toRaw.Contains #[] row := by
  have decoded := fields_of_parse SourceCaptureThetaProofs.parsed parsed
  have sameColumns : artifact.columns = SourceCaptureTheta.columns :=
    Except.ok.inj (decoded.2.symm.trans SourceCaptureThetaProofs.columns_decoded)
  have sameRow : row = (Vector.ofFn (fun column : Fin 9 =>
      signedValue ((((SourceCaptureTheta.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0))).map
      (fun value : Int => (value : F)) := by
    apply Vector.ext
    intro column bound
    simpa only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin, sameColumns] using values ⟨column, bound⟩
  change ∃ nativeIndex : Fin Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericLength,
    row = (Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericRow nativeIndex).map (fun value : Int => (value : F))
  refine ⟨⟨index.val, by change index.val < 4194304; omega⟩, ?_⟩
  rw [sameRow]
  let localIndex : Fin 524288 := ⟨index.val - 65536, by omega⟩
  have position : 65536 + localIndex.val = index.val := by dsimp [localIndex]; omega
  have canonical := SourceCaptureThetaProofs.source_split_rows parsed localIndex
  have physical : Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericRow ⟨index.val, by
      change index.val < 4194304; omega⟩ =
      (Keccak.Split.Native.Fixed.thetaRhoXorSplit.row ⟨index.val - 65536, by
        change index.val - 65536 < 524288; omega⟩).map signedValue := by
    simp only [Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericRow, dif_neg (by omega : ¬ index.val < 65536), dif_pos upper]
  rw [physical]
  have reference := congrArg (fun actual : Vector Int 9 => actual.map (fun value : Int => (value : F))) canonical
  simpa only [position] using reference

/-- Every real theta/rho source row has original canonical membership. -/
theorem split_theta_real_rows : SplitThetaRealRows := by
  intro prime artifact parsed shape row index bound values
  by_cases byte : index.val < 65536
  · exact theta_source_xor_member parsed shape index byte row values
  · by_cases split : index.val < 589824
    · exact theta_source_split_member parsed shape index (Nat.le_of_not_gt byte) split row values
    · exact theta_source_control_slot_member parsed shape index (Nat.le_of_not_gt split) bound row values

/-- Complete source coverage follows from the real rows and proved padding. -/
theorem theta_source_rows [Fact babyBearModulus.Prime] :
    FixedSetupRows SourceCaptureTheta.source Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericTable :=
  theta_source_rows_of_real_range split_theta_real_rows

end Airbender.Compiler.MachineTargets.Proofs
