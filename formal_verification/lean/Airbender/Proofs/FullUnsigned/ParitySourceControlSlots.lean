import Mathlib.Tactic.IntervalCases
import Airbender.Proofs.FullUnsigned.ParitySourcePrefixRead
import Airbender.Data.Setup.Keccak.ColumnParityGeneric
import Airbender.Proofs.FullUnsigned.CapturedSetup

namespace Airbender.Setup.SourceCaptureParityProofs
set_option warningAsError true
set_option Elab.async false
-- The finite control and slot domain has 244 rows and eight fields.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem retained_part0 : ∀ index : Fin 31,
    (Vector.ofFn fun column : Fin 8 => signedValue
      ((getFromBlocks (prefixBlocks column) (65536 + (0 + index.val))).getD 0)) =
      Airbender.Keccak.Split.Native.Fixed.columnParityGenericRow ⟨65536 + (0 + index.val), by
        change 65536 + (0 + index.val) < 4194304; omega⟩ := by
  decide +kernel

private theorem retained_part1 : ∀ index : Fin 31,
    (Vector.ofFn fun column : Fin 8 => signedValue
      ((getFromBlocks (prefixBlocks column) (65536 + (31 + index.val))).getD 0)) =
      Airbender.Keccak.Split.Native.Fixed.columnParityGenericRow ⟨65536 + (31 + index.val), by
        change 65536 + (31 + index.val) < 4194304; omega⟩ := by
  decide +kernel

private theorem retained_part2 : ∀ index : Fin 31,
    (Vector.ofFn fun column : Fin 8 => signedValue
      ((getFromBlocks (prefixBlocks column) (65536 + (62 + index.val))).getD 0)) =
      Airbender.Keccak.Split.Native.Fixed.columnParityGenericRow ⟨65536 + (62 + index.val), by
        change 65536 + (62 + index.val) < 4194304; omega⟩ := by
  decide +kernel

private theorem retained_part3 : ∀ index : Fin 31,
    (Vector.ofFn fun column : Fin 8 => signedValue
      ((getFromBlocks (prefixBlocks column) (65536 + (93 + index.val))).getD 0)) =
      Airbender.Keccak.Split.Native.Fixed.columnParityGenericRow ⟨65536 + (93 + index.val), by
        change 65536 + (93 + index.val) < 4194304; omega⟩ := by
  decide +kernel

private theorem retained_part4 : ∀ index : Fin 31,
    (Vector.ofFn fun column : Fin 8 => signedValue
      ((getFromBlocks (prefixBlocks column) (65536 + (124 + index.val))).getD 0)) =
      Airbender.Keccak.Split.Native.Fixed.columnParityGenericRow ⟨65536 + (124 + index.val), by
        change 65536 + (124 + index.val) < 4194304; omega⟩ := by
  decide +kernel

private theorem retained_part5 : ∀ index : Fin 31,
    (Vector.ofFn fun column : Fin 8 => signedValue
      ((getFromBlocks (prefixBlocks column) (65536 + (155 + index.val))).getD 0)) =
      Airbender.Keccak.Split.Native.Fixed.columnParityGenericRow ⟨65536 + (155 + index.val), by
        change 65536 + (155 + index.val) < 4194304; omega⟩ := by
  decide +kernel

private theorem retained_part6 : ∀ index : Fin 31,
    (Vector.ofFn fun column : Fin 8 => signedValue
      ((getFromBlocks (prefixBlocks column) (65536 + (186 + index.val))).getD 0)) =
      Airbender.Keccak.Split.Native.Fixed.columnParityGenericRow ⟨65536 + (186 + index.val), by
        change 65536 + (186 + index.val) < 4194304; omega⟩ := by
  decide +kernel

private theorem retained_part7 : ∀ index : Fin 27,
    (Vector.ofFn fun column : Fin 8 => signedValue
      ((getFromBlocks (prefixBlocks column) (65536 + (217 + index.val))).getD 0)) =
      Airbender.Keccak.Split.Native.Fixed.columnParityGenericRow ⟨65536 + (217 + index.val), by
        change 65536 + (217 + index.val) < 4194304; omega⟩ := by
  decide +kernel

private theorem retained_rows : ∀ index : Fin 244,
    (Vector.ofFn fun column : Fin 8 => signedValue
      ((getFromBlocks (prefixBlocks column) (65536 + index.val)).getD 0)) =
      Airbender.Keccak.Split.Native.Fixed.columnParityGenericRow ⟨65536 + index.val, by
        change 65536 + index.val < 4194304; omega⟩ := by
  intro index
  have groupBound : index.val / 31 < 8 := by omega
  generalize groupEq : index.val / 31 = group at *
  interval_cases group
  · let localIndex : Fin 31 := ⟨index.val - 0, by omega⟩
    have position : 0 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [position] using retained_part0 localIndex
  · let localIndex : Fin 31 := ⟨index.val - 31, by omega⟩
    have position : 31 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [position] using retained_part1 localIndex
  · let localIndex : Fin 31 := ⟨index.val - 62, by omega⟩
    have position : 62 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [position] using retained_part2 localIndex
  · let localIndex : Fin 31 := ⟨index.val - 93, by omega⟩
    have position : 93 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [position] using retained_part3 localIndex
  · let localIndex : Fin 31 := ⟨index.val - 124, by omega⟩
    have position : 124 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [position] using retained_part4 localIndex
  · let localIndex : Fin 31 := ⟨index.val - 155, by omega⟩
    have position : 155 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [position] using retained_part5 localIndex
  · let localIndex : Fin 31 := ⟨index.val - 186, by omega⟩
    have position : 186 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [position] using retained_part6 localIndex
  · let localIndex : Fin 27 := ⟨index.val - 217, by omega⟩
    have position : 217 + localIndex.val = index.val := by dsimp [localIndex]; omega
    simpa only [position] using retained_part7 localIndex

/-- Both original parity control regions have exact source-row values. -/
theorem source_control_slot_rows (index : Fin 244) :
    (Vector.ofFn fun column : Fin 8 => signedValue
      ((((SourceCaptureParity.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val)).getD 0)) =
      Airbender.Keccak.Split.Native.Fixed.columnParityGenericRow ⟨65536 + index.val, by
        change 65536 + index.val < 4194304; omega⟩ := by
  rw [← retained_rows index]
  apply Vector.ext
  intro column bound
  simp only [Vector.getElem_ofFn]
  exact congrArg (fun value : Option Nat => signedValue (value.getD 0))
    (source_prefix_get ⟨column, bound⟩ ⟨65536 + index.val, by omega⟩)

end Airbender.Setup.SourceCaptureParityProofs

namespace Airbender.Compiler.MachineTargets.Proofs
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false

/-- Parsing supplies original canonical membership for parity slots and control. -/
theorem parity_source_control_slot_member [Fact babyBearModulus.Prime] {artifact : Artifact}
    (parsed : parse SourceCaptureParity.source = .ok artifact) (_shape : artifact.columns.size = 8)
    (index : Fin artifact.trace_len) (lower : 65536 ≤ index.val) (upper : index.val < 65780)
    (row : Vector F 8)
    (values : ∀ column : Fin 8,
      row[column] = (signedValue
        ((((artifact.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0) : F)) :
    Keccak.Split.Native.Fixed.columnParityGenericTable.toRaw.Contains #[] row := by
  have decoded := fields_of_parse SourceCaptureParityProofs.parsed parsed
  have sameColumns : artifact.columns = SourceCaptureParity.columns :=
    Except.ok.inj (decoded.2.symm.trans SourceCaptureParityProofs.columns_decoded)
  have sameRow : row = (Vector.ofFn (fun column : Fin 8 =>
      signedValue ((((SourceCaptureParity.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0))).map
      (fun value : Int => (value : F)) := by
    apply Vector.ext
    intro column bound
    simpa only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin, sameColumns] using values ⟨column, bound⟩
  change ∃ nativeIndex : Fin Keccak.Split.Native.Fixed.columnParityGenericLength,
    row = (Keccak.Split.Native.Fixed.columnParityGenericRow nativeIndex).map (fun value : Int => (value : F))
  refine ⟨⟨index.val, by change index.val < 4194304; omega⟩, ?_⟩
  rw [sameRow]
  let localIndex : Fin 244 := ⟨index.val - 65536, by omega⟩
  have position : 65536 + localIndex.val = index.val := by dsimp [localIndex]; omega
  have reference := congrArg (fun actual : Vector Int 8 => actual.map (fun value : Int => (value : F)))
    (SourceCaptureParityProofs.source_control_slot_rows localIndex)
  simpa only [position] using reference

end Airbender.Compiler.MachineTargets.Proofs
