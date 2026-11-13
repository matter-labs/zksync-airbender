module
public import Proven.Compiler.DecoderRows
public import Proven.Compiler.Lookups.NativeRanges

@[expose] public section
namespace Airbender.Compiler.NativePublicSetup.Proofs
open Airbender Trace NativeArithmetic Metadata
set_option warningAsError true

/-- A zero unused payload coordinate excludes every public decoder row and sentinel.
    The remaining native row is in the fixed prefix or is zero commitment padding. -/
theorem fixed_or_padding {initial : RV.State} {program : List RVMachineProgramEntry}
    {actual : ProgramLookupRows} (bound : Bound initial program actual)
    (family : RVMachineDecoderFamily) (isTagged : tagged family = true) (fields : List F)
    (member : Contains initial program family 0 fields)
    (unused : (fields[maskColumn family]?).getD 0 = 0) :
    (∃ index < offset family, fields = fixedRow family (ROM.wordsRV initial) index) ∨
      fields = List.replicate (width family) 0 := by
  obtain ⟨index, same⟩ := member
  change fields = genericRow family initial program index.val at same
  unfold genericRow at same
  dsimp only at same
  rw [offset_binding, width_binding] at same
  by_cases isFixed : index.val < offset family
  · exact Or.inl ⟨index.val, isFixed, by simpa only [ite_eq_left isFixed] using same⟩
  · rw [ite_eq_right isFixed] at same
    by_cases decoder : index.val - offset family < decoderCapacity
    · rw [ite_eq_left decoder] at same
      have selected := congrArg (fun row : List F => (row[maskColumn family]?).getD 0) same
      exact False.elim ((decoder_mask_nonzero bound family (index.val - offset family))
        (selected.symm.trans unused))
    · rw [ite_eq_right decoder] at same
      exact Or.inr (by simpa only [isTagged, ite_true] using same)

end Airbender.Compiler.NativePublicSetup.Proofs

namespace Airbender.Compiler.NativeFixedMembership
open Airbender Trace NativeArithmetic NativePublicSetup NativePublicSetup.Proofs NativePublicSetup.Metadata
set_option warningAsError true

/-- Native fixed or zero rows give exactly the retained shift-table membership. -/
theorem shift_contains {initial : RV.State} {program : List RVMachineProgramEntry}
    {actual : ProgramLookupRows} (bound : Bound initial program actual) (value : Vector F 10)
    (member : Contains initial program (.pooled .shiftBinop) 0 value.toList)
    (unused : value[8] = 0) (provided : Array (Vector F 10)) :
    (Verification.shiftBinopTable (p := babyBearModulus)).Contains provided value := by
  have zero : (value.toList[maskColumn (.pooled .shiftBinop)]?).getD 0 = 0 := by
    simpa [maskColumn, hasFunct3] using unused
  rcases fixed_or_padding bound (.pooled .shiftBinop) rfl value.toList member zero with fixed | padding
  · obtain ⟨index, _, same⟩ := fixed
    change ∃ row : Fin 524545, value = (Verification.shiftBinopRow row).map (fun (n : Nat) => (n : F))
    refine ⟨Fin.ofNat 524545 index, ?_⟩
    apply Vector.toList_inj.mp
    simpa only [NativePublicSetup.fixedRow, Vector.toList_map] using same
  · change ∃ row : Fin 524545, value = (Verification.shiftBinopRow row).map (fun (n : Nat) => (n : F))
    refine ⟨0, ?_⟩
    apply Vector.toList_inj.mp
    simpa [width, hasFunct3, Verification.shiftBinopRow] using padding

/-- Native subword rows retain the full public-ROM table interpretation. -/
theorem subword_contains {initial : RV.State} {program : List RVMachineProgramEntry}
    {actual : ProgramLookupRows} (bound : Bound initial program actual) (value : Vector F 9)
    (member : Contains initial program (.pooled .subwordMemory) 0 value.toList)
    (unused : value[7] = 0) (provided : Array (Vector F 9)) :
    (Verification.subwordTable (p := babyBearModulus) (ROM.wordsRV initial)).Contains provided value := by
  have zero : (value.toList[maskColumn (.pooled .subwordMemory)]?).getD 0 = 0 := by
    simpa [maskColumn, hasFunct3] using unused
  rcases fixed_or_padding bound (.pooled .subwordMemory) rfl value.toList member zero with fixed | padding
  · obtain ⟨index, _, same⟩ := fixed
    change ∃ row : Fin 13238273, value = (Verification.subwordRow (ROM.wordsRV initial) row).map (fun (n : Nat) => (n : F))
    refine ⟨Fin.ofNat 13238273 index, ?_⟩
    apply Vector.toList_inj.mp
    simpa only [NativePublicSetup.fixedRow, Vector.toList_map] using same
  · change ∃ row : Fin 13238273, value = (Verification.subwordRow (ROM.wordsRV initial) row).map (fun (n : Nat) => (n : F))
    refine ⟨0, ?_⟩
    apply Vector.toList_inj.mp
    simpa [width, hasFunct3, Verification.subwordRow, Verification.subwordDataRow] using padding

/-- Reordering native unified regions preserves all logical fixed and ROM rows. -/
theorem unified_contains {initial : RV.State} {program : List RVMachineProgramEntry}
    {actual : ProgramLookupRows} (bound : Bound initial program actual) (value : Vector F 10)
    (member : Contains initial program .unified 0 value.toList)
    (unused : value[8] = 0) (provided : Array (Vector F 10)) :
    (UnifiedReduced.Setup.tableRV (p := babyBearModulus) initial).Contains provided value := by
  have zero : (value.toList[maskColumn .unified]?).getD 0 = 0 := by
    simpa [maskColumn, hasFunct3] using unused
  rcases fixed_or_padding bound .unified rfl value.toList member zero with fixed | padding
  · obtain ⟨index, _, same⟩ := fixed
    change ∃ row : Fin 2097537, value = (UnifiedReduced.Setup.rowWith (ROM.wordsRV initial) row).map (fun (n : Nat) => (n : F))
    refine ⟨NativeFixedRows.unifiedIndex (Fin.ofNat 2097537 index), ?_⟩
    apply Vector.toList_inj.mp
    simpa only [NativePublicSetup.fixedRow, NativeFixedRows.unified, Vector.toList_map] using same
  · change ∃ row : Fin 2097537, value = (UnifiedReduced.Setup.rowWith (ROM.wordsRV initial) row).map (fun (n : Nat) => (n : F))
    refine ⟨0, ?_⟩
    apply Vector.toList_inj.mp
    simpa [width, hasFunct3, UnifiedReduced.Setup.rowWith, UnifiedReduced.Setup.fixedRow,
      UnifiedReduced.Setup.binaryRow, UnifiedReduced.Setup.binaryTag, Verification.shiftBinopRow] using padding

end Airbender.Compiler.NativeFixedMembership
