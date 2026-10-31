import Airbender.Reference.Compiler.ProgramSetup
import Airbender.Review.Compiler.ProgramLogicalRows

namespace Airbender.Compiler.NativeProgramSetup
open Airbender.Reference.Compiler

/-- Native setup geometry. Both cache configurations use each exported layout. -/
def layouts : Configuration → Option ProgramSetup.Layout
  | .addSubUncached | .addSubCached => some {
      «width» := 8
      tagged := false
      decoderStart := 0
      decoderWords := 1048576
      romStart := none
      romWords := 0 }
  | .jumpBranchUncached | .jumpBranchCached => some {
      «width» := 10
      tagged := true
      decoderStart := 4456448
      decoderWords := 1048576
      romStart := none
      romWords := 0 }
  | .mulDivUncached | .mulDivCached => some {
      «width» := 9
      tagged := true
      decoderStart := 270336
      decoderWords := 1048576
      romStart := none
      romWords := 0 }
  | .shiftBinopUncached | .shiftBinopCached => some {
      «width» := 10
      tagged := true
      decoderStart := 524545
      decoderWords := 1048576
      romStart := none
      romWords := 0 }
  | .wordMemoryUncached | .wordMemoryCached => some {
      «width» := 9
      tagged := true
      decoderStart := 1048577
      decoderWords := 1048576
      romStart := some 1
      romWords := 1048576 }
  | .subwordMemoryUncached | .subwordMemoryCached => some {
      «width» := 9
      tagged := true
      decoderStart := 13238273
      decoderWords := 1048576
      romStart := none
      romWords := 0 }
  | .unifiedUncached | .unifiedCached => some {
      «width» := 10
      tagged := true
      decoderStart := 2097537
      decoderWords := 1048576
      romStart := some 590081
      romWords := 1048576 }
  | _ => none

def lookupLength : Configuration → Nat
  | .addSubUncached => MaterializedNative.AddSubUncached.native.model.imported.data.length
  | .addSubCached => MaterializedNative.AddSubCached.native.model.imported.data.length
  | .jumpBranchUncached => MaterializedNative.JumpBranchUncached.native.model.imported.data.length
  | .jumpBranchCached => MaterializedNative.JumpBranchCached.native.model.imported.data.length
  | .mulDivUncached => MaterializedNative.MulDivUncached.native.model.imported.data.length
  | .mulDivCached => MaterializedNative.MulDivCached.native.model.imported.data.length
  | .shiftBinopUncached => MaterializedNative.ShiftBinopUncached.native.model.imported.data.length
  | .shiftBinopCached => MaterializedNative.ShiftBinopCached.native.model.imported.data.length
  | .wordMemoryUncached => MaterializedNative.WordMemoryUncached.native.model.imported.data.length
  | .wordMemoryCached => MaterializedNative.WordMemoryCached.native.model.imported.data.length
  | .subwordMemoryUncached => MaterializedNative.SubwordMemoryUncached.native.model.imported.data.length
  | .subwordMemoryCached => MaterializedNative.SubwordMemoryCached.native.model.imported.data.length
  | .unifiedUncached => MaterializedNative.UnifiedUncached.native.model.imported.data.length
  | .unifiedCached => MaterializedNative.UnifiedCached.native.model.imported.data.length
  | _ => 0

def genericWidth : Configuration → Nat
  | .addSubUncached => TableNative.AddSubUncached.native.genericSetupColumns.length
  | .addSubCached => TableNative.AddSubCached.native.genericSetupColumns.length
  | .jumpBranchUncached => TableNative.JumpBranchUncached.native.genericSetupColumns.length
  | .jumpBranchCached => TableNative.JumpBranchCached.native.genericSetupColumns.length
  | .mulDivUncached => TableNative.MulDivUncached.native.genericSetupColumns.length
  | .mulDivCached => TableNative.MulDivCached.native.genericSetupColumns.length
  | .shiftBinopUncached => TableNative.ShiftBinopUncached.native.genericSetupColumns.length
  | .shiftBinopCached => TableNative.ShiftBinopCached.native.genericSetupColumns.length
  | .wordMemoryUncached => TableNative.WordMemoryUncached.native.genericSetupColumns.length
  | .wordMemoryCached => TableNative.WordMemoryCached.native.genericSetupColumns.length
  | .subwordMemoryUncached => TableNative.SubwordMemoryUncached.native.genericSetupColumns.length
  | .subwordMemoryCached => TableNative.SubwordMemoryCached.native.genericSetupColumns.length
  | .unifiedUncached => TableNative.UnifiedUncached.native.genericSetupColumns.length
  | .unifiedCached => TableNative.UnifiedCached.native.genericSetupColumns.length
  | _ => 0

/-- Read the unchanged captured row at every valid native index. -/
noncomputable def retainedRows (configuration : Configuration) (group : Fin 3)
    (index : Nat) : List Source.BaseField :=
  match configuration with
  | .addSubUncached =>
    if bounded : index < MaterializedNative.AddSubUncached.native.model.imported.data.length then
      MaterializedNative.AddSubUncached.native.model.fields
        (([TableNative.AddSubUncached.native.genericSetupColumns,
           TableNative.AddSubUncached.native.range16SetupColumns,
           TableNative.AddSubUncached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .addSubCached =>
    if bounded : index < MaterializedNative.AddSubCached.native.model.imported.data.length then
      MaterializedNative.AddSubCached.native.model.fields
        (([TableNative.AddSubCached.native.genericSetupColumns,
           TableNative.AddSubCached.native.range16SetupColumns,
           TableNative.AddSubCached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .jumpBranchUncached =>
    if bounded : index < MaterializedNative.JumpBranchUncached.native.model.imported.data.length then
      MaterializedNative.JumpBranchUncached.native.model.fields
        (([TableNative.JumpBranchUncached.native.genericSetupColumns,
           TableNative.JumpBranchUncached.native.range16SetupColumns,
           TableNative.JumpBranchUncached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .jumpBranchCached =>
    if bounded : index < MaterializedNative.JumpBranchCached.native.model.imported.data.length then
      MaterializedNative.JumpBranchCached.native.model.fields
        (([TableNative.JumpBranchCached.native.genericSetupColumns,
           TableNative.JumpBranchCached.native.range16SetupColumns,
           TableNative.JumpBranchCached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .mulDivUncached =>
    if bounded : index < MaterializedNative.MulDivUncached.native.model.imported.data.length then
      MaterializedNative.MulDivUncached.native.model.fields
        (([TableNative.MulDivUncached.native.genericSetupColumns,
           TableNative.MulDivUncached.native.range16SetupColumns,
           TableNative.MulDivUncached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .mulDivCached =>
    if bounded : index < MaterializedNative.MulDivCached.native.model.imported.data.length then
      MaterializedNative.MulDivCached.native.model.fields
        (([TableNative.MulDivCached.native.genericSetupColumns,
           TableNative.MulDivCached.native.range16SetupColumns,
           TableNative.MulDivCached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .shiftBinopUncached =>
    if bounded : index < MaterializedNative.ShiftBinopUncached.native.model.imported.data.length then
      MaterializedNative.ShiftBinopUncached.native.model.fields
        (([TableNative.ShiftBinopUncached.native.genericSetupColumns,
           TableNative.ShiftBinopUncached.native.range16SetupColumns,
           TableNative.ShiftBinopUncached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .shiftBinopCached =>
    if bounded : index < MaterializedNative.ShiftBinopCached.native.model.imported.data.length then
      MaterializedNative.ShiftBinopCached.native.model.fields
        (([TableNative.ShiftBinopCached.native.genericSetupColumns,
           TableNative.ShiftBinopCached.native.range16SetupColumns,
           TableNative.ShiftBinopCached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .wordMemoryUncached =>
    if bounded : index < MaterializedNative.WordMemoryUncached.native.model.imported.data.length then
      MaterializedNative.WordMemoryUncached.native.model.fields
        (([TableNative.WordMemoryUncached.native.genericSetupColumns,
           TableNative.WordMemoryUncached.native.range16SetupColumns,
           TableNative.WordMemoryUncached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .wordMemoryCached =>
    if bounded : index < MaterializedNative.WordMemoryCached.native.model.imported.data.length then
      MaterializedNative.WordMemoryCached.native.model.fields
        (([TableNative.WordMemoryCached.native.genericSetupColumns,
           TableNative.WordMemoryCached.native.range16SetupColumns,
           TableNative.WordMemoryCached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .subwordMemoryUncached =>
    if bounded : index < MaterializedNative.SubwordMemoryUncached.native.model.imported.data.length then
      MaterializedNative.SubwordMemoryUncached.native.model.fields
        (([TableNative.SubwordMemoryUncached.native.genericSetupColumns,
           TableNative.SubwordMemoryUncached.native.range16SetupColumns,
           TableNative.SubwordMemoryUncached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .subwordMemoryCached =>
    if bounded : index < MaterializedNative.SubwordMemoryCached.native.model.imported.data.length then
      MaterializedNative.SubwordMemoryCached.native.model.fields
        (([TableNative.SubwordMemoryCached.native.genericSetupColumns,
           TableNative.SubwordMemoryCached.native.range16SetupColumns,
           TableNative.SubwordMemoryCached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .unifiedUncached =>
    if bounded : index < MaterializedNative.UnifiedUncached.native.model.imported.data.length then
      MaterializedNative.UnifiedUncached.native.model.fields
        (([TableNative.UnifiedUncached.native.genericSetupColumns,
           TableNative.UnifiedUncached.native.range16SetupColumns,
           TableNative.UnifiedUncached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .unifiedCached =>
    if bounded : index < MaterializedNative.UnifiedCached.native.model.imported.data.length then
      MaterializedNative.UnifiedCached.native.model.fields
        (([TableNative.UnifiedCached.native.genericSetupColumns,
           TableNative.UnifiedCached.native.range16SetupColumns,
           TableNative.UnifiedCached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | _ => []

/-- Build lookup rows from public decoder columns and a public ROM word function. -/
noncomputable def rows (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) : ProgramLookupRows :=
  fun configuration group index =>
    match layouts configuration with
    | none => retainedRows configuration group index
    | some layout => ProgramSetup.groupRows layout (retainedRows configuration)
        (decoder configuration) wordAt group index

def ValidGeometry (configuration : Configuration) : Prop :=
  match layouts configuration with
  | none => True
  | some layout =>
    0 < layout.width ∧ layout.width = genericWidth configuration ∧
      layout.decoderStart + layout.decoderWords ≤ lookupLength configuration ∧
      layout.decoderWords = 1048576 ∧ layout.romWords ≤ 1048576 ∧
      match layout.romStart with
      | none => layout.romWords = 0
      | some regionStart => regionStart + layout.romWords ≤ layout.decoderStart

end Airbender.Compiler.NativeProgramSetup
