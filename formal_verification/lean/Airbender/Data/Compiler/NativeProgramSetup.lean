import Airbender.Reference.Compiler.ProgramSetup
import Airbender.Review.Compiler.ProgramLogicalRows

namespace Airbender.Compiler.NativeProgramSetup
open Airbender.Reference.Compiler

/-- Native setup geometry. Production uses the cached layout. -/
def layouts : Configuration → Option ProgramSetup.Layout
  | .addSubCached => some {
      «width» := 8
      tagged := false
      decoderStart := 0
      decoderWords := 1048576
      romStart := none
      romWords := 0 }
  | .jumpBranchCached => some {
      «width» := 10
      tagged := true
      decoderStart := 4456448
      decoderWords := 1048576
      romStart := none
      romWords := 0 }
  | .mulDivCached => some {
      «width» := 9
      tagged := true
      decoderStart := 270336
      decoderWords := 1048576
      romStart := none
      romWords := 0 }
  | .shiftBinopCached => some {
      «width» := 10
      tagged := true
      decoderStart := 524545
      decoderWords := 1048576
      romStart := none
      romWords := 0 }
  | .wordMemoryCached => some {
      «width» := 9
      tagged := true
      decoderStart := 1048577
      decoderWords := 1048576
      romStart := some 1
      romWords := 1048576 }
  | .subwordMemoryCached => some {
      «width» := 9
      tagged := true
      decoderStart := 13238273
      decoderWords := 1048576
      romStart := none
      romWords := 0 }
  | .unifiedCached => some {
      «width» := 10
      tagged := true
      decoderStart := 2097537
      decoderWords := 1048576
      romStart := some 590081
      romWords := 1048576 }
  | _ => none

def lookupLength : Configuration → Nat
  | .addSubCached => MaterializedNative.AddSubCached.native.model.imported.data.length
  | .jumpBranchCached => MaterializedNative.JumpBranchCached.native.model.imported.data.length
  | .mulDivCached => MaterializedNative.MulDivCached.native.model.imported.data.length
  | .shiftBinopCached => MaterializedNative.ShiftBinopCached.native.model.imported.data.length
  | .wordMemoryCached => MaterializedNative.WordMemoryCached.native.model.imported.data.length
  | .subwordMemoryCached => MaterializedNative.SubwordMemoryCached.native.model.imported.data.length
  | .unifiedCached => MaterializedNative.UnifiedCached.native.model.imported.data.length
  | _ => 0

def genericWidth : Configuration → Nat
  | .addSubCached => TableNative.AddSubCached.native.genericSetupColumns.length
  | .jumpBranchCached => TableNative.JumpBranchCached.native.genericSetupColumns.length
  | .mulDivCached => TableNative.MulDivCached.native.genericSetupColumns.length
  | .shiftBinopCached => TableNative.ShiftBinopCached.native.genericSetupColumns.length
  | .wordMemoryCached => TableNative.WordMemoryCached.native.genericSetupColumns.length
  | .subwordMemoryCached => TableNative.SubwordMemoryCached.native.genericSetupColumns.length
  | .unifiedCached => TableNative.UnifiedCached.native.genericSetupColumns.length
  | _ => 0

/-- Read the unchanged captured row at every valid native index. -/
noncomputable def retainedRows (configuration : Configuration) (group : Fin 3)
    (index : Nat) : List Source.BaseField :=
  match configuration with
  | .addSubCached =>
    if bounded : index < MaterializedNative.AddSubCached.native.model.imported.data.length then
      MaterializedNative.AddSubCached.native.model.fields
        (([TableNative.AddSubCached.native.genericSetupColumns,
           TableNative.AddSubCached.native.range16SetupColumns,
           TableNative.AddSubCached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .jumpBranchCached =>
    if bounded : index < MaterializedNative.JumpBranchCached.native.model.imported.data.length then
      MaterializedNative.JumpBranchCached.native.model.fields
        (([TableNative.JumpBranchCached.native.genericSetupColumns,
           TableNative.JumpBranchCached.native.range16SetupColumns,
           TableNative.JumpBranchCached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .mulDivCached =>
    if bounded : index < MaterializedNative.MulDivCached.native.model.imported.data.length then
      MaterializedNative.MulDivCached.native.model.fields
        (([TableNative.MulDivCached.native.genericSetupColumns,
           TableNative.MulDivCached.native.range16SetupColumns,
           TableNative.MulDivCached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .shiftBinopCached =>
    if bounded : index < MaterializedNative.ShiftBinopCached.native.model.imported.data.length then
      MaterializedNative.ShiftBinopCached.native.model.fields
        (([TableNative.ShiftBinopCached.native.genericSetupColumns,
           TableNative.ShiftBinopCached.native.range16SetupColumns,
           TableNative.ShiftBinopCached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .wordMemoryCached =>
    if bounded : index < MaterializedNative.WordMemoryCached.native.model.imported.data.length then
      MaterializedNative.WordMemoryCached.native.model.fields
        (([TableNative.WordMemoryCached.native.genericSetupColumns,
           TableNative.WordMemoryCached.native.range16SetupColumns,
           TableNative.WordMemoryCached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
    else []
  | .subwordMemoryCached =>
    if bounded : index < MaterializedNative.SubwordMemoryCached.native.model.imported.data.length then
      MaterializedNative.SubwordMemoryCached.native.model.fields
        (([TableNative.SubwordMemoryCached.native.genericSetupColumns,
           TableNative.SubwordMemoryCached.native.range16SetupColumns,
           TableNative.SubwordMemoryCached.native.timestampSetupColumns]).get group) ⟨index, bounded⟩
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

-- Emit these equations once, in their source module.
attribute [local simp] layouts lookupLength genericWidth retainedRows rows ValidGeometry

end Airbender.Compiler.NativeProgramSetup
