import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BlakeGUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodeField : Source.MemoryField → NumericPolynomialChecks.Data := (fun field : Source.MemoryField => NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement))

noncomputable def ramSource := Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields.map encodeField

numeric_data_binding ramLeaf0 : (data.ram.drop 0).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields.drop 0).take 16).map encodeField

theorem ramSlice0 : (data.ram.drop 0).take 16 = (ramSource.drop 0).take 16 :=
  ramLeaf0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields encodeField 0 16)

numeric_data_binding ramLeaf16 : (data.ram.drop 16).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields.drop 16).take 16).map encodeField

theorem ramSlice16 : (data.ram.drop 16).take 16 = (ramSource.drop 16).take 16 :=
  ramLeaf16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields encodeField 16 16)

numeric_data_binding ramLeaf32 : (data.ram.drop 32).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields.drop 32).take 16).map encodeField

theorem ramSlice32 : (data.ram.drop 32).take 16 = (ramSource.drop 32).take 16 :=
  ramLeaf32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields encodeField 32 16)

numeric_data_binding ramLeaf48 : (data.ram.drop 48).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields.drop 48).take 16).map encodeField

theorem ramSlice48 : (data.ram.drop 48).take 16 = (ramSource.drop 48).take 16 :=
  ramLeaf48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields encodeField 48 16)

numeric_data_binding ramLeaf64 : (data.ram.drop 64).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields.drop 64).take 16).map encodeField

theorem ramSlice64 : (data.ram.drop 64).take 16 = (ramSource.drop 64).take 16 :=
  ramLeaf64.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields encodeField 64 16)

numeric_data_binding ramLeaf80 : (data.ram.drop 80).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields.drop 80).take 16).map encodeField

theorem ramSlice80 : (data.ram.drop 80).take 16 = (ramSource.drop 80).take 16 :=
  ramLeaf80.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields encodeField 80 16)

numeric_data_binding ramLeaf96 : (data.ram.drop 96).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields.drop 96).take 16).map encodeField

theorem ramSlice96 : (data.ram.drop 96).take 16 = (ramSource.drop 96).take 16 :=
  ramLeaf96.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields encodeField 96 16)

numeric_data_binding ramLeaf112 : (data.ram.drop 112).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields.drop 112).take 16).map encodeField

theorem ramSlice112 : (data.ram.drop 112).take 16 = (ramSource.drop 112).take 16 :=
  ramLeaf112.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields encodeField 112 16)

numeric_data_binding ramLeaf128 : (data.ram.drop 128).take 12 =
  ((Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields.drop 128).take 12).map encodeField

theorem ramSlice128 : (data.ram.drop 128).take 12 = (ramSource.drop 128).take 12 :=
  ramLeaf128.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields encodeField 128 12)

theorem ramNode0_32 : (data.ram.drop 0).take 32 = (ramSource.drop 0).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 0 16 16 ramSlice0 ramSlice16

theorem ramNode32_32 : (data.ram.drop 32).take 32 = (ramSource.drop 32).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 32 16 16 ramSlice32 ramSlice48

theorem ramNode0_64 : (data.ram.drop 0).take 64 = (ramSource.drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 0 32 32 ramNode0_32 ramNode32_32

theorem ramNode64_32 : (data.ram.drop 64).take 32 = (ramSource.drop 64).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 64 16 16 ramSlice64 ramSlice80

theorem ramNode112_28 : (data.ram.drop 112).take 28 = (ramSource.drop 112).take 28 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 112 16 12 ramSlice112 ramSlice128

theorem ramNode96_44 : (data.ram.drop 96).take 44 = (ramSource.drop 96).take 44 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 96 16 28 ramSlice96 ramNode112_28

theorem ramNode64_76 : (data.ram.drop 64).take 76 = (ramSource.drop 64).take 76 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 64 32 44 ramNode64_32 ramNode96_44

theorem ramNode0_140 : (data.ram.drop 0).take 140 = (ramSource.drop 0).take 140 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 0 64 76 ramNode0_64 ramNode64_76

theorem ramLength : Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields.length = 140 := by decide +kernel

theorem ram_binding : data.ram = ramSource :=
  NumericQueryFrameChecks.complete_binding data.ram ramSource 140
    (by decide +kernel) (by rw [ramSource, List.length_map, ramLength]) ramNode0_140

numeric_data_binding initialization_binding : data.initialization = Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.initializationFields.map encodeField

numeric_data_binding execution_binding : data.execution = Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.executeFields.map encodeField

end Airbender.Compiler.MemoryFrameChecks.BlakeGUncached
