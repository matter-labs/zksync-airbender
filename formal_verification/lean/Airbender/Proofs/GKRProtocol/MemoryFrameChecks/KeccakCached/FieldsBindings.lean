import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.KeccakCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodeField : Source.MemoryField → NumericPolynomialChecks.Data := (fun field : Source.MemoryField => NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.MemoryNative.KeccakCached.native.sourcePlacement))

noncomputable def ramSource := Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields.map encodeField

numeric_data_binding ramLeaf0 : (data.ram.drop 0).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields.drop 0).take 16).map encodeField

theorem ramSlice0 : (data.ram.drop 0).take 16 = (ramSource.drop 0).take 16 :=
  ramLeaf0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields encodeField 0 16)

numeric_data_binding ramLeaf16 : (data.ram.drop 16).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields.drop 16).take 16).map encodeField

theorem ramSlice16 : (data.ram.drop 16).take 16 = (ramSource.drop 16).take 16 :=
  ramLeaf16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields encodeField 16 16)

numeric_data_binding ramLeaf32 : (data.ram.drop 32).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields.drop 32).take 16).map encodeField

theorem ramSlice32 : (data.ram.drop 32).take 16 = (ramSource.drop 32).take 16 :=
  ramLeaf32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields encodeField 32 16)

numeric_data_binding ramLeaf48 : (data.ram.drop 48).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields.drop 48).take 16).map encodeField

theorem ramSlice48 : (data.ram.drop 48).take 16 = (ramSource.drop 48).take 16 :=
  ramLeaf48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields encodeField 48 16)

numeric_data_binding ramLeaf64 : (data.ram.drop 64).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields.drop 64).take 16).map encodeField

theorem ramSlice64 : (data.ram.drop 64).take 16 = (ramSource.drop 64).take 16 :=
  ramLeaf64.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields encodeField 64 16)

numeric_data_binding ramLeaf80 : (data.ram.drop 80).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields.drop 80).take 16).map encodeField

theorem ramSlice80 : (data.ram.drop 80).take 16 = (ramSource.drop 80).take 16 :=
  ramLeaf80.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields encodeField 80 16)

numeric_data_binding ramLeaf96 : (data.ram.drop 96).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields.drop 96).take 16).map encodeField

theorem ramSlice96 : (data.ram.drop 96).take 16 = (ramSource.drop 96).take 16 :=
  ramLeaf96.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields encodeField 96 16)

numeric_data_binding ramLeaf112 : (data.ram.drop 112).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields.drop 112).take 16).map encodeField

theorem ramSlice112 : (data.ram.drop 112).take 16 = (ramSource.drop 112).take 16 :=
  ramLeaf112.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields encodeField 112 16)

numeric_data_binding ramLeaf128 : (data.ram.drop 128).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields.drop 128).take 16).map encodeField

theorem ramSlice128 : (data.ram.drop 128).take 16 = (ramSource.drop 128).take 16 :=
  ramLeaf128.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields encodeField 128 16)

numeric_data_binding ramLeaf144 : (data.ram.drop 144).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields.drop 144).take 16).map encodeField

theorem ramSlice144 : (data.ram.drop 144).take 16 = (ramSource.drop 144).take 16 :=
  ramLeaf144.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields encodeField 144 16)

numeric_data_binding ramLeaf160 : (data.ram.drop 160).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields.drop 160).take 16).map encodeField

theorem ramSlice160 : (data.ram.drop 160).take 16 = (ramSource.drop 160).take 16 :=
  ramLeaf160.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields encodeField 160 16)

numeric_data_binding ramLeaf176 : (data.ram.drop 176).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields.drop 176).take 16).map encodeField

theorem ramSlice176 : (data.ram.drop 176).take 16 = (ramSource.drop 176).take 16 :=
  ramLeaf176.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields encodeField 176 16)

numeric_data_binding ramLeaf192 : (data.ram.drop 192).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields.drop 192).take 16).map encodeField

theorem ramSlice192 : (data.ram.drop 192).take 16 = (ramSource.drop 192).take 16 :=
  ramLeaf192.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields encodeField 192 16)

numeric_data_binding ramLeaf208 : (data.ram.drop 208).take 2 =
  ((Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields.drop 208).take 2).map encodeField

theorem ramSlice208 : (data.ram.drop 208).take 2 = (ramSource.drop 208).take 2 :=
  ramLeaf208.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields encodeField 208 2)

theorem ramNode16_32 : (data.ram.drop 16).take 32 = (ramSource.drop 16).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 16 16 16 ramSlice16 ramSlice32

theorem ramNode0_48 : (data.ram.drop 0).take 48 = (ramSource.drop 0).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 0 16 32 ramSlice0 ramNode16_32

theorem ramNode48_32 : (data.ram.drop 48).take 32 = (ramSource.drop 48).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 48 16 16 ramSlice48 ramSlice64

theorem ramNode80_32 : (data.ram.drop 80).take 32 = (ramSource.drop 80).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 80 16 16 ramSlice80 ramSlice96

theorem ramNode48_64 : (data.ram.drop 48).take 64 = (ramSource.drop 48).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 48 32 32 ramNode48_32 ramNode80_32

theorem ramNode0_112 : (data.ram.drop 0).take 112 = (ramSource.drop 0).take 112 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 0 48 64 ramNode0_48 ramNode48_64

theorem ramNode128_32 : (data.ram.drop 128).take 32 = (ramSource.drop 128).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 128 16 16 ramSlice128 ramSlice144

theorem ramNode112_48 : (data.ram.drop 112).take 48 = (ramSource.drop 112).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 112 16 32 ramSlice112 ramNode128_32

theorem ramNode160_32 : (data.ram.drop 160).take 32 = (ramSource.drop 160).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 160 16 16 ramSlice160 ramSlice176

theorem ramNode192_18 : (data.ram.drop 192).take 18 = (ramSource.drop 192).take 18 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 192 16 2 ramSlice192 ramSlice208

theorem ramNode160_50 : (data.ram.drop 160).take 50 = (ramSource.drop 160).take 50 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 160 32 18 ramNode160_32 ramNode192_18

theorem ramNode112_98 : (data.ram.drop 112).take 98 = (ramSource.drop 112).take 98 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 112 48 50 ramNode112_48 ramNode160_50

theorem ramNode0_210 : (data.ram.drop 0).take 210 = (ramSource.drop 0).take 210 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 0 112 98 ramNode0_112 ramNode112_98

theorem ramLength : Airbender.Compiler.MemoryFrameNative.KeccakCached.native.ramFields.length = 210 := by decide +kernel

theorem ram_binding : data.ram = ramSource :=
  NumericQueryFrameChecks.complete_binding data.ram ramSource 210
    (by decide +kernel) (by rw [ramSource, List.length_map, ramLength]) ramNode0_210

numeric_data_binding initialization_binding : data.initialization = Airbender.Compiler.MemoryFrameNative.KeccakCached.native.initializationFields.map encodeField

numeric_data_binding execution_binding : data.execution = Airbender.Compiler.MemoryFrameNative.KeccakCached.native.executeFields.map encodeField

end Airbender.Compiler.MemoryFrameChecks.KeccakCached
