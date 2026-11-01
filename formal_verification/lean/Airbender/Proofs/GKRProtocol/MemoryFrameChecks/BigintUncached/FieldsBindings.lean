import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BigintUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodeField : Source.MemoryField → NumericPolynomialChecks.Data := (fun field : Source.MemoryField => NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.MemoryNative.BigintUncached.native.sourcePlacement))

noncomputable def ramSource := Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.map encodeField

numeric_data_binding ramLeaf0 : (data.ram.drop 0).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 0).take 16).map encodeField

theorem ramSlice0 : (data.ram.drop 0).take 16 = (ramSource.drop 0).take 16 :=
  ramLeaf0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 0 16)

numeric_data_binding ramLeaf16 : (data.ram.drop 16).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 16).take 16).map encodeField

theorem ramSlice16 : (data.ram.drop 16).take 16 = (ramSource.drop 16).take 16 :=
  ramLeaf16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 16 16)

numeric_data_binding ramLeaf32 : (data.ram.drop 32).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 32).take 16).map encodeField

theorem ramSlice32 : (data.ram.drop 32).take 16 = (ramSource.drop 32).take 16 :=
  ramLeaf32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 32 16)

numeric_data_binding ramLeaf48 : (data.ram.drop 48).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 48).take 16).map encodeField

theorem ramSlice48 : (data.ram.drop 48).take 16 = (ramSource.drop 48).take 16 :=
  ramLeaf48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 48 16)

numeric_data_binding ramLeaf64 : (data.ram.drop 64).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 64).take 16).map encodeField

theorem ramSlice64 : (data.ram.drop 64).take 16 = (ramSource.drop 64).take 16 :=
  ramLeaf64.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 64 16)

numeric_data_binding ramLeaf80 : (data.ram.drop 80).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 80).take 16).map encodeField

theorem ramSlice80 : (data.ram.drop 80).take 16 = (ramSource.drop 80).take 16 :=
  ramLeaf80.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 80 16)

numeric_data_binding ramLeaf96 : (data.ram.drop 96).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 96).take 16).map encodeField

theorem ramSlice96 : (data.ram.drop 96).take 16 = (ramSource.drop 96).take 16 :=
  ramLeaf96.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 96 16)

numeric_data_binding ramLeaf112 : (data.ram.drop 112).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 112).take 16).map encodeField

theorem ramSlice112 : (data.ram.drop 112).take 16 = (ramSource.drop 112).take 16 :=
  ramLeaf112.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 112 16)

numeric_data_binding ramLeaf128 : (data.ram.drop 128).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 128).take 16).map encodeField

theorem ramSlice128 : (data.ram.drop 128).take 16 = (ramSource.drop 128).take 16 :=
  ramLeaf128.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 128 16)

numeric_data_binding ramLeaf144 : (data.ram.drop 144).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 144).take 16).map encodeField

theorem ramSlice144 : (data.ram.drop 144).take 16 = (ramSource.drop 144).take 16 :=
  ramLeaf144.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 144 16)

numeric_data_binding ramLeaf160 : (data.ram.drop 160).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 160).take 16).map encodeField

theorem ramSlice160 : (data.ram.drop 160).take 16 = (ramSource.drop 160).take 16 :=
  ramLeaf160.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 160 16)

numeric_data_binding ramLeaf176 : (data.ram.drop 176).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 176).take 16).map encodeField

theorem ramSlice176 : (data.ram.drop 176).take 16 = (ramSource.drop 176).take 16 :=
  ramLeaf176.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 176 16)

numeric_data_binding ramLeaf192 : (data.ram.drop 192).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 192).take 16).map encodeField

theorem ramSlice192 : (data.ram.drop 192).take 16 = (ramSource.drop 192).take 16 :=
  ramLeaf192.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 192 16)

numeric_data_binding ramLeaf208 : (data.ram.drop 208).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 208).take 16).map encodeField

theorem ramSlice208 : (data.ram.drop 208).take 16 = (ramSource.drop 208).take 16 :=
  ramLeaf208.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 208 16)

numeric_data_binding ramLeaf224 : (data.ram.drop 224).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 224).take 16).map encodeField

theorem ramSlice224 : (data.ram.drop 224).take 16 = (ramSource.drop 224).take 16 :=
  ramLeaf224.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 224 16)

numeric_data_binding ramLeaf240 : (data.ram.drop 240).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 240).take 16).map encodeField

theorem ramSlice240 : (data.ram.drop 240).take 16 = (ramSource.drop 240).take 16 :=
  ramLeaf240.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 240 16)

numeric_data_binding ramLeaf256 : (data.ram.drop 256).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 256).take 16).map encodeField

theorem ramSlice256 : (data.ram.drop 256).take 16 = (ramSource.drop 256).take 16 :=
  ramLeaf256.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 256 16)

numeric_data_binding ramLeaf272 : (data.ram.drop 272).take 8 =
  ((Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.drop 272).take 8).map encodeField

theorem ramSlice272 : (data.ram.drop 272).take 8 = (ramSource.drop 272).take 8 :=
  ramLeaf272.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields encodeField 272 8)

theorem ramNode0_32 : (data.ram.drop 0).take 32 = (ramSource.drop 0).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 0 16 16 ramSlice0 ramSlice16

theorem ramNode32_32 : (data.ram.drop 32).take 32 = (ramSource.drop 32).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 32 16 16 ramSlice32 ramSlice48

theorem ramNode0_64 : (data.ram.drop 0).take 64 = (ramSource.drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 0 32 32 ramNode0_32 ramNode32_32

theorem ramNode64_32 : (data.ram.drop 64).take 32 = (ramSource.drop 64).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 64 16 16 ramSlice64 ramSlice80

theorem ramNode112_32 : (data.ram.drop 112).take 32 = (ramSource.drop 112).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 112 16 16 ramSlice112 ramSlice128

theorem ramNode96_48 : (data.ram.drop 96).take 48 = (ramSource.drop 96).take 48 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 96 16 32 ramSlice96 ramNode112_32

theorem ramNode64_80 : (data.ram.drop 64).take 80 = (ramSource.drop 64).take 80 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 64 32 48 ramNode64_32 ramNode96_48

theorem ramNode0_144 : (data.ram.drop 0).take 144 = (ramSource.drop 0).take 144 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 0 64 80 ramNode0_64 ramNode64_80

theorem ramNode144_32 : (data.ram.drop 144).take 32 = (ramSource.drop 144).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 144 16 16 ramSlice144 ramSlice160

theorem ramNode176_32 : (data.ram.drop 176).take 32 = (ramSource.drop 176).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 176 16 16 ramSlice176 ramSlice192

theorem ramNode144_64 : (data.ram.drop 144).take 64 = (ramSource.drop 144).take 64 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 144 32 32 ramNode144_32 ramNode176_32

theorem ramNode208_32 : (data.ram.drop 208).take 32 = (ramSource.drop 208).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 208 16 16 ramSlice208 ramSlice224

theorem ramNode256_24 : (data.ram.drop 256).take 24 = (ramSource.drop 256).take 24 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 256 16 8 ramSlice256 ramSlice272

theorem ramNode240_40 : (data.ram.drop 240).take 40 = (ramSource.drop 240).take 40 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 240 16 24 ramSlice240 ramNode256_24

theorem ramNode208_72 : (data.ram.drop 208).take 72 = (ramSource.drop 208).take 72 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 208 32 40 ramNode208_32 ramNode240_40

theorem ramNode144_136 : (data.ram.drop 144).take 136 = (ramSource.drop 144).take 136 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 144 64 72 ramNode144_64 ramNode208_72

theorem ramNode0_280 : (data.ram.drop 0).take 280 = (ramSource.drop 0).take 280 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 0 144 136 ramNode0_144 ramNode144_136

theorem ramLength : Airbender.Compiler.MemoryFrameNative.BigintUncached.native.ramFields.length = 280 := by decide +kernel

theorem ram_binding : data.ram = ramSource :=
  NumericQueryFrameChecks.complete_binding data.ram ramSource 280
    (by decide +kernel) (by rw [ramSource, List.length_map, ramLength]) ramNode0_280

numeric_data_binding initialization_binding : data.initialization = Airbender.Compiler.MemoryFrameNative.BigintUncached.native.initializationFields.map encodeField

numeric_data_binding execution_binding : data.execution = Airbender.Compiler.MemoryFrameNative.BigintUncached.native.executeFields.map encodeField

end Airbender.Compiler.MemoryFrameChecks.BigintUncached
