import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.JumpBranchUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.MemoryFrameChecks.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def encodeField : Source.MemoryField → NumericPolynomialChecks.Data := (fun field : Source.MemoryField => NumericPolynomialChecks.encode (field.polynomial Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement))

noncomputable def ramSource := Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.ramFields.map encodeField

numeric_data_binding ramLeaf0 : (data.ram.drop 0).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.ramFields.drop 0).take 16).map encodeField

theorem ramSlice0 : (data.ram.drop 0).take 16 = (ramSource.drop 0).take 16 :=
  ramLeaf0.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.ramFields encodeField 0 16)

numeric_data_binding ramLeaf16 : (data.ram.drop 16).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.ramFields.drop 16).take 16).map encodeField

theorem ramSlice16 : (data.ram.drop 16).take 16 = (ramSource.drop 16).take 16 :=
  ramLeaf16.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.ramFields encodeField 16 16)

numeric_data_binding ramLeaf32 : (data.ram.drop 32).take 16 =
  ((Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.ramFields.drop 32).take 16).map encodeField

theorem ramSlice32 : (data.ram.drop 32).take 16 = (ramSource.drop 32).take 16 :=
  ramLeaf32.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.ramFields encodeField 32 16)

numeric_data_binding ramLeaf48 : (data.ram.drop 48).take 8 =
  ((Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.ramFields.drop 48).take 8).map encodeField

theorem ramSlice48 : (data.ram.drop 48).take 8 = (ramSource.drop 48).take 8 :=
  ramLeaf48.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.ramFields encodeField 48 8)

theorem ramNode0_32 : (data.ram.drop 0).take 32 = (ramSource.drop 0).take 32 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 0 16 16 ramSlice0 ramSlice16

theorem ramNode32_24 : (data.ram.drop 32).take 24 = (ramSource.drop 32).take 24 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 32 16 8 ramSlice32 ramSlice48

theorem ramNode0_56 : (data.ram.drop 0).take 56 = (ramSource.drop 0).take 56 :=
  NumericQueryFrameChecks.merge_bindings data.ram ramSource 0 32 24 ramNode0_32 ramNode32_24

theorem ramLength : Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.ramFields.length = 56 := by decide +kernel

theorem ram_binding : data.ram = ramSource :=
  NumericQueryFrameChecks.complete_binding data.ram ramSource 56
    (by decide +kernel) (by rw [ramSource, List.length_map, ramLength]) ramNode0_56

numeric_data_binding initialization_binding : data.initialization = Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.initializationFields.map encodeField

numeric_data_binding execution_binding : data.execution = Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.executeFields.map encodeField

end Airbender.Compiler.MemoryFrameChecks.JumpBranchUncached
