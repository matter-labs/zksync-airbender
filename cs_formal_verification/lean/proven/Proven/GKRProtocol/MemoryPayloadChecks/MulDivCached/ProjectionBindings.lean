module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.MemoryPayloadChecks.MulDivCached.ProjectionData
public import Proven.Import.GKRProtocol.NumericArithmeticDataImport
public import Proven.GKRProtocol.NumericWorkerPortChecks

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.MemoryPayloadChecks.MulDivCached
open Airbender Airbender.Compiler
set_option maxRecDepth 8192

attribute [local irreducible] projectionData Airbender.Compiler.MemoryNative.MulDivCached.native.projectionInputs

numeric_data_binding projection0_view : (projectionData.ports.drop 0).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection0_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.MulDivCached.native.projectionInputs.drop 0).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)

theorem projection0_binding : (projectionData.ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.MulDivCached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).drop 0).take 2 :=
  projection0_view.trans (projection0_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.MulDivCached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.ConsumerNative.MulDivCached.native.typing) 0 2))

numeric_data_binding projection2_view : (projectionData.ports.drop 2).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection2_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.MulDivCached.native.projectionInputs.drop 2).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)

theorem projection2_binding : (projectionData.ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.MulDivCached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).drop 2).take 2 :=
  projection2_view.trans (projection2_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.MulDivCached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.ConsumerNative.MulDivCached.native.typing) 2 2))

numeric_data_binding projection4_view : (projectionData.ports.drop 4).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection4_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.MulDivCached.native.projectionInputs.drop 4).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)

theorem projection4_binding : (projectionData.ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.MulDivCached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).drop 4).take 2 :=
  projection4_view.trans (projection4_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.MulDivCached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.ConsumerNative.MulDivCached.native.typing) 4 2))

theorem projectionNode2_4 : (projectionData.ports.drop 2).take 4 = ((Airbender.Compiler.MemoryNative.MulDivCached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).drop 2).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.MulDivCached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)) 2 2 2 4 4 rfl rfl projection2_binding projection4_binding

theorem projectionNode0_6 : (projectionData.ports.drop 0).take 6 = ((Airbender.Compiler.MemoryNative.MulDivCached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).drop 0).take 6 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.MulDivCached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)) 0 2 4 2 6 rfl rfl projection0_binding projectionNode2_4

theorem projection_ports_binding : projectionData.ports = (Airbender.Compiler.MemoryNative.MulDivCached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)) :=
  NumericQueryFrameChecks.complete_binding projectionData.ports (Airbender.Compiler.MemoryNative.MulDivCached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)) 6
    (by decide +kernel) (by rw [List.length_map]; decide +kernel) projectionNode0_6

theorem projection_source_binding : projectionData = NumericFunctionalBaseChecks.encode
    (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.MulDivCached.native.bank Airbender.Compiler.ConsumerNative.MulDivCached.native.typing Airbender.Compiler.MemoryNative.MulDivCached.native.projectionInputs) := by
  rw [NumericMemoryPayloadChecks.encode_inputs]
  simpa only [projectionData] using congrArg (fun ports => NumericFunctionalBaseChecks.Data.mk ports [] []) projection_ports_binding

end Airbender.Compiler.MemoryPayloadChecks.MulDivCached
