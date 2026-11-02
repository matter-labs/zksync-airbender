import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.UnifiedUncached.ProjectionData
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.MemoryPayloadChecks.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

attribute [local irreducible] projectionData Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs

numeric_data_binding projection0_view : (projectionData.ports.drop 0).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection0_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.drop 0).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)

theorem projection0_binding : (projectionData.ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)).drop 0).take 2 :=
  projection0_view.trans (projection0_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing) 0 2))

numeric_data_binding projection2_view : (projectionData.ports.drop 2).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection2_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.drop 2).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)

theorem projection2_binding : (projectionData.ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)).drop 2).take 2 :=
  projection2_view.trans (projection2_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing) 2 2))

numeric_data_binding projection4_view : (projectionData.ports.drop 4).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection4_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.drop 4).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)

theorem projection4_binding : (projectionData.ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)).drop 4).take 2 :=
  projection4_view.trans (projection4_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing) 4 2))

numeric_data_binding projection6_view : (projectionData.ports.drop 6).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection6_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.drop 6).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)

theorem projection6_binding : (projectionData.ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)).drop 6).take 2 :=
  projection6_view.trans (projection6_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing) 6 2))

numeric_data_binding projection8_view : (projectionData.ports.drop 8).take 2 = ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection8_source : ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.drop 8).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)

theorem projection8_binding : (projectionData.ports.drop 8).take 2 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)).drop 8).take 2 :=
  projection8_view.trans (projection8_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing) 8 2))

numeric_data_binding projection10_view : (projectionData.ports.drop 10).take 2 = ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection10_source : ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.drop 10).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)

theorem projection10_binding : (projectionData.ports.drop 10).take 2 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)).drop 10).take 2 :=
  projection10_view.trans (projection10_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing) 10 2))

numeric_data_binding projection12_view : (projectionData.ports.drop 12).take 2 = ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection12_source : ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.drop 12).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)

theorem projection12_binding : (projectionData.ports.drop 12).take 2 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)).drop 12).take 2 :=
  projection12_view.trans (projection12_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing) 12 2))

numeric_data_binding projection14_view : (projectionData.ports.drop 14).take 2 = ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection14_source : ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.drop 14).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)

theorem projection14_binding : (projectionData.ports.drop 14).take 2 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)).drop 14).take 2 :=
  projection14_view.trans (projection14_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing) 14 2))

theorem projectionNode0_4 : (projectionData.ports.drop 0).take 4 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)).drop 0).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)) 0 2 2 2 4 rfl rfl projection0_binding projection2_binding

theorem projectionNode4_4 : (projectionData.ports.drop 4).take 4 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)).drop 4).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)) 4 2 2 6 4 rfl rfl projection4_binding projection6_binding

theorem projectionNode0_8 : (projectionData.ports.drop 0).take 8 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)).drop 0).take 8 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)) 0 4 4 4 8 rfl rfl projectionNode0_4 projectionNode4_4

theorem projectionNode8_4 : (projectionData.ports.drop 8).take 4 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)).drop 8).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)) 8 2 2 10 4 rfl rfl projection8_binding projection10_binding

theorem projectionNode12_4 : (projectionData.ports.drop 12).take 4 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)).drop 12).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)) 12 2 2 14 4 rfl rfl projection12_binding projection14_binding

theorem projectionNode8_8 : (projectionData.ports.drop 8).take 8 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)).drop 8).take 8 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)) 8 4 4 12 8 rfl rfl projectionNode8_4 projectionNode12_4

theorem projectionNode0_16 : (projectionData.ports.drop 0).take 16 = ((Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)).drop 0).take 16 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)) 0 8 8 8 16 rfl rfl projectionNode0_8 projectionNode8_8

theorem projection_ports_binding : projectionData.ports = (Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)) :=
  NumericQueryFrameChecks.complete_binding projectionData.ports (Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing)) 16
    (by decide +kernel) (by rw [List.length_map]; decide +kernel) projectionNode0_16

theorem projection_source_binding : projectionData = NumericFunctionalBaseChecks.encode
    (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing Airbender.Compiler.MemoryNative.UnifiedUncached.native.projectionInputs) := by
  rw [NumericMemoryPayloadChecks.encode_inputs]
  simpa only [projectionData] using congrArg (fun ports => NumericFunctionalBaseChecks.Data.mk ports [] []) projection_ports_binding

end Airbender.Compiler.MemoryPayloadChecks.UnifiedUncached
