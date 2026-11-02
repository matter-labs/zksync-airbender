import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.KeccakUncached.ProjectionData
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.MemoryPayloadChecks.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

attribute [local irreducible] projectionData Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs

numeric_data_binding projection0_view : (projectionData.ports.drop 0).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection0_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.drop 0).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)

theorem projection0_binding : (projectionData.ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 0).take 2 :=
  projection0_view.trans (projection0_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing) 0 2))

numeric_data_binding projection2_view : (projectionData.ports.drop 2).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection2_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.drop 2).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)

theorem projection2_binding : (projectionData.ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 2).take 2 :=
  projection2_view.trans (projection2_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing) 2 2))

numeric_data_binding projection4_view : (projectionData.ports.drop 4).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection4_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.drop 4).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)

theorem projection4_binding : (projectionData.ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 4).take 2 :=
  projection4_view.trans (projection4_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing) 4 2))

numeric_data_binding projection6_view : (projectionData.ports.drop 6).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection6_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.drop 6).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)

theorem projection6_binding : (projectionData.ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 6).take 2 :=
  projection6_view.trans (projection6_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing) 6 2))

numeric_data_binding projection8_view : (projectionData.ports.drop 8).take 2 = ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection8_source : ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.drop 8).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)

theorem projection8_binding : (projectionData.ports.drop 8).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 8).take 2 :=
  projection8_view.trans (projection8_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing) 8 2))

numeric_data_binding projection10_view : (projectionData.ports.drop 10).take 2 = ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection10_source : ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.drop 10).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)

theorem projection10_binding : (projectionData.ports.drop 10).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 10).take 2 :=
  projection10_view.trans (projection10_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing) 10 2))

numeric_data_binding projection12_view : (projectionData.ports.drop 12).take 2 = ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection12_source : ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.drop 12).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)

theorem projection12_binding : (projectionData.ports.drop 12).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 12).take 2 :=
  projection12_view.trans (projection12_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing) 12 2))

numeric_data_binding projection14_view : (projectionData.ports.drop 14).take 2 = ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection14_source : ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.drop 14).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)

theorem projection14_binding : (projectionData.ports.drop 14).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 14).take 2 :=
  projection14_view.trans (projection14_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing) 14 2))

numeric_data_binding projection16_view : (projectionData.ports.drop 16).take 2 = ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection16_source : ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.drop 16).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)

theorem projection16_binding : (projectionData.ports.drop 16).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 16).take 2 :=
  projection16_view.trans (projection16_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing) 16 2))

numeric_data_binding projection18_view : (projectionData.ports.drop 18).take 2 = ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection18_source : ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.drop 18).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)

theorem projection18_binding : (projectionData.ports.drop 18).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 18).take 2 :=
  projection18_view.trans (projection18_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing) 18 2))

numeric_data_binding projection20_view : (projectionData.ports.drop 20).take 2 = ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection20_source : ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.drop 20).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)

theorem projection20_binding : (projectionData.ports.drop 20).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 20).take 2 :=
  projection20_view.trans (projection20_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing) 20 2))

numeric_data_binding projection22_view : (projectionData.ports.drop 22).take 2 = ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection22_source : ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.drop 22).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)

theorem projection22_binding : (projectionData.ports.drop 22).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 22).take 2 :=
  projection22_view.trans (projection22_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing) 22 2))

numeric_data_binding projection24_view : (projectionData.ports.drop 24).take 2 = ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection24_source : ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.drop 24).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)

theorem projection24_binding : (projectionData.ports.drop 24).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 24).take 2 :=
  projection24_view.trans (projection24_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing) 24 2))

numeric_data_binding projection26_view : (projectionData.ports.drop 26).take 2 = ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection26_source : ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.drop 26).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)

theorem projection26_binding : (projectionData.ports.drop 26).take 2 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 26).take 2 :=
  projection26_view.trans (projection26_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing) 26 2))

theorem projectionNode2_4 : (projectionData.ports.drop 2).take 4 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 2).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)) 2 2 2 4 4 rfl rfl projection2_binding projection4_binding

theorem projectionNode0_6 : (projectionData.ports.drop 0).take 6 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 0).take 6 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)) 0 2 4 2 6 rfl rfl projection0_binding projectionNode2_4

theorem projectionNode6_4 : (projectionData.ports.drop 6).take 4 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 6).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)) 6 2 2 8 4 rfl rfl projection6_binding projection8_binding

theorem projectionNode10_4 : (projectionData.ports.drop 10).take 4 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 10).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)) 10 2 2 12 4 rfl rfl projection10_binding projection12_binding

theorem projectionNode6_8 : (projectionData.ports.drop 6).take 8 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 6).take 8 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)) 6 4 4 10 8 rfl rfl projectionNode6_4 projectionNode10_4

theorem projectionNode0_14 : (projectionData.ports.drop 0).take 14 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 0).take 14 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)) 0 6 8 6 14 rfl rfl projectionNode0_6 projectionNode6_8

theorem projectionNode16_4 : (projectionData.ports.drop 16).take 4 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 16).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)) 16 2 2 18 4 rfl rfl projection16_binding projection18_binding

theorem projectionNode14_6 : (projectionData.ports.drop 14).take 6 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 14).take 6 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)) 14 2 4 16 6 rfl rfl projection14_binding projectionNode16_4

theorem projectionNode20_4 : (projectionData.ports.drop 20).take 4 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 20).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)) 20 2 2 22 4 rfl rfl projection20_binding projection22_binding

theorem projectionNode24_4 : (projectionData.ports.drop 24).take 4 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 24).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)) 24 2 2 26 4 rfl rfl projection24_binding projection26_binding

theorem projectionNode20_8 : (projectionData.ports.drop 20).take 8 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 20).take 8 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)) 20 4 4 24 8 rfl rfl projectionNode20_4 projectionNode24_4

theorem projectionNode14_14 : (projectionData.ports.drop 14).take 14 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 14).take 14 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)) 14 6 8 20 14 rfl rfl projectionNode14_6 projectionNode20_8

theorem projectionNode0_28 : (projectionData.ports.drop 0).take 28 = ((Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)).drop 0).take 28 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)) 0 14 14 14 28 rfl rfl projectionNode0_14 projectionNode14_14

theorem projection_ports_binding : projectionData.ports = (Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)) :=
  NumericQueryFrameChecks.complete_binding projectionData.ports (Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)) 28
    (by decide +kernel) (by rw [List.length_map]; decide +kernel) projectionNode0_28

theorem projection_source_binding : projectionData = NumericFunctionalBaseChecks.encode
    (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs) := by
  rw [NumericMemoryPayloadChecks.encode_inputs]
  simpa only [projectionData] using congrArg (fun ports => NumericFunctionalBaseChecks.Data.mk ports [] []) projection_ports_binding

end Airbender.Compiler.MemoryPayloadChecks.KeccakUncached
