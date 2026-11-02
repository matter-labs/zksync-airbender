import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.BigintUncached.ProjectionData
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.MemoryPayloadChecks.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

attribute [local irreducible] projectionData Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs

numeric_data_binding projection0_view : (projectionData.ports.drop 0).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection0_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 0).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection0_binding : (projectionData.ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 0).take 2 :=
  projection0_view.trans (projection0_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 0 2))

numeric_data_binding projection2_view : (projectionData.ports.drop 2).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection2_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 2).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection2_binding : (projectionData.ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 2).take 2 :=
  projection2_view.trans (projection2_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 2 2))

numeric_data_binding projection4_view : (projectionData.ports.drop 4).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection4_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 4).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection4_binding : (projectionData.ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 4).take 2 :=
  projection4_view.trans (projection4_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 4 2))

numeric_data_binding projection6_view : (projectionData.ports.drop 6).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection6_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 6).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection6_binding : (projectionData.ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 6).take 2 :=
  projection6_view.trans (projection6_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 6 2))

numeric_data_binding projection8_view : (projectionData.ports.drop 8).take 2 = ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection8_source : ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 8).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection8_binding : (projectionData.ports.drop 8).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 8).take 2 :=
  projection8_view.trans (projection8_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 8 2))

numeric_data_binding projection10_view : (projectionData.ports.drop 10).take 2 = ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection10_source : ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 10).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection10_binding : (projectionData.ports.drop 10).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 10).take 2 :=
  projection10_view.trans (projection10_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 10 2))

numeric_data_binding projection12_view : (projectionData.ports.drop 12).take 2 = ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection12_source : ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 12).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection12_binding : (projectionData.ports.drop 12).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 12).take 2 :=
  projection12_view.trans (projection12_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 12 2))

numeric_data_binding projection14_view : (projectionData.ports.drop 14).take 2 = ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection14_source : ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 14).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection14_binding : (projectionData.ports.drop 14).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 14).take 2 :=
  projection14_view.trans (projection14_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 14 2))

numeric_data_binding projection16_view : (projectionData.ports.drop 16).take 2 = ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection16_source : ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 16).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection16_binding : (projectionData.ports.drop 16).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 16).take 2 :=
  projection16_view.trans (projection16_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 16 2))

numeric_data_binding projection18_view : (projectionData.ports.drop 18).take 2 = ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection18_source : ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 18).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection18_binding : (projectionData.ports.drop 18).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 18).take 2 :=
  projection18_view.trans (projection18_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 18 2))

numeric_data_binding projection20_view : (projectionData.ports.drop 20).take 2 = ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection20_source : ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 20).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection20_binding : (projectionData.ports.drop 20).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 20).take 2 :=
  projection20_view.trans (projection20_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 20 2))

numeric_data_binding projection22_view : (projectionData.ports.drop 22).take 2 = ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection22_source : ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 22).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection22_binding : (projectionData.ports.drop 22).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 22).take 2 :=
  projection22_view.trans (projection22_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 22 2))

numeric_data_binding projection24_view : (projectionData.ports.drop 24).take 2 = ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection24_source : ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 24).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection24_binding : (projectionData.ports.drop 24).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 24).take 2 :=
  projection24_view.trans (projection24_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 24 2))

numeric_data_binding projection26_view : (projectionData.ports.drop 26).take 2 = ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection26_source : ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 26).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection26_binding : (projectionData.ports.drop 26).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 26).take 2 :=
  projection26_view.trans (projection26_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 26 2))

numeric_data_binding projection28_view : (projectionData.ports.drop 28).take 2 = ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection28_source : ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 28).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection28_binding : (projectionData.ports.drop 28).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 28).take 2 :=
  projection28_view.trans (projection28_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 28 2))

numeric_data_binding projection30_view : (projectionData.ports.drop 30).take 2 = ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection30_source : ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 30).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection30_binding : (projectionData.ports.drop 30).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 30).take 2 :=
  projection30_view.trans (projection30_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 30 2))

numeric_data_binding projection32_view : (projectionData.ports.drop 32).take 2 = ((projectionChunk32.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection32_source : ((projectionChunk32.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 32).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection32_binding : (projectionData.ports.drop 32).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 32).take 2 :=
  projection32_view.trans (projection32_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 32 2))

numeric_data_binding projection34_view : (projectionData.ports.drop 34).take 2 = ((projectionChunk32.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection34_source : ((projectionChunk32.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 34).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection34_binding : (projectionData.ports.drop 34).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 34).take 2 :=
  projection34_view.trans (projection34_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 34 2))

numeric_data_binding projection36_view : (projectionData.ports.drop 36).take 2 = ((projectionChunk32.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection36_source : ((projectionChunk32.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.drop 36).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)

theorem projection36_binding : (projectionData.ports.drop 36).take 2 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 36).take 2 :=
  projection36_view.trans (projection36_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) 36 2))

theorem projectionNode0_4 : (projectionData.ports.drop 0).take 4 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 0).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 0 2 2 2 4 rfl rfl projection0_binding projection2_binding

theorem projectionNode4_4 : (projectionData.ports.drop 4).take 4 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 4).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 4 2 2 6 4 rfl rfl projection4_binding projection6_binding

theorem projectionNode0_8 : (projectionData.ports.drop 0).take 8 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 0).take 8 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 0 4 4 4 8 rfl rfl projectionNode0_4 projectionNode4_4

theorem projectionNode8_4 : (projectionData.ports.drop 8).take 4 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 8).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 8 2 2 10 4 rfl rfl projection8_binding projection10_binding

theorem projectionNode14_4 : (projectionData.ports.drop 14).take 4 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 14).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 14 2 2 16 4 rfl rfl projection14_binding projection16_binding

theorem projectionNode12_6 : (projectionData.ports.drop 12).take 6 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 12).take 6 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 12 2 4 14 6 rfl rfl projection12_binding projectionNode14_4

theorem projectionNode8_10 : (projectionData.ports.drop 8).take 10 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 8).take 10 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 8 4 6 12 10 rfl rfl projectionNode8_4 projectionNode12_6

theorem projectionNode0_18 : (projectionData.ports.drop 0).take 18 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 0).take 18 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 0 8 10 8 18 rfl rfl projectionNode0_8 projectionNode8_10

theorem projectionNode18_4 : (projectionData.ports.drop 18).take 4 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 18).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 18 2 2 20 4 rfl rfl projection18_binding projection20_binding

theorem projectionNode24_4 : (projectionData.ports.drop 24).take 4 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 24).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 24 2 2 26 4 rfl rfl projection24_binding projection26_binding

theorem projectionNode22_6 : (projectionData.ports.drop 22).take 6 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 22).take 6 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 22 2 4 24 6 rfl rfl projection22_binding projectionNode24_4

theorem projectionNode18_10 : (projectionData.ports.drop 18).take 10 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 18).take 10 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 18 4 6 22 10 rfl rfl projectionNode18_4 projectionNode22_6

theorem projectionNode28_4 : (projectionData.ports.drop 28).take 4 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 28).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 28 2 2 30 4 rfl rfl projection28_binding projection30_binding

theorem projectionNode34_4 : (projectionData.ports.drop 34).take 4 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 34).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 34 2 2 36 4 rfl rfl projection34_binding projection36_binding

theorem projectionNode32_6 : (projectionData.ports.drop 32).take 6 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 32).take 6 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 32 2 4 34 6 rfl rfl projection32_binding projectionNode34_4

theorem projectionNode28_10 : (projectionData.ports.drop 28).take 10 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 28).take 10 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 28 4 6 32 10 rfl rfl projectionNode28_4 projectionNode32_6

theorem projectionNode18_20 : (projectionData.ports.drop 18).take 20 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 18).take 20 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 18 10 10 28 20 rfl rfl projectionNode18_10 projectionNode28_10

theorem projectionNode0_38 : (projectionData.ports.drop 0).take 38 = ((Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)).drop 0).take 38 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 0 18 20 18 38 rfl rfl projectionNode0_18 projectionNode18_20

theorem projection_ports_binding : projectionData.ports = (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) :=
  NumericQueryFrameChecks.complete_binding projectionData.ports (Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)) 38
    (by decide +kernel) (by rw [List.length_map]; decide +kernel) projectionNode0_38

theorem projection_source_binding : projectionData = NumericFunctionalBaseChecks.encode
    (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintUncached.native.bank Airbender.Compiler.ConsumerNative.BigintUncached.native.typing Airbender.Compiler.MemoryNative.BigintUncached.native.projectionInputs) := by
  rw [NumericMemoryPayloadChecks.encode_inputs]
  simpa only [projectionData] using congrArg (fun ports => NumericFunctionalBaseChecks.Data.mk ports [] []) projection_ports_binding

end Airbender.Compiler.MemoryPayloadChecks.BigintUncached
