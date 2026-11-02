import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.BlakeRoundUncached.ProjectionData
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.MemoryPayloadChecks.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

attribute [local irreducible] projectionData Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs

numeric_data_binding projection0_view : (projectionData.ports.drop 0).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection0_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 0).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection0_binding : (projectionData.ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 0).take 2 :=
  projection0_view.trans (projection0_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 0 2))

numeric_data_binding projection2_view : (projectionData.ports.drop 2).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection2_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 2).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection2_binding : (projectionData.ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 2).take 2 :=
  projection2_view.trans (projection2_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 2 2))

numeric_data_binding projection4_view : (projectionData.ports.drop 4).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection4_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 4).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection4_binding : (projectionData.ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 4).take 2 :=
  projection4_view.trans (projection4_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 4 2))

numeric_data_binding projection6_view : (projectionData.ports.drop 6).take 2 = ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection6_source : ((projectionChunk0.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 6).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection6_binding : (projectionData.ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 6).take 2 :=
  projection6_view.trans (projection6_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 6 2))

numeric_data_binding projection8_view : (projectionData.ports.drop 8).take 2 = ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection8_source : ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 8).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection8_binding : (projectionData.ports.drop 8).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 8).take 2 :=
  projection8_view.trans (projection8_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 8 2))

numeric_data_binding projection10_view : (projectionData.ports.drop 10).take 2 = ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection10_source : ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 10).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection10_binding : (projectionData.ports.drop 10).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 10).take 2 :=
  projection10_view.trans (projection10_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 10 2))

numeric_data_binding projection12_view : (projectionData.ports.drop 12).take 2 = ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection12_source : ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 12).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection12_binding : (projectionData.ports.drop 12).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 12).take 2 :=
  projection12_view.trans (projection12_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 12 2))

numeric_data_binding projection14_view : (projectionData.ports.drop 14).take 2 = ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection14_source : ((projectionChunk8.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 14).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection14_binding : (projectionData.ports.drop 14).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 14).take 2 :=
  projection14_view.trans (projection14_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 14 2))

numeric_data_binding projection16_view : (projectionData.ports.drop 16).take 2 = ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection16_source : ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 16).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection16_binding : (projectionData.ports.drop 16).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 16).take 2 :=
  projection16_view.trans (projection16_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 16 2))

numeric_data_binding projection18_view : (projectionData.ports.drop 18).take 2 = ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection18_source : ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 18).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection18_binding : (projectionData.ports.drop 18).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 18).take 2 :=
  projection18_view.trans (projection18_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 18 2))

numeric_data_binding projection20_view : (projectionData.ports.drop 20).take 2 = ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection20_source : ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 20).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection20_binding : (projectionData.ports.drop 20).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 20).take 2 :=
  projection20_view.trans (projection20_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 20 2))

numeric_data_binding projection22_view : (projectionData.ports.drop 22).take 2 = ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection22_source : ((projectionChunk16.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 22).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection22_binding : (projectionData.ports.drop 22).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 22).take 2 :=
  projection22_view.trans (projection22_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 22 2))

numeric_data_binding projection24_view : (projectionData.ports.drop 24).take 2 = ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection24_source : ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 24).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection24_binding : (projectionData.ports.drop 24).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 24).take 2 :=
  projection24_view.trans (projection24_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 24 2))

numeric_data_binding projection26_view : (projectionData.ports.drop 26).take 2 = ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection26_source : ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 26).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection26_binding : (projectionData.ports.drop 26).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 26).take 2 :=
  projection26_view.trans (projection26_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 26 2))

numeric_data_binding projection28_view : (projectionData.ports.drop 28).take 2 = ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection28_source : ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 28).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection28_binding : (projectionData.ports.drop 28).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 28).take 2 :=
  projection28_view.trans (projection28_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 28 2))

numeric_data_binding projection30_view : (projectionData.ports.drop 30).take 2 = ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection30_source : ((projectionChunk24.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 30).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection30_binding : (projectionData.ports.drop 30).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 30).take 2 :=
  projection30_view.trans (projection30_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 30 2))

numeric_data_binding projection32_view : (projectionData.ports.drop 32).take 2 = ((projectionChunk32.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection32_source : ((projectionChunk32.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 32).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection32_binding : (projectionData.ports.drop 32).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 32).take 2 :=
  projection32_view.trans (projection32_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 32 2))

numeric_data_binding projection34_view : (projectionData.ports.drop 34).take 2 = ((projectionChunk32.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection34_source : ((projectionChunk32.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 34).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection34_binding : (projectionData.ports.drop 34).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 34).take 2 :=
  projection34_view.trans (projection34_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 34 2))

numeric_data_binding projection36_view : (projectionData.ports.drop 36).take 2 = ((projectionChunk32.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection36_source : ((projectionChunk32.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 36).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection36_binding : (projectionData.ports.drop 36).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 36).take 2 :=
  projection36_view.trans (projection36_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 36 2))

numeric_data_binding projection38_view : (projectionData.ports.drop 38).take 2 = ((projectionChunk32.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection38_source : ((projectionChunk32.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 38).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection38_binding : (projectionData.ports.drop 38).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 38).take 2 :=
  projection38_view.trans (projection38_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 38 2))

numeric_data_binding projection40_view : (projectionData.ports.drop 40).take 2 = ((projectionChunk40.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection40_source : ((projectionChunk40.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 40).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection40_binding : (projectionData.ports.drop 40).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 40).take 2 :=
  projection40_view.trans (projection40_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 40 2))

numeric_data_binding projection42_view : (projectionData.ports.drop 42).take 2 = ((projectionChunk40.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection42_source : ((projectionChunk40.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 42).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection42_binding : (projectionData.ports.drop 42).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 42).take 2 :=
  projection42_view.trans (projection42_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 42 2))

numeric_data_binding projection44_view : (projectionData.ports.drop 44).take 2 = ((projectionChunk40.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection44_source : ((projectionChunk40.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 44).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection44_binding : (projectionData.ports.drop 44).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 44).take 2 :=
  projection44_view.trans (projection44_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 44 2))

numeric_data_binding projection46_view : (projectionData.ports.drop 46).take 2 = ((projectionChunk40.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection46_source : ((projectionChunk40.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 46).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection46_binding : (projectionData.ports.drop 46).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 46).take 2 :=
  projection46_view.trans (projection46_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 46 2))

numeric_data_binding projection48_view : (projectionData.ports.drop 48).take 2 = ((projectionChunk48.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection48_source : ((projectionChunk48.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 48).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection48_binding : (projectionData.ports.drop 48).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 48).take 2 :=
  projection48_view.trans (projection48_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 48 2))

numeric_data_binding projection50_view : (projectionData.ports.drop 50).take 2 = ((projectionChunk48.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection50_source : ((projectionChunk48.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 50).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection50_binding : (projectionData.ports.drop 50).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 50).take 2 :=
  projection50_view.trans (projection50_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 50 2))

numeric_data_binding projection52_view : (projectionData.ports.drop 52).take 2 = ((projectionChunk48.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection52_source : ((projectionChunk48.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 52).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection52_binding : (projectionData.ports.drop 52).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 52).take 2 :=
  projection52_view.trans (projection52_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 52 2))

numeric_data_binding projection54_view : (projectionData.ports.drop 54).take 2 = ((projectionChunk48.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection54_source : ((projectionChunk48.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 54).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection54_binding : (projectionData.ports.drop 54).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 54).take 2 :=
  projection54_view.trans (projection54_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 54 2))

numeric_data_binding projection56_view : (projectionData.ports.drop 56).take 2 = ((projectionChunk56.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection56_source : ((projectionChunk56.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 56).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection56_binding : (projectionData.ports.drop 56).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 56).take 2 :=
  projection56_view.trans (projection56_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 56 2))

numeric_data_binding projection58_view : (projectionData.ports.drop 58).take 2 = ((projectionChunk56.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection58_source : ((projectionChunk56.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 58).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection58_binding : (projectionData.ports.drop 58).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 58).take 2 :=
  projection58_view.trans (projection58_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 58 2))

numeric_data_binding projection60_view : (projectionData.ports.drop 60).take 2 = ((projectionChunk56.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection60_source : ((projectionChunk56.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 60).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection60_binding : (projectionData.ports.drop 60).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 60).take 2 :=
  projection60_view.trans (projection60_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 60 2))

numeric_data_binding projection62_view : (projectionData.ports.drop 62).take 2 = ((projectionChunk56.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection62_source : ((projectionChunk56.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 62).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection62_binding : (projectionData.ports.drop 62).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 62).take 2 :=
  projection62_view.trans (projection62_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 62 2))

numeric_data_binding projection64_view : (projectionData.ports.drop 64).take 2 = ((projectionChunk64.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection64_source : ((projectionChunk64.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 64).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection64_binding : (projectionData.ports.drop 64).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 64).take 2 :=
  projection64_view.trans (projection64_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 64 2))

numeric_data_binding projection66_view : (projectionData.ports.drop 66).take 2 = ((projectionChunk64.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection66_source : ((projectionChunk64.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 66).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection66_binding : (projectionData.ports.drop 66).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 66).take 2 :=
  projection66_view.trans (projection66_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 66 2))

numeric_data_binding projection68_view : (projectionData.ports.drop 68).take 2 = ((projectionChunk64.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection68_source : ((projectionChunk64.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 68).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection68_binding : (projectionData.ports.drop 68).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 68).take 2 :=
  projection68_view.trans (projection68_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 68 2))

numeric_data_binding projection70_view : (projectionData.ports.drop 70).take 2 = ((projectionChunk64.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection70_source : ((projectionChunk64.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 70).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection70_binding : (projectionData.ports.drop 70).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 70).take 2 :=
  projection70_view.trans (projection70_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 70 2))

numeric_data_binding projection72_view : (projectionData.ports.drop 72).take 2 = ((projectionChunk72.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection72_source : ((projectionChunk72.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 72).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection72_binding : (projectionData.ports.drop 72).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 72).take 2 :=
  projection72_view.trans (projection72_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 72 2))

numeric_data_binding projection74_view : (projectionData.ports.drop 74).take 2 = ((projectionChunk72.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection74_source : ((projectionChunk72.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 74).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection74_binding : (projectionData.ports.drop 74).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 74).take 2 :=
  projection74_view.trans (projection74_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 74 2))

numeric_data_binding projection76_view : (projectionData.ports.drop 76).take 2 = ((projectionChunk72.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection76_source : ((projectionChunk72.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 76).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection76_binding : (projectionData.ports.drop 76).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 76).take 2 :=
  projection76_view.trans (projection76_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 76 2))

numeric_data_binding projection78_view : (projectionData.ports.drop 78).take 2 = ((projectionChunk72.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2

numeric_data_binding projection78_source : ((projectionChunk72.getD 0 ⟨[], [], []⟩).ports.drop 6).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 78).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection78_binding : (projectionData.ports.drop 78).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 78).take 2 :=
  projection78_view.trans (projection78_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 78 2))

numeric_data_binding projection80_view : (projectionData.ports.drop 80).take 2 = ((projectionChunk80.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2

numeric_data_binding projection80_source : ((projectionChunk80.getD 0 ⟨[], [], []⟩).ports.drop 0).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 80).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection80_binding : (projectionData.ports.drop 80).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 80).take 2 :=
  projection80_view.trans (projection80_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 80 2))

numeric_data_binding projection82_view : (projectionData.ports.drop 82).take 2 = ((projectionChunk80.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2

numeric_data_binding projection82_source : ((projectionChunk80.getD 0 ⟨[], [], []⟩).ports.drop 2).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 82).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection82_binding : (projectionData.ports.drop 82).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 82).take 2 :=
  projection82_view.trans (projection82_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 82 2))

numeric_data_binding projection84_view : (projectionData.ports.drop 84).take 2 = ((projectionChunk80.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2

numeric_data_binding projection84_source : ((projectionChunk80.getD 0 ⟨[], [], []⟩).ports.drop 4).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.drop 84).take 2).map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)

theorem projection84_binding : (projectionData.ports.drop 84).take 2 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 84).take 2 :=
  projection84_view.trans (projection84_source.trans (NumericQueryFrameChecks.map_window Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing) 84 2))

theorem projectionNode0_4 : (projectionData.ports.drop 0).take 4 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 0).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 0 2 2 2 4 rfl rfl projection0_binding projection2_binding

theorem projectionNode6_4 : (projectionData.ports.drop 6).take 4 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 6).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 6 2 2 8 4 rfl rfl projection6_binding projection8_binding

theorem projectionNode4_6 : (projectionData.ports.drop 4).take 6 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 4).take 6 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 4 2 4 6 6 rfl rfl projection4_binding projectionNode6_4

theorem projectionNode0_10 : (projectionData.ports.drop 0).take 10 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 0).take 10 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 0 4 6 4 10 rfl rfl projectionNode0_4 projectionNode4_6

theorem projectionNode10_4 : (projectionData.ports.drop 10).take 4 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 10).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 10 2 2 12 4 rfl rfl projection10_binding projection12_binding

theorem projectionNode16_4 : (projectionData.ports.drop 16).take 4 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 16).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 16 2 2 18 4 rfl rfl projection16_binding projection18_binding

theorem projectionNode14_6 : (projectionData.ports.drop 14).take 6 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 14).take 6 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 14 2 4 16 6 rfl rfl projection14_binding projectionNode16_4

theorem projectionNode10_10 : (projectionData.ports.drop 10).take 10 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 10).take 10 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 10 4 6 14 10 rfl rfl projectionNode10_4 projectionNode14_6

theorem projectionNode0_20 : (projectionData.ports.drop 0).take 20 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 0).take 20 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 0 10 10 10 20 rfl rfl projectionNode0_10 projectionNode10_10

theorem projectionNode20_4 : (projectionData.ports.drop 20).take 4 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 20).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 20 2 2 22 4 rfl rfl projection20_binding projection22_binding

theorem projectionNode26_4 : (projectionData.ports.drop 26).take 4 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 26).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 26 2 2 28 4 rfl rfl projection26_binding projection28_binding

theorem projectionNode24_6 : (projectionData.ports.drop 24).take 6 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 24).take 6 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 24 2 4 26 6 rfl rfl projection24_binding projectionNode26_4

theorem projectionNode20_10 : (projectionData.ports.drop 20).take 10 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 20).take 10 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 20 4 6 24 10 rfl rfl projectionNode20_4 projectionNode24_6

theorem projectionNode32_4 : (projectionData.ports.drop 32).take 4 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 32).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 32 2 2 34 4 rfl rfl projection32_binding projection34_binding

theorem projectionNode30_6 : (projectionData.ports.drop 30).take 6 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 30).take 6 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 30 2 4 32 6 rfl rfl projection30_binding projectionNode32_4

theorem projectionNode38_4 : (projectionData.ports.drop 38).take 4 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 38).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 38 2 2 40 4 rfl rfl projection38_binding projection40_binding

theorem projectionNode36_6 : (projectionData.ports.drop 36).take 6 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 36).take 6 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 36 2 4 38 6 rfl rfl projection36_binding projectionNode38_4

theorem projectionNode30_12 : (projectionData.ports.drop 30).take 12 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 30).take 12 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 30 6 6 36 12 rfl rfl projectionNode30_6 projectionNode36_6

theorem projectionNode20_22 : (projectionData.ports.drop 20).take 22 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 20).take 22 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 20 10 12 30 22 rfl rfl projectionNode20_10 projectionNode30_12

theorem projectionNode0_42 : (projectionData.ports.drop 0).take 42 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 0).take 42 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 0 20 22 20 42 rfl rfl projectionNode0_20 projectionNode20_22

theorem projectionNode42_4 : (projectionData.ports.drop 42).take 4 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 42).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 42 2 2 44 4 rfl rfl projection42_binding projection44_binding

theorem projectionNode48_4 : (projectionData.ports.drop 48).take 4 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 48).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 48 2 2 50 4 rfl rfl projection48_binding projection50_binding

theorem projectionNode46_6 : (projectionData.ports.drop 46).take 6 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 46).take 6 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 46 2 4 48 6 rfl rfl projection46_binding projectionNode48_4

theorem projectionNode42_10 : (projectionData.ports.drop 42).take 10 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 42).take 10 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 42 4 6 46 10 rfl rfl projectionNode42_4 projectionNode46_6

theorem projectionNode54_4 : (projectionData.ports.drop 54).take 4 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 54).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 54 2 2 56 4 rfl rfl projection54_binding projection56_binding

theorem projectionNode52_6 : (projectionData.ports.drop 52).take 6 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 52).take 6 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 52 2 4 54 6 rfl rfl projection52_binding projectionNode54_4

theorem projectionNode60_4 : (projectionData.ports.drop 60).take 4 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 60).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 60 2 2 62 4 rfl rfl projection60_binding projection62_binding

theorem projectionNode58_6 : (projectionData.ports.drop 58).take 6 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 58).take 6 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 58 2 4 60 6 rfl rfl projection58_binding projectionNode60_4

theorem projectionNode52_12 : (projectionData.ports.drop 52).take 12 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 52).take 12 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 52 6 6 58 12 rfl rfl projectionNode52_6 projectionNode58_6

theorem projectionNode42_22 : (projectionData.ports.drop 42).take 22 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 42).take 22 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 42 10 12 52 22 rfl rfl projectionNode42_10 projectionNode52_12

theorem projectionNode64_4 : (projectionData.ports.drop 64).take 4 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 64).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 64 2 2 66 4 rfl rfl projection64_binding projection66_binding

theorem projectionNode70_4 : (projectionData.ports.drop 70).take 4 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 70).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 70 2 2 72 4 rfl rfl projection70_binding projection72_binding

theorem projectionNode68_6 : (projectionData.ports.drop 68).take 6 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 68).take 6 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 68 2 4 70 6 rfl rfl projection68_binding projectionNode70_4

theorem projectionNode64_10 : (projectionData.ports.drop 64).take 10 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 64).take 10 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 64 4 6 68 10 rfl rfl projectionNode64_4 projectionNode68_6

theorem projectionNode76_4 : (projectionData.ports.drop 76).take 4 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 76).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 76 2 2 78 4 rfl rfl projection76_binding projection78_binding

theorem projectionNode74_6 : (projectionData.ports.drop 74).take 6 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 74).take 6 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 74 2 4 76 6 rfl rfl projection74_binding projectionNode76_4

theorem projectionNode82_4 : (projectionData.ports.drop 82).take 4 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 82).take 4 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 82 2 2 84 4 rfl rfl projection82_binding projection84_binding

theorem projectionNode80_6 : (projectionData.ports.drop 80).take 6 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 80).take 6 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 80 2 4 82 6 rfl rfl projection80_binding projectionNode82_4

theorem projectionNode74_12 : (projectionData.ports.drop 74).take 12 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 74).take 12 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 74 6 6 80 12 rfl rfl projectionNode74_6 projectionNode80_6

theorem projectionNode64_22 : (projectionData.ports.drop 64).take 22 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 64).take 22 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 64 10 12 74 22 rfl rfl projectionNode64_10 projectionNode74_12

theorem projectionNode42_44 : (projectionData.ports.drop 42).take 44 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 42).take 44 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 42 22 22 64 44 rfl rfl projectionNode42_22 projectionNode64_22

theorem projectionNode0_86 : (projectionData.ports.drop 0).take 86 = ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)).drop 0).take 86 :=
  NumericWorkerPortChecks.merge_at projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 0 42 44 42 86 rfl rfl projectionNode0_42 projectionNode42_44

theorem projection_ports_binding : projectionData.ports = (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) :=
  NumericQueryFrameChecks.complete_binding projectionData.ports (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs.map (NumericMemoryPayloadChecks.inputPortCode Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)) 86
    (by decide +kernel) (by rw [List.length_map]; decide +kernel) projectionNode0_86

theorem projection_source_binding : projectionData = NumericFunctionalBaseChecks.encode
    (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.projectionInputs) := by
  rw [NumericMemoryPayloadChecks.encode_inputs]
  simpa only [projectionData] using congrArg (fun ports => NumericFunctionalBaseChecks.Data.mk ports [] []) projection_ports_binding

end Airbender.Compiler.MemoryPayloadChecks.BlakeRoundUncached
