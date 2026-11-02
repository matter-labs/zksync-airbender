import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.UnifiedCached.Data
import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.UnifiedCached.ProjectionBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.MemoryPayloadChecks.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

attribute [local irreducible] originalEntries data

numeric_data_binding row0_view : (data.drop 0).take 1 = [projectionData]

theorem row0_source : [projectionData] = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing Airbender.Compiler.MemoryNative.UnifiedCached.native.projectionInputs)] :=
  congrArg List.singleton projection_source_binding

numeric_data_binding row0_entry : (originalEntries.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing Airbender.Compiler.MemoryNative.UnifiedCached.native.projectionInputs)]

theorem row0_binding : (data.drop 0).take 1 = (originalEntries.drop 0).take 1 :=
  row0_view.trans (row0_source.trans row0_entry.symm)

numeric_data_binding row1_view : (data.drop 1).take 1 = (data1.drop 0).take 1

numeric_data_binding row1_source : (data1.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [0] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf0).isSome))]

numeric_data_binding row1_entry : (originalEntries.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [0] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf0).isSome))]

theorem row1_binding : (data.drop 1).take 1 = (originalEntries.drop 1).take 1 :=
  row1_view.trans (row1_source.trans row1_entry.symm)

numeric_data_binding row2_view : (data.drop 2).take 1 = (data1.drop 1).take 1

numeric_data_binding row2_source : (data1.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw0).inputs)]

numeric_data_binding row2_entry : (originalEntries.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw0).inputs)]

theorem row2_binding : (data.drop 2).take 1 = (originalEntries.drop 2).take 1 :=
  row2_view.trans (row2_source.trans row2_entry.symm)

numeric_data_binding row3_view : (data.drop 3).take 1 = (data1.drop 2).take 1

numeric_data_binding row3_source : (data1.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [1] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf1).isSome))]

numeric_data_binding row3_entry : (originalEntries.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [1] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf1).isSome))]

theorem row3_binding : (data.drop 3).take 1 = (originalEntries.drop 3).take 1 :=
  row3_view.trans (row3_source.trans row3_entry.symm)

numeric_data_binding row4_view : (data.drop 4).take 1 = (data1.drop 3).take 1

numeric_data_binding row4_source : (data1.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw1).inputs)]

numeric_data_binding row4_entry : (originalEntries.drop 4).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw1).inputs)]

theorem row4_binding : (data.drop 4).take 1 = (originalEntries.drop 4).take 1 :=
  row4_view.trans (row4_source.trans row4_entry.symm)

numeric_data_binding row5_view : (data.drop 5).take 1 = (data5.drop 0).take 1

numeric_data_binding row5_source : (data5.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [2] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf2).isSome))]

numeric_data_binding row5_entry : (originalEntries.drop 5).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [2] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf2).isSome))]

theorem row5_binding : (data.drop 5).take 1 = (originalEntries.drop 5).take 1 :=
  row5_view.trans (row5_source.trans row5_entry.symm)

numeric_data_binding row6_view : (data.drop 6).take 1 = (data5.drop 1).take 1

numeric_data_binding row6_source : (data5.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw2).inputs)]

numeric_data_binding row6_entry : (originalEntries.drop 6).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw2).inputs)]

theorem row6_binding : (data.drop 6).take 1 = (originalEntries.drop 6).take 1 :=
  row6_view.trans (row6_source.trans row6_entry.symm)

numeric_data_binding row7_view : (data.drop 7).take 1 = (data5.drop 2).take 1

numeric_data_binding row7_source : (data5.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [3] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf3).isSome))]

numeric_data_binding row7_entry : (originalEntries.drop 7).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [3] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf3).isSome))]

theorem row7_binding : (data.drop 7).take 1 = (originalEntries.drop 7).take 1 :=
  row7_view.trans (row7_source.trans row7_entry.symm)

numeric_data_binding row8_view : (data.drop 8).take 1 = (data5.drop 3).take 1

numeric_data_binding row8_source : (data5.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw3).inputs)]

numeric_data_binding row8_entry : (originalEntries.drop 8).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw3).inputs)]

theorem row8_binding : (data.drop 8).take 1 = (originalEntries.drop 8).take 1 :=
  row8_view.trans (row8_source.trans row8_entry.symm)

numeric_data_binding row9_view : (data.drop 9).take 1 = (data9.drop 0).take 1

numeric_data_binding row9_source : (data9.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [4] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf4).isSome))]

numeric_data_binding row9_entry : (originalEntries.drop 9).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [4] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf4).isSome))]

theorem row9_binding : (data.drop 9).take 1 = (originalEntries.drop 9).take 1 :=
  row9_view.trans (row9_source.trans row9_entry.symm)

numeric_data_binding row10_view : (data.drop 10).take 1 = (data9.drop 1).take 1

numeric_data_binding row10_source : (data9.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw4).inputs)]

numeric_data_binding row10_entry : (originalEntries.drop 10).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw4).inputs)]

theorem row10_binding : (data.drop 10).take 1 = (originalEntries.drop 10).take 1 :=
  row10_view.trans (row10_source.trans row10_entry.symm)

numeric_data_binding row11_view : (data.drop 11).take 1 = (data9.drop 2).take 1

numeric_data_binding row11_source : (data9.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [5] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf5).isSome))]

numeric_data_binding row11_entry : (originalEntries.drop 11).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [5] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf5).isSome))]

theorem row11_binding : (data.drop 11).take 1 = (originalEntries.drop 11).take 1 :=
  row11_view.trans (row11_source.trans row11_entry.symm)

numeric_data_binding row12_view : (data.drop 12).take 1 = (data9.drop 3).take 1

numeric_data_binding row12_source : (data9.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw5).inputs)]

numeric_data_binding row12_entry : (originalEntries.drop 12).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw5).inputs)]

theorem row12_binding : (data.drop 12).take 1 = (originalEntries.drop 12).take 1 :=
  row12_view.trans (row12_source.trans row12_entry.symm)

numeric_data_binding row13_view : (data.drop 13).take 1 = (data13.drop 0).take 1

numeric_data_binding row13_source : (data13.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [6] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf6).isSome))]

numeric_data_binding row13_entry : (originalEntries.drop 13).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [6] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf6).isSome))]

theorem row13_binding : (data.drop 13).take 1 = (originalEntries.drop 13).take 1 :=
  row13_view.trans (row13_source.trans row13_entry.symm)

numeric_data_binding row14_view : (data.drop 14).take 1 = (data13.drop 1).take 1

numeric_data_binding row14_source : (data13.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw6).inputs)]

numeric_data_binding row14_entry : (originalEntries.drop 14).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw6).inputs)]

theorem row14_binding : (data.drop 14).take 1 = (originalEntries.drop 14).take 1 :=
  row14_view.trans (row14_source.trans row14_entry.symm)

numeric_data_binding row15_view : (data.drop 15).take 1 = (data13.drop 2).take 1

numeric_data_binding row15_source : (data13.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [7] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf7).isSome))]

numeric_data_binding row15_entry : (originalEntries.drop 15).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [7] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf7).isSome))]

theorem row15_binding : (data.drop 15).take 1 = (originalEntries.drop 15).take 1 :=
  row15_view.trans (row15_source.trans row15_entry.symm)

numeric_data_binding row16_view : (data.drop 16).take 1 = (data13.drop 3).take 1

numeric_data_binding row16_source : (data13.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw7).inputs)]

numeric_data_binding row16_entry : (originalEntries.drop 16).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw7).inputs)]

theorem row16_binding : (data.drop 16).take 1 = (originalEntries.drop 16).take 1 :=
  row16_view.trans (row16_source.trans row16_entry.symm)

numeric_data_binding row17_view : (data.drop 17).take 1 = (data17.drop 0).take 1

numeric_data_binding row17_source : (data17.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf8).isSome))]

numeric_data_binding row17_entry : (originalEntries.drop 17).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf8).isSome))]

theorem row17_binding : (data.drop 17).take 1 = (originalEntries.drop 17).take 1 :=
  row17_view.trans (row17_source.trans row17_entry.symm)

numeric_data_binding row18_view : (data.drop 18).take 1 = (data17.drop 1).take 1

numeric_data_binding row18_source : (data17.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw8).inputs)]

numeric_data_binding row18_entry : (originalEntries.drop 18).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw8).inputs)]

theorem row18_binding : (data.drop 18).take 1 = (originalEntries.drop 18).take 1 :=
  row18_view.trans (row18_source.trans row18_entry.symm)

numeric_data_binding row19_view : (data.drop 19).take 1 = (data17.drop 2).take 1

numeric_data_binding row19_source : (data17.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf9).isSome))]

numeric_data_binding row19_entry : (originalEntries.drop 19).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf9).isSome))]

theorem row19_binding : (data.drop 19).take 1 = (originalEntries.drop 19).take 1 :=
  row19_view.trans (row19_source.trans row19_entry.symm)

numeric_data_binding row20_view : (data.drop 20).take 1 = (data17.drop 3).take 1

numeric_data_binding row20_source : (data17.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw9).inputs)]

numeric_data_binding row20_entry : (originalEntries.drop 20).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw9).inputs)]

theorem row20_binding : (data.drop 20).take 1 = (originalEntries.drop 20).take 1 :=
  row20_view.trans (row20_source.trans row20_entry.symm)

numeric_data_binding row21_view : (data.drop 21).take 1 = (data21.drop 0).take 1

numeric_data_binding row21_source : (data21.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf10).isSome))]

numeric_data_binding row21_entry : (originalEntries.drop 21).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf10).isSome))]

theorem row21_binding : (data.drop 21).take 1 = (originalEntries.drop 21).take 1 :=
  row21_view.trans (row21_source.trans row21_entry.symm)

numeric_data_binding row22_view : (data.drop 22).take 1 = (data21.drop 1).take 1

numeric_data_binding row22_source : (data21.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw10).inputs)]

numeric_data_binding row22_entry : (originalEntries.drop 22).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw10).inputs)]

theorem row22_binding : (data.drop 22).take 1 = (originalEntries.drop 22).take 1 :=
  row22_view.trans (row22_source.trans row22_entry.symm)

numeric_data_binding row23_view : (data.drop 23).take 1 = (data21.drop 2).take 1

numeric_data_binding row23_source : (data21.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf11).isSome))]

numeric_data_binding row23_entry : (originalEntries.drop 23).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf11).isSome))]

theorem row23_binding : (data.drop 23).take 1 = (originalEntries.drop 23).take 1 :=
  row23_view.trans (row23_source.trans row23_entry.symm)

numeric_data_binding row24_view : (data.drop 24).take 1 = (data21.drop 3).take 1

numeric_data_binding row24_source : (data21.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw11).inputs)]

numeric_data_binding row24_entry : (originalEntries.drop 24).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw11).inputs)]

theorem row24_binding : (data.drop 24).take 1 = (originalEntries.drop 24).take 1 :=
  row24_view.trans (row24_source.trans row24_entry.symm)

numeric_data_binding row25_view : (data.drop 25).take 1 = (data25.drop 0).take 1

numeric_data_binding row25_source : (data25.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw10 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

numeric_data_binding row25_entry : (originalEntries.drop 25).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw10 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

theorem row25_binding : (data.drop 25).take 1 = (originalEntries.drop 25).take 1 :=
  row25_view.trans (row25_source.trans row25_entry.symm)

numeric_data_binding row26_view : (data.drop 26).take 1 = (data25.drop 1).take 1

numeric_data_binding row26_source : (data25.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw11 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

numeric_data_binding row26_entry : (originalEntries.drop 26).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw11 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

theorem row26_binding : (data.drop 26).take 1 = (originalEntries.drop 26).take 1 :=
  row26_view.trans (row26_source.trans row26_entry.symm)

numeric_data_binding row27_view : (data.drop 27).take 1 = (data25.drop 2).take 1

numeric_data_binding row27_source : (data25.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw8 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

numeric_data_binding row27_entry : (originalEntries.drop 27).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw8 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

theorem row27_binding : (data.drop 27).take 1 = (originalEntries.drop 27).take 1 :=
  row27_view.trans (row27_source.trans row27_entry.symm)

numeric_data_binding row28_view : (data.drop 28).take 1 = (data25.drop 3).take 1

numeric_data_binding row28_source : (data25.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw9 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

numeric_data_binding row28_entry : (originalEntries.drop 28).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw9 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

theorem row28_binding : (data.drop 28).take 1 = (originalEntries.drop 28).take 1 :=
  row28_view.trans (row28_source.trans row28_entry.symm)

numeric_data_binding row29_view : (data.drop 29).take 1 = (data29.drop 0).take 1

numeric_data_binding row29_source : (data29.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw0 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

numeric_data_binding row29_entry : (originalEntries.drop 29).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw0 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

theorem row29_binding : (data.drop 29).take 1 = (originalEntries.drop 29).take 1 :=
  row29_view.trans (row29_source.trans row29_entry.symm)

numeric_data_binding row30_view : (data.drop 30).take 1 = (data29.drop 1).take 1

numeric_data_binding row30_source : (data29.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw1 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

numeric_data_binding row30_entry : (originalEntries.drop 30).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw1 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

theorem row30_binding : (data.drop 30).take 1 = (originalEntries.drop 30).take 1 :=
  row30_view.trans (row30_source.trans row30_entry.symm)

numeric_data_binding row31_view : (data.drop 31).take 1 = (data29.drop 2).take 1

numeric_data_binding row31_source : (data29.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw4 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

numeric_data_binding row31_entry : (originalEntries.drop 31).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw4 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

theorem row31_binding : (data.drop 31).take 1 = (originalEntries.drop 31).take 1 :=
  row31_view.trans (row31_source.trans row31_entry.symm)

numeric_data_binding row32_view : (data.drop 32).take 1 = (data29.drop 3).take 1

numeric_data_binding row32_source : (data29.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw5 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

numeric_data_binding row32_entry : (originalEntries.drop 32).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw5 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

theorem row32_binding : (data.drop 32).take 1 = (originalEntries.drop 32).take 1 :=
  row32_view.trans (row32_source.trans row32_entry.symm)

numeric_data_binding row33_view : (data.drop 33).take 1 = (data33.drop 0).take 1

numeric_data_binding row33_source : (data33.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing [(GKRAddress.InnerLayer 2 0)])]

numeric_data_binding row33_entry : (originalEntries.drop 33).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing [(GKRAddress.InnerLayer 2 0)])]

theorem row33_binding : (data.drop 33).take 1 = (originalEntries.drop 33).take 1 :=
  row33_view.trans (row33_source.trans row33_entry.symm)

numeric_data_binding row34_view : (data.drop 34).take 1 = (data33.drop 1).take 1

numeric_data_binding row34_source : (data33.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw2 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

numeric_data_binding row34_entry : (originalEntries.drop 34).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw2 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

theorem row34_binding : (data.drop 34).take 1 = (originalEntries.drop 34).take 1 :=
  row34_view.trans (row34_source.trans row34_entry.symm)

numeric_data_binding row35_view : (data.drop 35).take 1 = (data33.drop 2).take 1

numeric_data_binding row35_source : (data33.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw3 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

numeric_data_binding row35_entry : (originalEntries.drop 35).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw3 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

theorem row35_binding : (data.drop 35).take 1 = (originalEntries.drop 35).take 1 :=
  row35_view.trans (row35_source.trans row35_entry.symm)

numeric_data_binding row36_view : (data.drop 36).take 1 = (data33.drop 3).take 1

numeric_data_binding row36_source : (data33.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw6 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

numeric_data_binding row36_entry : (originalEntries.drop 36).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw6 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

theorem row36_binding : (data.drop 36).take 1 = (originalEntries.drop 36).take 1 :=
  row36_view.trans (row36_source.trans row36_entry.symm)

numeric_data_binding row37_view : (data.drop 37).take 1 = (data37.drop 0).take 1

numeric_data_binding row37_source : (data37.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw7 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

numeric_data_binding row37_entry : (originalEntries.drop 37).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw7 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

theorem row37_binding : (data.drop 37).take 1 = (originalEntries.drop 37).take 1 :=
  row37_view.trans (row37_source.trans row37_entry.symm)

numeric_data_binding row38_view : (data.drop 38).take 1 = (data37.drop 1).take 1

numeric_data_binding row38_source : (data37.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing [(GKRAddress.InnerLayer 2 0)])]

numeric_data_binding row38_entry : (originalEntries.drop 38).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing [(GKRAddress.InnerLayer 2 0)])]

theorem row38_binding : (data.drop 38).take 1 = (originalEntries.drop 38).take 1 :=
  row38_view.trans (row38_source.trans row38_entry.symm)

theorem entriesNode0_2 : (data.drop 0).take 2 = (originalEntries.drop 0).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 1 1 1 2 rfl rfl row0_binding row1_binding

theorem entriesNode2_2 : (data.drop 2).take 2 = (originalEntries.drop 2).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 2 1 1 3 2 rfl rfl row2_binding row3_binding

theorem entriesNode0_4 : (data.drop 0).take 4 = (originalEntries.drop 0).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 2 2 2 4 rfl rfl entriesNode0_2 entriesNode2_2

theorem entriesNode4_2 : (data.drop 4).take 2 = (originalEntries.drop 4).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 4 1 1 5 2 rfl rfl row4_binding row5_binding

theorem entriesNode7_2 : (data.drop 7).take 2 = (originalEntries.drop 7).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 7 1 1 8 2 rfl rfl row7_binding row8_binding

theorem entriesNode6_3 : (data.drop 6).take 3 = (originalEntries.drop 6).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 6 1 2 7 3 rfl rfl row6_binding entriesNode7_2

theorem entriesNode4_5 : (data.drop 4).take 5 = (originalEntries.drop 4).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 4 2 3 6 5 rfl rfl entriesNode4_2 entriesNode6_3

theorem entriesNode0_9 : (data.drop 0).take 9 = (originalEntries.drop 0).take 9 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 4 5 4 9 rfl rfl entriesNode0_4 entriesNode4_5

theorem entriesNode9_2 : (data.drop 9).take 2 = (originalEntries.drop 9).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 9 1 1 10 2 rfl rfl row9_binding row10_binding

theorem entriesNode12_2 : (data.drop 12).take 2 = (originalEntries.drop 12).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 12 1 1 13 2 rfl rfl row12_binding row13_binding

theorem entriesNode11_3 : (data.drop 11).take 3 = (originalEntries.drop 11).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 11 1 2 12 3 rfl rfl row11_binding entriesNode12_2

theorem entriesNode9_5 : (data.drop 9).take 5 = (originalEntries.drop 9).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 9 2 3 11 5 rfl rfl entriesNode9_2 entriesNode11_3

theorem entriesNode14_2 : (data.drop 14).take 2 = (originalEntries.drop 14).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 14 1 1 15 2 rfl rfl row14_binding row15_binding

theorem entriesNode17_2 : (data.drop 17).take 2 = (originalEntries.drop 17).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 17 1 1 18 2 rfl rfl row17_binding row18_binding

theorem entriesNode16_3 : (data.drop 16).take 3 = (originalEntries.drop 16).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 16 1 2 17 3 rfl rfl row16_binding entriesNode17_2

theorem entriesNode14_5 : (data.drop 14).take 5 = (originalEntries.drop 14).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 14 2 3 16 5 rfl rfl entriesNode14_2 entriesNode16_3

theorem entriesNode9_10 : (data.drop 9).take 10 = (originalEntries.drop 9).take 10 :=
  NumericWorkerPortChecks.merge_at data originalEntries 9 5 5 14 10 rfl rfl entriesNode9_5 entriesNode14_5

theorem entriesNode0_19 : (data.drop 0).take 19 = (originalEntries.drop 0).take 19 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 9 10 9 19 rfl rfl entriesNode0_9 entriesNode9_10

theorem entriesNode19_2 : (data.drop 19).take 2 = (originalEntries.drop 19).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 19 1 1 20 2 rfl rfl row19_binding row20_binding

theorem entriesNode22_2 : (data.drop 22).take 2 = (originalEntries.drop 22).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 22 1 1 23 2 rfl rfl row22_binding row23_binding

theorem entriesNode21_3 : (data.drop 21).take 3 = (originalEntries.drop 21).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 21 1 2 22 3 rfl rfl row21_binding entriesNode22_2

theorem entriesNode19_5 : (data.drop 19).take 5 = (originalEntries.drop 19).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 19 2 3 21 5 rfl rfl entriesNode19_2 entriesNode21_3

theorem entriesNode24_2 : (data.drop 24).take 2 = (originalEntries.drop 24).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 24 1 1 25 2 rfl rfl row24_binding row25_binding

theorem entriesNode27_2 : (data.drop 27).take 2 = (originalEntries.drop 27).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 27 1 1 28 2 rfl rfl row27_binding row28_binding

theorem entriesNode26_3 : (data.drop 26).take 3 = (originalEntries.drop 26).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 26 1 2 27 3 rfl rfl row26_binding entriesNode27_2

theorem entriesNode24_5 : (data.drop 24).take 5 = (originalEntries.drop 24).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 24 2 3 26 5 rfl rfl entriesNode24_2 entriesNode26_3

theorem entriesNode19_10 : (data.drop 19).take 10 = (originalEntries.drop 19).take 10 :=
  NumericWorkerPortChecks.merge_at data originalEntries 19 5 5 24 10 rfl rfl entriesNode19_5 entriesNode24_5

theorem entriesNode29_2 : (data.drop 29).take 2 = (originalEntries.drop 29).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 29 1 1 30 2 rfl rfl row29_binding row30_binding

theorem entriesNode32_2 : (data.drop 32).take 2 = (originalEntries.drop 32).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 32 1 1 33 2 rfl rfl row32_binding row33_binding

theorem entriesNode31_3 : (data.drop 31).take 3 = (originalEntries.drop 31).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 31 1 2 32 3 rfl rfl row31_binding entriesNode32_2

theorem entriesNode29_5 : (data.drop 29).take 5 = (originalEntries.drop 29).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 29 2 3 31 5 rfl rfl entriesNode29_2 entriesNode31_3

theorem entriesNode34_2 : (data.drop 34).take 2 = (originalEntries.drop 34).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 34 1 1 35 2 rfl rfl row34_binding row35_binding

theorem entriesNode37_2 : (data.drop 37).take 2 = (originalEntries.drop 37).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 37 1 1 38 2 rfl rfl row37_binding row38_binding

theorem entriesNode36_3 : (data.drop 36).take 3 = (originalEntries.drop 36).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 36 1 2 37 3 rfl rfl row36_binding entriesNode37_2

theorem entriesNode34_5 : (data.drop 34).take 5 = (originalEntries.drop 34).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 34 2 3 36 5 rfl rfl entriesNode34_2 entriesNode36_3

theorem entriesNode29_10 : (data.drop 29).take 10 = (originalEntries.drop 29).take 10 :=
  NumericWorkerPortChecks.merge_at data originalEntries 29 5 5 34 10 rfl rfl entriesNode29_5 entriesNode34_5

theorem entriesNode19_20 : (data.drop 19).take 20 = (originalEntries.drop 19).take 20 :=
  NumericWorkerPortChecks.merge_at data originalEntries 19 10 10 29 20 rfl rfl entriesNode19_10 entriesNode29_10

theorem entriesNode0_39 : (data.drop 0).take 39 = (originalEntries.drop 0).take 39 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 19 20 19 39 rfl rfl entriesNode0_19 entriesNode19_20

theorem source_binding : data = originalEntries :=
  NumericQueryFrameChecks.complete_binding data originalEntries 39
    (by decide +kernel) (by decide +kernel) entriesNode0_39

end Airbender.Compiler.MemoryPayloadChecks.UnifiedCached
