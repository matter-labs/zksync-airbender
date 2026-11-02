import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.BigintCached.Data
import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.BigintCached.ProjectionBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.MemoryPayloadChecks.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

attribute [local irreducible] originalEntries data

numeric_data_binding row0_view : (data.drop 0).take 1 = [projectionData]

theorem row0_source : [projectionData] = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing Airbender.Compiler.MemoryNative.BigintCached.native.projectionInputs)] :=
  congrArg List.singleton projection_source_binding

numeric_data_binding row0_entry : (originalEntries.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing Airbender.Compiler.MemoryNative.BigintCached.native.projectionInputs)]

theorem row0_binding : (data.drop 0).take 1 = (originalEntries.drop 0).take 1 :=
  row0_view.trans (row0_source.trans row0_entry.symm)

numeric_data_binding row1_view : (data.drop 1).take 1 = (data1.drop 0).take 1

numeric_data_binding row1_source : (data1.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [0] Airbender.Compiler.MemoryNative.BigintCached.native.leaf0).isSome))]

numeric_data_binding row1_entry : (originalEntries.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [0] Airbender.Compiler.MemoryNative.BigintCached.native.leaf0).isSome))]

theorem row1_binding : (data.drop 1).take 1 = (originalEntries.drop 1).take 1 :=
  row1_view.trans (row1_source.trans row1_entry.symm)

numeric_data_binding row2_view : (data.drop 2).take 1 = (data1.drop 1).take 1

numeric_data_binding row2_source : (data1.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw0).inputs)]

numeric_data_binding row2_entry : (originalEntries.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw0).inputs)]

theorem row2_binding : (data.drop 2).take 1 = (originalEntries.drop 2).take 1 :=
  row2_view.trans (row2_source.trans row2_entry.symm)

numeric_data_binding row3_view : (data.drop 3).take 1 = (data1.drop 2).take 1

numeric_data_binding row3_source : (data1.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [1] Airbender.Compiler.MemoryNative.BigintCached.native.leaf1).isSome))]

numeric_data_binding row3_entry : (originalEntries.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [1] Airbender.Compiler.MemoryNative.BigintCached.native.leaf1).isSome))]

theorem row3_binding : (data.drop 3).take 1 = (originalEntries.drop 3).take 1 :=
  row3_view.trans (row3_source.trans row3_entry.symm)

numeric_data_binding row4_view : (data.drop 4).take 1 = (data1.drop 3).take 1

numeric_data_binding row4_source : (data1.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw1).inputs)]

numeric_data_binding row4_entry : (originalEntries.drop 4).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw1).inputs)]

theorem row4_binding : (data.drop 4).take 1 = (originalEntries.drop 4).take 1 :=
  row4_view.trans (row4_source.trans row4_entry.symm)

numeric_data_binding row5_view : (data.drop 5).take 1 = (data5.drop 0).take 1

numeric_data_binding row5_source : (data5.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [2] Airbender.Compiler.MemoryNative.BigintCached.native.leaf2).isSome))]

numeric_data_binding row5_entry : (originalEntries.drop 5).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [2] Airbender.Compiler.MemoryNative.BigintCached.native.leaf2).isSome))]

theorem row5_binding : (data.drop 5).take 1 = (originalEntries.drop 5).take 1 :=
  row5_view.trans (row5_source.trans row5_entry.symm)

numeric_data_binding row6_view : (data.drop 6).take 1 = (data5.drop 1).take 1

numeric_data_binding row6_source : (data5.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw2).inputs)]

numeric_data_binding row6_entry : (originalEntries.drop 6).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw2).inputs)]

theorem row6_binding : (data.drop 6).take 1 = (originalEntries.drop 6).take 1 :=
  row6_view.trans (row6_source.trans row6_entry.symm)

numeric_data_binding row7_view : (data.drop 7).take 1 = (data5.drop 2).take 1

numeric_data_binding row7_source : (data5.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [3] Airbender.Compiler.MemoryNative.BigintCached.native.leaf3).isSome))]

numeric_data_binding row7_entry : (originalEntries.drop 7).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [3] Airbender.Compiler.MemoryNative.BigintCached.native.leaf3).isSome))]

theorem row7_binding : (data.drop 7).take 1 = (originalEntries.drop 7).take 1 :=
  row7_view.trans (row7_source.trans row7_entry.symm)

numeric_data_binding row8_view : (data.drop 8).take 1 = (data5.drop 3).take 1

numeric_data_binding row8_source : (data5.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw3).inputs)]

numeric_data_binding row8_entry : (originalEntries.drop 8).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw3).inputs)]

theorem row8_binding : (data.drop 8).take 1 = (originalEntries.drop 8).take 1 :=
  row8_view.trans (row8_source.trans row8_entry.symm)

numeric_data_binding row9_view : (data.drop 9).take 1 = (data9.drop 0).take 1

numeric_data_binding row9_source : (data9.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [4] Airbender.Compiler.MemoryNative.BigintCached.native.leaf4).isSome))]

numeric_data_binding row9_entry : (originalEntries.drop 9).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [4] Airbender.Compiler.MemoryNative.BigintCached.native.leaf4).isSome))]

theorem row9_binding : (data.drop 9).take 1 = (originalEntries.drop 9).take 1 :=
  row9_view.trans (row9_source.trans row9_entry.symm)

numeric_data_binding row10_view : (data.drop 10).take 1 = (data9.drop 1).take 1

numeric_data_binding row10_source : (data9.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw4).inputs)]

numeric_data_binding row10_entry : (originalEntries.drop 10).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw4).inputs)]

theorem row10_binding : (data.drop 10).take 1 = (originalEntries.drop 10).take 1 :=
  row10_view.trans (row10_source.trans row10_entry.symm)

numeric_data_binding row11_view : (data.drop 11).take 1 = (data9.drop 2).take 1

numeric_data_binding row11_source : (data9.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [5] Airbender.Compiler.MemoryNative.BigintCached.native.leaf5).isSome))]

numeric_data_binding row11_entry : (originalEntries.drop 11).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [5] Airbender.Compiler.MemoryNative.BigintCached.native.leaf5).isSome))]

theorem row11_binding : (data.drop 11).take 1 = (originalEntries.drop 11).take 1 :=
  row11_view.trans (row11_source.trans row11_entry.symm)

numeric_data_binding row12_view : (data.drop 12).take 1 = (data9.drop 3).take 1

numeric_data_binding row12_source : (data9.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw5).inputs)]

numeric_data_binding row12_entry : (originalEntries.drop 12).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw5).inputs)]

theorem row12_binding : (data.drop 12).take 1 = (originalEntries.drop 12).take 1 :=
  row12_view.trans (row12_source.trans row12_entry.symm)

numeric_data_binding row13_view : (data.drop 13).take 1 = (data13.drop 0).take 1

numeric_data_binding row13_source : (data13.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [6] Airbender.Compiler.MemoryNative.BigintCached.native.leaf6).isSome))]

numeric_data_binding row13_entry : (originalEntries.drop 13).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [6] Airbender.Compiler.MemoryNative.BigintCached.native.leaf6).isSome))]

theorem row13_binding : (data.drop 13).take 1 = (originalEntries.drop 13).take 1 :=
  row13_view.trans (row13_source.trans row13_entry.symm)

numeric_data_binding row14_view : (data.drop 14).take 1 = (data13.drop 1).take 1

numeric_data_binding row14_source : (data13.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw6).inputs)]

numeric_data_binding row14_entry : (originalEntries.drop 14).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw6).inputs)]

theorem row14_binding : (data.drop 14).take 1 = (originalEntries.drop 14).take 1 :=
  row14_view.trans (row14_source.trans row14_entry.symm)

numeric_data_binding row15_view : (data.drop 15).take 1 = (data13.drop 2).take 1

numeric_data_binding row15_source : (data13.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [7] Airbender.Compiler.MemoryNative.BigintCached.native.leaf7).isSome))]

numeric_data_binding row15_entry : (originalEntries.drop 15).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [7] Airbender.Compiler.MemoryNative.BigintCached.native.leaf7).isSome))]

theorem row15_binding : (data.drop 15).take 1 = (originalEntries.drop 15).take 1 :=
  row15_view.trans (row15_source.trans row15_entry.symm)

numeric_data_binding row16_view : (data.drop 16).take 1 = (data13.drop 3).take 1

numeric_data_binding row16_source : (data13.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw7).inputs)]

numeric_data_binding row16_entry : (originalEntries.drop 16).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw7).inputs)]

theorem row16_binding : (data.drop 16).take 1 = (originalEntries.drop 16).take 1 :=
  row16_view.trans (row16_source.trans row16_entry.symm)

numeric_data_binding row17_view : (data.drop 17).take 1 = (data17.drop 0).take 1

numeric_data_binding row17_source : (data17.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [8] Airbender.Compiler.MemoryNative.BigintCached.native.leaf8).isSome))]

numeric_data_binding row17_entry : (originalEntries.drop 17).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [8] Airbender.Compiler.MemoryNative.BigintCached.native.leaf8).isSome))]

theorem row17_binding : (data.drop 17).take 1 = (originalEntries.drop 17).take 1 :=
  row17_view.trans (row17_source.trans row17_entry.symm)

numeric_data_binding row18_view : (data.drop 18).take 1 = (data17.drop 1).take 1

numeric_data_binding row18_source : (data17.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw8).inputs)]

numeric_data_binding row18_entry : (originalEntries.drop 18).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw8).inputs)]

theorem row18_binding : (data.drop 18).take 1 = (originalEntries.drop 18).take 1 :=
  row18_view.trans (row18_source.trans row18_entry.symm)

numeric_data_binding row19_view : (data.drop 19).take 1 = (data17.drop 2).take 1

numeric_data_binding row19_source : (data17.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [9] Airbender.Compiler.MemoryNative.BigintCached.native.leaf9).isSome))]

numeric_data_binding row19_entry : (originalEntries.drop 19).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [9] Airbender.Compiler.MemoryNative.BigintCached.native.leaf9).isSome))]

theorem row19_binding : (data.drop 19).take 1 = (originalEntries.drop 19).take 1 :=
  row19_view.trans (row19_source.trans row19_entry.symm)

numeric_data_binding row20_view : (data.drop 20).take 1 = (data17.drop 3).take 1

numeric_data_binding row20_source : (data17.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw9).inputs)]

numeric_data_binding row20_entry : (originalEntries.drop 20).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw9).inputs)]

theorem row20_binding : (data.drop 20).take 1 = (originalEntries.drop 20).take 1 :=
  row20_view.trans (row20_source.trans row20_entry.symm)

numeric_data_binding row21_view : (data.drop 21).take 1 = (data21.drop 0).take 1

numeric_data_binding row21_source : (data21.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [10] Airbender.Compiler.MemoryNative.BigintCached.native.leaf10).isSome))]

numeric_data_binding row21_entry : (originalEntries.drop 21).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [10] Airbender.Compiler.MemoryNative.BigintCached.native.leaf10).isSome))]

theorem row21_binding : (data.drop 21).take 1 = (originalEntries.drop 21).take 1 :=
  row21_view.trans (row21_source.trans row21_entry.symm)

numeric_data_binding row22_view : (data.drop 22).take 1 = (data21.drop 1).take 1

numeric_data_binding row22_source : (data21.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw10).inputs)]

numeric_data_binding row22_entry : (originalEntries.drop 22).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw10).inputs)]

theorem row22_binding : (data.drop 22).take 1 = (originalEntries.drop 22).take 1 :=
  row22_view.trans (row22_source.trans row22_entry.symm)

numeric_data_binding row23_view : (data.drop 23).take 1 = (data21.drop 2).take 1

numeric_data_binding row23_source : (data21.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [11] Airbender.Compiler.MemoryNative.BigintCached.native.leaf11).isSome))]

numeric_data_binding row23_entry : (originalEntries.drop 23).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [11] Airbender.Compiler.MemoryNative.BigintCached.native.leaf11).isSome))]

theorem row23_binding : (data.drop 23).take 1 = (originalEntries.drop 23).take 1 :=
  row23_view.trans (row23_source.trans row23_entry.symm)

numeric_data_binding row24_view : (data.drop 24).take 1 = (data21.drop 3).take 1

numeric_data_binding row24_source : (data21.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw11).inputs)]

numeric_data_binding row24_entry : (originalEntries.drop 24).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw11).inputs)]

theorem row24_binding : (data.drop 24).take 1 = (originalEntries.drop 24).take 1 :=
  row24_view.trans (row24_source.trans row24_entry.symm)

numeric_data_binding row25_view : (data.drop 25).take 1 = (data25.drop 0).take 1

numeric_data_binding row25_source : (data25.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [12] Airbender.Compiler.MemoryNative.BigintCached.native.leaf12).isSome))]

numeric_data_binding row25_entry : (originalEntries.drop 25).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [12] Airbender.Compiler.MemoryNative.BigintCached.native.leaf12).isSome))]

theorem row25_binding : (data.drop 25).take 1 = (originalEntries.drop 25).take 1 :=
  row25_view.trans (row25_source.trans row25_entry.symm)

numeric_data_binding row26_view : (data.drop 26).take 1 = (data25.drop 1).take 1

numeric_data_binding row26_source : (data25.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw12).inputs)]

numeric_data_binding row26_entry : (originalEntries.drop 26).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw12).inputs)]

theorem row26_binding : (data.drop 26).take 1 = (originalEntries.drop 26).take 1 :=
  row26_view.trans (row26_source.trans row26_entry.symm)

numeric_data_binding row27_view : (data.drop 27).take 1 = (data25.drop 2).take 1

numeric_data_binding row27_source : (data25.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [13] Airbender.Compiler.MemoryNative.BigintCached.native.leaf13).isSome))]

numeric_data_binding row27_entry : (originalEntries.drop 27).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [13] Airbender.Compiler.MemoryNative.BigintCached.native.leaf13).isSome))]

theorem row27_binding : (data.drop 27).take 1 = (originalEntries.drop 27).take 1 :=
  row27_view.trans (row27_source.trans row27_entry.symm)

numeric_data_binding row28_view : (data.drop 28).take 1 = (data25.drop 3).take 1

numeric_data_binding row28_source : (data25.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw13).inputs)]

numeric_data_binding row28_entry : (originalEntries.drop 28).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw13).inputs)]

theorem row28_binding : (data.drop 28).take 1 = (originalEntries.drop 28).take 1 :=
  row28_view.trans (row28_source.trans row28_entry.symm)

numeric_data_binding row29_view : (data.drop 29).take 1 = (data29.drop 0).take 1

numeric_data_binding row29_source : (data29.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [14] Airbender.Compiler.MemoryNative.BigintCached.native.leaf14).isSome))]

numeric_data_binding row29_entry : (originalEntries.drop 29).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [14] Airbender.Compiler.MemoryNative.BigintCached.native.leaf14).isSome))]

theorem row29_binding : (data.drop 29).take 1 = (originalEntries.drop 29).take 1 :=
  row29_view.trans (row29_source.trans row29_entry.symm)

numeric_data_binding row30_view : (data.drop 30).take 1 = (data29.drop 1).take 1

numeric_data_binding row30_source : (data29.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw14).inputs)]

numeric_data_binding row30_entry : (originalEntries.drop 30).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw14).inputs)]

theorem row30_binding : (data.drop 30).take 1 = (originalEntries.drop 30).take 1 :=
  row30_view.trans (row30_source.trans row30_entry.symm)

numeric_data_binding row31_view : (data.drop 31).take 1 = (data29.drop 2).take 1

numeric_data_binding row31_source : (data29.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [15] Airbender.Compiler.MemoryNative.BigintCached.native.leaf15).isSome))]

numeric_data_binding row31_entry : (originalEntries.drop 31).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [15] Airbender.Compiler.MemoryNative.BigintCached.native.leaf15).isSome))]

theorem row31_binding : (data.drop 31).take 1 = (originalEntries.drop 31).take 1 :=
  row31_view.trans (row31_source.trans row31_entry.symm)

numeric_data_binding row32_view : (data.drop 32).take 1 = (data29.drop 3).take 1

numeric_data_binding row32_source : (data29.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw15).inputs)]

numeric_data_binding row32_entry : (originalEntries.drop 32).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw15).inputs)]

theorem row32_binding : (data.drop 32).take 1 = (originalEntries.drop 32).take 1 :=
  row32_view.trans (row32_source.trans row32_entry.symm)

numeric_data_binding row33_view : (data.drop 33).take 1 = (data33.drop 0).take 1

numeric_data_binding row33_source : (data33.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [16] Airbender.Compiler.MemoryNative.BigintCached.native.leaf16).isSome))]

numeric_data_binding row33_entry : (originalEntries.drop 33).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [16] Airbender.Compiler.MemoryNative.BigintCached.native.leaf16).isSome))]

theorem row33_binding : (data.drop 33).take 1 = (originalEntries.drop 33).take 1 :=
  row33_view.trans (row33_source.trans row33_entry.symm)

numeric_data_binding row34_view : (data.drop 34).take 1 = (data33.drop 1).take 1

numeric_data_binding row34_source : (data33.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw16).inputs)]

numeric_data_binding row34_entry : (originalEntries.drop 34).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw16).inputs)]

theorem row34_binding : (data.drop 34).take 1 = (originalEntries.drop 34).take 1 :=
  row34_view.trans (row34_source.trans row34_entry.symm)

numeric_data_binding row35_view : (data.drop 35).take 1 = (data33.drop 2).take 1

numeric_data_binding row35_source : (data33.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [17] Airbender.Compiler.MemoryNative.BigintCached.native.leaf17).isSome))]

numeric_data_binding row35_entry : (originalEntries.drop 35).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [17] Airbender.Compiler.MemoryNative.BigintCached.native.leaf17).isSome))]

theorem row35_binding : (data.drop 35).take 1 = (originalEntries.drop 35).take 1 :=
  row35_view.trans (row35_source.trans row35_entry.symm)

numeric_data_binding row36_view : (data.drop 36).take 1 = (data33.drop 3).take 1

numeric_data_binding row36_source : (data33.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw17).inputs)]

numeric_data_binding row36_entry : (originalEntries.drop 36).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw17).inputs)]

theorem row36_binding : (data.drop 36).take 1 = (originalEntries.drop 36).take 1 :=
  row36_view.trans (row36_source.trans row36_entry.symm)

numeric_data_binding row37_view : (data.drop 37).take 1 = (data37.drop 0).take 1

numeric_data_binding row37_source : (data37.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [18] Airbender.Compiler.MemoryNative.BigintCached.native.leaf18).isSome))]

numeric_data_binding row37_entry : (originalEntries.drop 37).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [18] Airbender.Compiler.MemoryNative.BigintCached.native.leaf18).isSome))]

theorem row37_binding : (data.drop 37).take 1 = (originalEntries.drop 37).take 1 :=
  row37_view.trans (row37_source.trans row37_entry.symm)

numeric_data_binding row38_view : (data.drop 38).take 1 = (data37.drop 1).take 1

numeric_data_binding row38_source : (data37.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw18).inputs)]

numeric_data_binding row38_entry : (originalEntries.drop 38).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw18).inputs)]

theorem row38_binding : (data.drop 38).take 1 = (originalEntries.drop 38).take 1 :=
  row38_view.trans (row38_source.trans row38_entry.symm)

numeric_data_binding row39_view : (data.drop 39).take 1 = (data37.drop 2).take 1

numeric_data_binding row39_source : (data37.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [19] Airbender.Compiler.MemoryNative.BigintCached.native.leaf19).isSome))]

numeric_data_binding row39_entry : (originalEntries.drop 39).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [19] Airbender.Compiler.MemoryNative.BigintCached.native.leaf19).isSome))]

theorem row39_binding : (data.drop 39).take 1 = (originalEntries.drop 39).take 1 :=
  row39_view.trans (row39_source.trans row39_entry.symm)

numeric_data_binding row40_view : (data.drop 40).take 1 = (data37.drop 3).take 1

numeric_data_binding row40_source : (data37.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw19).inputs)]

numeric_data_binding row40_entry : (originalEntries.drop 40).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw19).inputs)]

theorem row40_binding : (data.drop 40).take 1 = (originalEntries.drop 40).take 1 :=
  row40_view.trans (row40_source.trans row40_entry.symm)

numeric_data_binding row41_view : (data.drop 41).take 1 = (data41.drop 0).take 1

numeric_data_binding row41_source : (data41.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [20] Airbender.Compiler.MemoryNative.BigintCached.native.leaf20).isSome))]

numeric_data_binding row41_entry : (originalEntries.drop 41).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [20] Airbender.Compiler.MemoryNative.BigintCached.native.leaf20).isSome))]

theorem row41_binding : (data.drop 41).take 1 = (originalEntries.drop 41).take 1 :=
  row41_view.trans (row41_source.trans row41_entry.symm)

numeric_data_binding row42_view : (data.drop 42).take 1 = (data41.drop 1).take 1

numeric_data_binding row42_source : (data41.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw20).inputs)]

numeric_data_binding row42_entry : (originalEntries.drop 42).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw20).inputs)]

theorem row42_binding : (data.drop 42).take 1 = (originalEntries.drop 42).take 1 :=
  row42_view.trans (row42_source.trans row42_entry.symm)

numeric_data_binding row43_view : (data.drop 43).take 1 = (data41.drop 2).take 1

numeric_data_binding row43_source : (data41.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [21] Airbender.Compiler.MemoryNative.BigintCached.native.leaf21).isSome))]

numeric_data_binding row43_entry : (originalEntries.drop 43).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [21] Airbender.Compiler.MemoryNative.BigintCached.native.leaf21).isSome))]

theorem row43_binding : (data.drop 43).take 1 = (originalEntries.drop 43).take 1 :=
  row43_view.trans (row43_source.trans row43_entry.symm)

numeric_data_binding row44_view : (data.drop 44).take 1 = (data41.drop 3).take 1

numeric_data_binding row44_source : (data41.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw21).inputs)]

numeric_data_binding row44_entry : (originalEntries.drop 44).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw21).inputs)]

theorem row44_binding : (data.drop 44).take 1 = (originalEntries.drop 44).take 1 :=
  row44_view.trans (row44_source.trans row44_entry.symm)

numeric_data_binding row45_view : (data.drop 45).take 1 = (data45.drop 0).take 1

numeric_data_binding row45_source : (data45.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [22] Airbender.Compiler.MemoryNative.BigintCached.native.leaf22).isSome))]

numeric_data_binding row45_entry : (originalEntries.drop 45).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [22] Airbender.Compiler.MemoryNative.BigintCached.native.leaf22).isSome))]

theorem row45_binding : (data.drop 45).take 1 = (originalEntries.drop 45).take 1 :=
  row45_view.trans (row45_source.trans row45_entry.symm)

numeric_data_binding row46_view : (data.drop 46).take 1 = (data45.drop 1).take 1

numeric_data_binding row46_source : (data45.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw22).inputs)]

numeric_data_binding row46_entry : (originalEntries.drop 46).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw22).inputs)]

theorem row46_binding : (data.drop 46).take 1 = (originalEntries.drop 46).take 1 :=
  row46_view.trans (row46_source.trans row46_entry.symm)

numeric_data_binding row47_view : (data.drop 47).take 1 = (data45.drop 2).take 1

numeric_data_binding row47_source : (data45.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [23] Airbender.Compiler.MemoryNative.BigintCached.native.leaf23).isSome))]

numeric_data_binding row47_entry : (originalEntries.drop 47).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [23] Airbender.Compiler.MemoryNative.BigintCached.native.leaf23).isSome))]

theorem row47_binding : (data.drop 47).take 1 = (originalEntries.drop 47).take 1 :=
  row47_view.trans (row47_source.trans row47_entry.symm)

numeric_data_binding row48_view : (data.drop 48).take 1 = (data45.drop 3).take 1

numeric_data_binding row48_source : (data45.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw23).inputs)]

numeric_data_binding row48_entry : (originalEntries.drop 48).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw23).inputs)]

theorem row48_binding : (data.drop 48).take 1 = (originalEntries.drop 48).take 1 :=
  row48_view.trans (row48_source.trans row48_entry.symm)

numeric_data_binding row49_view : (data.drop 49).take 1 = (data49.drop 0).take 1

numeric_data_binding row49_source : (data49.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [24] Airbender.Compiler.MemoryNative.BigintCached.native.leaf24).isSome))]

numeric_data_binding row49_entry : (originalEntries.drop 49).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [24] Airbender.Compiler.MemoryNative.BigintCached.native.leaf24).isSome))]

theorem row49_binding : (data.drop 49).take 1 = (originalEntries.drop 49).take 1 :=
  row49_view.trans (row49_source.trans row49_entry.symm)

numeric_data_binding row50_view : (data.drop 50).take 1 = (data49.drop 1).take 1

numeric_data_binding row50_source : (data49.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw24).inputs)]

numeric_data_binding row50_entry : (originalEntries.drop 50).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw24).inputs)]

theorem row50_binding : (data.drop 50).take 1 = (originalEntries.drop 50).take 1 :=
  row50_view.trans (row50_source.trans row50_entry.symm)

numeric_data_binding row51_view : (data.drop 51).take 1 = (data49.drop 2).take 1

numeric_data_binding row51_source : (data49.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [25] Airbender.Compiler.MemoryNative.BigintCached.native.leaf25).isSome))]

numeric_data_binding row51_entry : (originalEntries.drop 51).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [25] Airbender.Compiler.MemoryNative.BigintCached.native.leaf25).isSome))]

theorem row51_binding : (data.drop 51).take 1 = (originalEntries.drop 51).take 1 :=
  row51_view.trans (row51_source.trans row51_entry.symm)

numeric_data_binding row52_view : (data.drop 52).take 1 = (data49.drop 3).take 1

numeric_data_binding row52_source : (data49.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw25).inputs)]

numeric_data_binding row52_entry : (originalEntries.drop 52).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw25).inputs)]

theorem row52_binding : (data.drop 52).take 1 = (originalEntries.drop 52).take 1 :=
  row52_view.trans (row52_source.trans row52_entry.symm)

numeric_data_binding row53_view : (data.drop 53).take 1 = (data53.drop 0).take 1

numeric_data_binding row53_source : (data53.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [26] Airbender.Compiler.MemoryNative.BigintCached.native.leaf26).isSome))]

numeric_data_binding row53_entry : (originalEntries.drop 53).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [26] Airbender.Compiler.MemoryNative.BigintCached.native.leaf26).isSome))]

theorem row53_binding : (data.drop 53).take 1 = (originalEntries.drop 53).take 1 :=
  row53_view.trans (row53_source.trans row53_entry.symm)

numeric_data_binding row54_view : (data.drop 54).take 1 = (data53.drop 1).take 1

numeric_data_binding row54_source : (data53.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw26).inputs)]

numeric_data_binding row54_entry : (originalEntries.drop 54).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw26).inputs)]

theorem row54_binding : (data.drop 54).take 1 = (originalEntries.drop 54).take 1 :=
  row54_view.trans (row54_source.trans row54_entry.symm)

numeric_data_binding row55_view : (data.drop 55).take 1 = (data53.drop 2).take 1

numeric_data_binding row55_source : (data53.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [27] Airbender.Compiler.MemoryNative.BigintCached.native.leaf27).isSome))]

numeric_data_binding row55_entry : (originalEntries.drop 55).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [27] Airbender.Compiler.MemoryNative.BigintCached.native.leaf27).isSome))]

theorem row55_binding : (data.drop 55).take 1 = (originalEntries.drop 55).take 1 :=
  row55_view.trans (row55_source.trans row55_entry.symm)

numeric_data_binding row56_view : (data.drop 56).take 1 = (data53.drop 3).take 1

numeric_data_binding row56_source : (data53.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw27).inputs)]

numeric_data_binding row56_entry : (originalEntries.drop 56).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw27).inputs)]

theorem row56_binding : (data.drop 56).take 1 = (originalEntries.drop 56).take 1 :=
  row56_view.trans (row56_source.trans row56_entry.symm)

numeric_data_binding row57_view : (data.drop 57).take 1 = (data57.drop 0).take 1

numeric_data_binding row57_source : (data57.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [28] Airbender.Compiler.MemoryNative.BigintCached.native.leaf28).isSome))]

numeric_data_binding row57_entry : (originalEntries.drop 57).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [28] Airbender.Compiler.MemoryNative.BigintCached.native.leaf28).isSome))]

theorem row57_binding : (data.drop 57).take 1 = (originalEntries.drop 57).take 1 :=
  row57_view.trans (row57_source.trans row57_entry.symm)

numeric_data_binding row58_view : (data.drop 58).take 1 = (data57.drop 1).take 1

numeric_data_binding row58_source : (data57.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw28).inputs)]

numeric_data_binding row58_entry : (originalEntries.drop 58).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw28).inputs)]

theorem row58_binding : (data.drop 58).take 1 = (originalEntries.drop 58).take 1 :=
  row58_view.trans (row58_source.trans row58_entry.symm)

numeric_data_binding row59_view : (data.drop 59).take 1 = (data57.drop 2).take 1

numeric_data_binding row59_source : (data57.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [29] Airbender.Compiler.MemoryNative.BigintCached.native.leaf29).isSome))]

numeric_data_binding row59_entry : (originalEntries.drop 59).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [29] Airbender.Compiler.MemoryNative.BigintCached.native.leaf29).isSome))]

theorem row59_binding : (data.drop 59).take 1 = (originalEntries.drop 59).take 1 :=
  row59_view.trans (row59_source.trans row59_entry.symm)

numeric_data_binding row60_view : (data.drop 60).take 1 = (data57.drop 3).take 1

numeric_data_binding row60_source : (data57.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw29).inputs)]

numeric_data_binding row60_entry : (originalEntries.drop 60).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw29).inputs)]

theorem row60_binding : (data.drop 60).take 1 = (originalEntries.drop 60).take 1 :=
  row60_view.trans (row60_source.trans row60_entry.symm)

numeric_data_binding row61_view : (data.drop 61).take 1 = (data61.drop 0).take 1

numeric_data_binding row61_source : (data61.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [30] Airbender.Compiler.MemoryNative.BigintCached.native.leaf30).isSome))]

numeric_data_binding row61_entry : (originalEntries.drop 61).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [30] Airbender.Compiler.MemoryNative.BigintCached.native.leaf30).isSome))]

theorem row61_binding : (data.drop 61).take 1 = (originalEntries.drop 61).take 1 :=
  row61_view.trans (row61_source.trans row61_entry.symm)

numeric_data_binding row62_view : (data.drop 62).take 1 = (data61.drop 1).take 1

numeric_data_binding row62_source : (data61.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw30).inputs)]

numeric_data_binding row62_entry : (originalEntries.drop 62).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw30).inputs)]

theorem row62_binding : (data.drop 62).take 1 = (originalEntries.drop 62).take 1 :=
  row62_view.trans (row62_source.trans row62_entry.symm)

numeric_data_binding row63_view : (data.drop 63).take 1 = (data61.drop 2).take 1

numeric_data_binding row63_source : (data61.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [31] Airbender.Compiler.MemoryNative.BigintCached.native.leaf31).isSome))]

numeric_data_binding row63_entry : (originalEntries.drop 63).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [31] Airbender.Compiler.MemoryNative.BigintCached.native.leaf31).isSome))]

theorem row63_binding : (data.drop 63).take 1 = (originalEntries.drop 63).take 1 :=
  row63_view.trans (row63_source.trans row63_entry.symm)

numeric_data_binding row64_view : (data.drop 64).take 1 = (data61.drop 3).take 1

numeric_data_binding row64_source : (data61.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw31).inputs)]

numeric_data_binding row64_entry : (originalEntries.drop 64).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw31).inputs)]

theorem row64_binding : (data.drop 64).take 1 = (originalEntries.drop 64).take 1 :=
  row64_view.trans (row64_source.trans row64_entry.symm)

numeric_data_binding row65_view : (data.drop 65).take 1 = (data65.drop 0).take 1

numeric_data_binding row65_source : (data65.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [32] Airbender.Compiler.MemoryNative.BigintCached.native.leaf32).isSome))]

numeric_data_binding row65_entry : (originalEntries.drop 65).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [32] Airbender.Compiler.MemoryNative.BigintCached.native.leaf32).isSome))]

theorem row65_binding : (data.drop 65).take 1 = (originalEntries.drop 65).take 1 :=
  row65_view.trans (row65_source.trans row65_entry.symm)

numeric_data_binding row66_view : (data.drop 66).take 1 = (data65.drop 1).take 1

numeric_data_binding row66_source : (data65.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw32).inputs)]

numeric_data_binding row66_entry : (originalEntries.drop 66).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw32).inputs)]

theorem row66_binding : (data.drop 66).take 1 = (originalEntries.drop 66).take 1 :=
  row66_view.trans (row66_source.trans row66_entry.symm)

numeric_data_binding row67_view : (data.drop 67).take 1 = (data65.drop 2).take 1

numeric_data_binding row67_source : (data65.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [33] Airbender.Compiler.MemoryNative.BigintCached.native.leaf33).isSome))]

numeric_data_binding row67_entry : (originalEntries.drop 67).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [33] Airbender.Compiler.MemoryNative.BigintCached.native.leaf33).isSome))]

theorem row67_binding : (data.drop 67).take 1 = (originalEntries.drop 67).take 1 :=
  row67_view.trans (row67_source.trans row67_entry.symm)

numeric_data_binding row68_view : (data.drop 68).take 1 = (data65.drop 3).take 1

numeric_data_binding row68_source : (data65.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw33).inputs)]

numeric_data_binding row68_entry : (originalEntries.drop 68).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw33).inputs)]

theorem row68_binding : (data.drop 68).take 1 = (originalEntries.drop 68).take 1 :=
  row68_view.trans (row68_source.trans row68_entry.symm)

numeric_data_binding row69_view : (data.drop 69).take 1 = (data69.drop 0).take 1

numeric_data_binding row69_source : (data69.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [34] Airbender.Compiler.MemoryNative.BigintCached.native.leaf34).isSome))]

numeric_data_binding row69_entry : (originalEntries.drop 69).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [34] Airbender.Compiler.MemoryNative.BigintCached.native.leaf34).isSome))]

theorem row69_binding : (data.drop 69).take 1 = (originalEntries.drop 69).take 1 :=
  row69_view.trans (row69_source.trans row69_entry.symm)

numeric_data_binding row70_view : (data.drop 70).take 1 = (data69.drop 1).take 1

numeric_data_binding row70_source : (data69.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw34).inputs)]

numeric_data_binding row70_entry : (originalEntries.drop 70).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw34).inputs)]

theorem row70_binding : (data.drop 70).take 1 = (originalEntries.drop 70).take 1 :=
  row70_view.trans (row70_source.trans row70_entry.symm)

numeric_data_binding row71_view : (data.drop 71).take 1 = (data69.drop 2).take 1

numeric_data_binding row71_source : (data69.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [35] Airbender.Compiler.MemoryNative.BigintCached.native.leaf35).isSome))]

numeric_data_binding row71_entry : (originalEntries.drop 71).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [35] Airbender.Compiler.MemoryNative.BigintCached.native.leaf35).isSome))]

theorem row71_binding : (data.drop 71).take 1 = (originalEntries.drop 71).take 1 :=
  row71_view.trans (row71_source.trans row71_entry.symm)

numeric_data_binding row72_view : (data.drop 72).take 1 = (data69.drop 3).take 1

numeric_data_binding row72_source : (data69.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw35).inputs)]

numeric_data_binding row72_entry : (originalEntries.drop 72).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw35).inputs)]

theorem row72_binding : (data.drop 72).take 1 = (originalEntries.drop 72).take 1 :=
  row72_view.trans (row72_source.trans row72_entry.symm)

numeric_data_binding row73_view : (data.drop 73).take 1 = (data73.drop 0).take 1

numeric_data_binding row73_source : (data73.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [36] Airbender.Compiler.MemoryNative.BigintCached.native.leaf36).isSome))]

numeric_data_binding row73_entry : (originalEntries.drop 73).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [36] Airbender.Compiler.MemoryNative.BigintCached.native.leaf36).isSome))]

theorem row73_binding : (data.drop 73).take 1 = (originalEntries.drop 73).take 1 :=
  row73_view.trans (row73_source.trans row73_entry.symm)

numeric_data_binding row74_view : (data.drop 74).take 1 = (data73.drop 1).take 1

numeric_data_binding row74_source : (data73.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw36).inputs)]

numeric_data_binding row74_entry : (originalEntries.drop 74).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw36).inputs)]

theorem row74_binding : (data.drop 74).take 1 = (originalEntries.drop 74).take 1 :=
  row74_view.trans (row74_source.trans row74_entry.symm)

numeric_data_binding row75_view : (data.drop 75).take 1 = (data73.drop 2).take 1

numeric_data_binding row75_source : (data73.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [37] Airbender.Compiler.MemoryNative.BigintCached.native.leaf37).isSome))]

numeric_data_binding row75_entry : (originalEntries.drop 75).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [37] Airbender.Compiler.MemoryNative.BigintCached.native.leaf37).isSome))]

theorem row75_binding : (data.drop 75).take 1 = (originalEntries.drop 75).take 1 :=
  row75_view.trans (row75_source.trans row75_entry.symm)

numeric_data_binding row76_view : (data.drop 76).take 1 = (data73.drop 3).take 1

numeric_data_binding row76_source : (data73.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw37).inputs)]

numeric_data_binding row76_entry : (originalEntries.drop 76).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw37).inputs)]

theorem row76_binding : (data.drop 76).take 1 = (originalEntries.drop 76).take 1 :=
  row76_view.trans (row76_source.trans row76_entry.symm)

numeric_data_binding row77_view : (data.drop 77).take 1 = (data77.drop 0).take 1

numeric_data_binding row77_source : (data77.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [38] Airbender.Compiler.MemoryNative.BigintCached.native.leaf38).isSome))]

numeric_data_binding row77_entry : (originalEntries.drop 77).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [38] Airbender.Compiler.MemoryNative.BigintCached.native.leaf38).isSome))]

theorem row77_binding : (data.drop 77).take 1 = (originalEntries.drop 77).take 1 :=
  row77_view.trans (row77_source.trans row77_entry.symm)

numeric_data_binding row78_view : (data.drop 78).take 1 = (data77.drop 1).take 1

numeric_data_binding row78_source : (data77.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw38).inputs)]

numeric_data_binding row78_entry : (originalEntries.drop 78).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw38).inputs)]

theorem row78_binding : (data.drop 78).take 1 = (originalEntries.drop 78).take 1 :=
  row78_view.trans (row78_source.trans row78_entry.symm)

numeric_data_binding row79_view : (data.drop 79).take 1 = (data77.drop 2).take 1

numeric_data_binding row79_source : (data77.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [39] Airbender.Compiler.MemoryNative.BigintCached.native.leaf39).isSome))]

numeric_data_binding row79_entry : (originalEntries.drop 79).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [39] Airbender.Compiler.MemoryNative.BigintCached.native.leaf39).isSome))]

theorem row79_binding : (data.drop 79).take 1 = (originalEntries.drop 79).take 1 :=
  row79_view.trans (row79_source.trans row79_entry.symm)

numeric_data_binding row80_view : (data.drop 80).take 1 = (data77.drop 3).take 1

numeric_data_binding row80_source : (data77.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw39).inputs)]

numeric_data_binding row80_entry : (originalEntries.drop 80).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw39).inputs)]

theorem row80_binding : (data.drop 80).take 1 = (originalEntries.drop 80).take 1 :=
  row80_view.trans (row80_source.trans row80_entry.symm)

numeric_data_binding row81_view : (data.drop 81).take 1 = (data81.drop 0).take 1

numeric_data_binding row81_source : (data81.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw0 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row81_entry : (originalEntries.drop 81).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw0 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row81_binding : (data.drop 81).take 1 = (originalEntries.drop 81).take 1 :=
  row81_view.trans (row81_source.trans row81_entry.symm)

numeric_data_binding row82_view : (data.drop 82).take 1 = (data81.drop 1).take 1

numeric_data_binding row82_source : (data81.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw1 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row82_entry : (originalEntries.drop 82).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw1 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row82_binding : (data.drop 82).take 1 = (originalEntries.drop 82).take 1 :=
  row82_view.trans (row82_source.trans row82_entry.symm)

numeric_data_binding row83_view : (data.drop 83).take 1 = (data81.drop 2).take 1

numeric_data_binding row83_source : (data81.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw4 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row83_entry : (originalEntries.drop 83).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw4 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row83_binding : (data.drop 83).take 1 = (originalEntries.drop 83).take 1 :=
  row83_view.trans (row83_source.trans row83_entry.symm)

numeric_data_binding row84_view : (data.drop 84).take 1 = (data81.drop 3).take 1

numeric_data_binding row84_source : (data81.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw5 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row84_entry : (originalEntries.drop 84).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw5 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row84_binding : (data.drop 84).take 1 = (originalEntries.drop 84).take 1 :=
  row84_view.trans (row84_source.trans row84_entry.symm)

numeric_data_binding row85_view : (data.drop 85).take 1 = (data85.drop 0).take 1

numeric_data_binding row85_source : (data85.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate4 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw8 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row85_entry : (originalEntries.drop 85).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate4 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw8 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row85_binding : (data.drop 85).take 1 = (originalEntries.drop 85).take 1 :=
  row85_view.trans (row85_source.trans row85_entry.symm)

numeric_data_binding row86_view : (data.drop 86).take 1 = (data85.drop 1).take 1

numeric_data_binding row86_source : (data85.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate5 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw9 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row86_entry : (originalEntries.drop 86).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate5 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw9 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row86_binding : (data.drop 86).take 1 = (originalEntries.drop 86).take 1 :=
  row86_view.trans (row86_source.trans row86_entry.symm)

numeric_data_binding row87_view : (data.drop 87).take 1 = (data85.drop 2).take 1

numeric_data_binding row87_source : (data85.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate6 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw12 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row87_entry : (originalEntries.drop 87).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate6 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw12 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row87_binding : (data.drop 87).take 1 = (originalEntries.drop 87).take 1 :=
  row87_view.trans (row87_source.trans row87_entry.symm)

numeric_data_binding row88_view : (data.drop 88).take 1 = (data85.drop 3).take 1

numeric_data_binding row88_source : (data85.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate7 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw13 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row88_entry : (originalEntries.drop 88).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate7 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw13 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row88_binding : (data.drop 88).take 1 = (originalEntries.drop 88).take 1 :=
  row88_view.trans (row88_source.trans row88_entry.symm)

numeric_data_binding row89_view : (data.drop 89).take 1 = (data89.drop 0).take 1

numeric_data_binding row89_source : (data89.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate8 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw16 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row89_entry : (originalEntries.drop 89).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate8 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw16 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row89_binding : (data.drop 89).take 1 = (originalEntries.drop 89).take 1 :=
  row89_view.trans (row89_source.trans row89_entry.symm)

numeric_data_binding row90_view : (data.drop 90).take 1 = (data89.drop 1).take 1

numeric_data_binding row90_source : (data89.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate9 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw17 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row90_entry : (originalEntries.drop 90).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate9 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw17 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row90_binding : (data.drop 90).take 1 = (originalEntries.drop 90).take 1 :=
  row90_view.trans (row90_source.trans row90_entry.symm)

numeric_data_binding row91_view : (data.drop 91).take 1 = (data89.drop 2).take 1

numeric_data_binding row91_source : (data89.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate10 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw20 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row91_entry : (originalEntries.drop 91).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate10 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw20 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row91_binding : (data.drop 91).take 1 = (originalEntries.drop 91).take 1 :=
  row91_view.trans (row91_source.trans row91_entry.symm)

numeric_data_binding row92_view : (data.drop 92).take 1 = (data89.drop 3).take 1

numeric_data_binding row92_source : (data89.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate11 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw21 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row92_entry : (originalEntries.drop 92).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate11 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw21 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row92_binding : (data.drop 92).take 1 = (originalEntries.drop 92).take 1 :=
  row92_view.trans (row92_source.trans row92_entry.symm)

numeric_data_binding row93_view : (data.drop 93).take 1 = (data93.drop 0).take 1

numeric_data_binding row93_source : (data93.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate12 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw24 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row93_entry : (originalEntries.drop 93).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate12 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw24 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row93_binding : (data.drop 93).take 1 = (originalEntries.drop 93).take 1 :=
  row93_view.trans (row93_source.trans row93_entry.symm)

numeric_data_binding row94_view : (data.drop 94).take 1 = (data93.drop 1).take 1

numeric_data_binding row94_source : (data93.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate13 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw25 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row94_entry : (originalEntries.drop 94).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate13 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw25 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row94_binding : (data.drop 94).take 1 = (originalEntries.drop 94).take 1 :=
  row94_view.trans (row94_source.trans row94_entry.symm)

numeric_data_binding row95_view : (data.drop 95).take 1 = (data93.drop 2).take 1

numeric_data_binding row95_source : (data93.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate14 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw28 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row95_entry : (originalEntries.drop 95).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate14 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw28 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row95_binding : (data.drop 95).take 1 = (originalEntries.drop 95).take 1 :=
  row95_view.trans (row95_source.trans row95_entry.symm)

numeric_data_binding row96_view : (data.drop 96).take 1 = (data93.drop 3).take 1

numeric_data_binding row96_source : (data93.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate15 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[15]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw29 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row96_entry : (originalEntries.drop 96).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate15 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[15]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw29 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row96_binding : (data.drop 96).take 1 = (originalEntries.drop 96).take 1 :=
  row96_view.trans (row96_source.trans row96_entry.symm)

numeric_data_binding row97_view : (data.drop 97).take 1 = (data97.drop 0).take 1

numeric_data_binding row97_source : (data97.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate16 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[16]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw32 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row97_entry : (originalEntries.drop 97).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate16 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[16]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw32 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row97_binding : (data.drop 97).take 1 = (originalEntries.drop 97).take 1 :=
  row97_view.trans (row97_source.trans row97_entry.symm)

numeric_data_binding row98_view : (data.drop 98).take 1 = (data97.drop 1).take 1

numeric_data_binding row98_source : (data97.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate17 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[17]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw33 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row98_entry : (originalEntries.drop 98).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate17 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[17]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw33 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row98_binding : (data.drop 98).take 1 = (originalEntries.drop 98).take 1 :=
  row98_view.trans (row98_source.trans row98_entry.symm)

numeric_data_binding row99_view : (data.drop 99).take 1 = (data97.drop 2).take 1

numeric_data_binding row99_source : (data97.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate18 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[18]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw36 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row99_entry : (originalEntries.drop 99).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate18 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[18]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw36 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row99_binding : (data.drop 99).take 1 = (originalEntries.drop 99).take 1 :=
  row99_view.trans (row99_source.trans row99_entry.symm)

numeric_data_binding row100_view : (data.drop 100).take 1 = (data97.drop 3).take 1

numeric_data_binding row100_source : (data97.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate19 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[19]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw37 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row100_entry : (originalEntries.drop 100).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate19 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[19]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw37 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row100_binding : (data.drop 100).take 1 = (originalEntries.drop 100).take 1 :=
  row100_view.trans (row100_source.trans row100_entry.symm)

numeric_data_binding row101_view : (data.drop 101).take 1 = (data101.drop 0).take 1

numeric_data_binding row101_source : (data101.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing [(GKRAddress.InnerLayer 5 0)])]

numeric_data_binding row101_entry : (originalEntries.drop 101).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing [(GKRAddress.InnerLayer 5 0)])]

theorem row101_binding : (data.drop 101).take 1 = (originalEntries.drop 101).take 1 :=
  row101_view.trans (row101_source.trans row101_entry.symm)

numeric_data_binding row102_view : (data.drop 102).take 1 = (data101.drop 1).take 1

numeric_data_binding row102_source : (data101.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw2 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row102_entry : (originalEntries.drop 102).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw2 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row102_binding : (data.drop 102).take 1 = (originalEntries.drop 102).take 1 :=
  row102_view.trans (row102_source.trans row102_entry.symm)

numeric_data_binding row103_view : (data.drop 103).take 1 = (data101.drop 2).take 1

numeric_data_binding row103_source : (data101.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw3 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row103_entry : (originalEntries.drop 103).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw3 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row103_binding : (data.drop 103).take 1 = (originalEntries.drop 103).take 1 :=
  row103_view.trans (row103_source.trans row103_entry.symm)

numeric_data_binding row104_view : (data.drop 104).take 1 = (data101.drop 3).take 1

numeric_data_binding row104_source : (data101.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw6 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row104_entry : (originalEntries.drop 104).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw6 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row104_binding : (data.drop 104).take 1 = (originalEntries.drop 104).take 1 :=
  row104_view.trans (row104_source.trans row104_entry.symm)

numeric_data_binding row105_view : (data.drop 105).take 1 = (data105.drop 0).take 1

numeric_data_binding row105_source : (data105.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw7 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row105_entry : (originalEntries.drop 105).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw7 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row105_binding : (data.drop 105).take 1 = (originalEntries.drop 105).take 1 :=
  row105_view.trans (row105_source.trans row105_entry.symm)

numeric_data_binding row106_view : (data.drop 106).take 1 = (data105.drop 1).take 1

numeric_data_binding row106_source : (data105.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate4 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw10 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row106_entry : (originalEntries.drop 106).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate4 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw10 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row106_binding : (data.drop 106).take 1 = (originalEntries.drop 106).take 1 :=
  row106_view.trans (row106_source.trans row106_entry.symm)

numeric_data_binding row107_view : (data.drop 107).take 1 = (data105.drop 2).take 1

numeric_data_binding row107_source : (data105.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate5 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw11 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row107_entry : (originalEntries.drop 107).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate5 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw11 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row107_binding : (data.drop 107).take 1 = (originalEntries.drop 107).take 1 :=
  row107_view.trans (row107_source.trans row107_entry.symm)

numeric_data_binding row108_view : (data.drop 108).take 1 = (data105.drop 3).take 1

numeric_data_binding row108_source : (data105.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate6 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw14 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row108_entry : (originalEntries.drop 108).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate6 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw14 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row108_binding : (data.drop 108).take 1 = (originalEntries.drop 108).take 1 :=
  row108_view.trans (row108_source.trans row108_entry.symm)

numeric_data_binding row109_view : (data.drop 109).take 1 = (data109.drop 0).take 1

numeric_data_binding row109_source : (data109.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate7 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw15 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row109_entry : (originalEntries.drop 109).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate7 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw15 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row109_binding : (data.drop 109).take 1 = (originalEntries.drop 109).take 1 :=
  row109_view.trans (row109_source.trans row109_entry.symm)

numeric_data_binding row110_view : (data.drop 110).take 1 = (data109.drop 1).take 1

numeric_data_binding row110_source : (data109.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate8 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw18 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row110_entry : (originalEntries.drop 110).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate8 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw18 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row110_binding : (data.drop 110).take 1 = (originalEntries.drop 110).take 1 :=
  row110_view.trans (row110_source.trans row110_entry.symm)

numeric_data_binding row111_view : (data.drop 111).take 1 = (data109.drop 2).take 1

numeric_data_binding row111_source : (data109.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate9 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw19 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row111_entry : (originalEntries.drop 111).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate9 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw19 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row111_binding : (data.drop 111).take 1 = (originalEntries.drop 111).take 1 :=
  row111_view.trans (row111_source.trans row111_entry.symm)

numeric_data_binding row112_view : (data.drop 112).take 1 = (data109.drop 3).take 1

numeric_data_binding row112_source : (data109.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate10 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw22 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row112_entry : (originalEntries.drop 112).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate10 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw22 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row112_binding : (data.drop 112).take 1 = (originalEntries.drop 112).take 1 :=
  row112_view.trans (row112_source.trans row112_entry.symm)

numeric_data_binding row113_view : (data.drop 113).take 1 = (data113.drop 0).take 1

numeric_data_binding row113_source : (data113.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate11 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw23 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row113_entry : (originalEntries.drop 113).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate11 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw23 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row113_binding : (data.drop 113).take 1 = (originalEntries.drop 113).take 1 :=
  row113_view.trans (row113_source.trans row113_entry.symm)

numeric_data_binding row114_view : (data.drop 114).take 1 = (data113.drop 1).take 1

numeric_data_binding row114_source : (data113.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate12 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw26 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row114_entry : (originalEntries.drop 114).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate12 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw26 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row114_binding : (data.drop 114).take 1 = (originalEntries.drop 114).take 1 :=
  row114_view.trans (row114_source.trans row114_entry.symm)

numeric_data_binding row115_view : (data.drop 115).take 1 = (data113.drop 2).take 1

numeric_data_binding row115_source : (data113.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate13 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw27 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row115_entry : (originalEntries.drop 115).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate13 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw27 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row115_binding : (data.drop 115).take 1 = (originalEntries.drop 115).take 1 :=
  row115_view.trans (row115_source.trans row115_entry.symm)

numeric_data_binding row116_view : (data.drop 116).take 1 = (data113.drop 3).take 1

numeric_data_binding row116_source : (data113.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate14 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw30 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row116_entry : (originalEntries.drop 116).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate14 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw30 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row116_binding : (data.drop 116).take 1 = (originalEntries.drop 116).take 1 :=
  row116_view.trans (row116_source.trans row116_entry.symm)

numeric_data_binding row117_view : (data.drop 117).take 1 = (data117.drop 0).take 1

numeric_data_binding row117_source : (data117.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate15 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[15]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw31 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row117_entry : (originalEntries.drop 117).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate15 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[15]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw31 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row117_binding : (data.drop 117).take 1 = (originalEntries.drop 117).take 1 :=
  row117_view.trans (row117_source.trans row117_entry.symm)

numeric_data_binding row118_view : (data.drop 118).take 1 = (data117.drop 1).take 1

numeric_data_binding row118_source : (data117.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate16 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[16]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw34 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row118_entry : (originalEntries.drop 118).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate16 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[16]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw34 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row118_binding : (data.drop 118).take 1 = (originalEntries.drop 118).take 1 :=
  row118_view.trans (row118_source.trans row118_entry.symm)

numeric_data_binding row119_view : (data.drop 119).take 1 = (data117.drop 2).take 1

numeric_data_binding row119_source : (data117.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate17 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[17]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw35 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row119_entry : (originalEntries.drop 119).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate17 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[17]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw35 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row119_binding : (data.drop 119).take 1 = (originalEntries.drop 119).take 1 :=
  row119_view.trans (row119_source.trans row119_entry.symm)

numeric_data_binding row120_view : (data.drop 120).take 1 = (data117.drop 3).take 1

numeric_data_binding row120_source : (data117.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate18 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[18]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw38 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row120_entry : (originalEntries.drop 120).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate18 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[18]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw38 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row120_binding : (data.drop 120).take 1 = (originalEntries.drop 120).take 1 :=
  row120_view.trans (row120_source.trans row120_entry.symm)

numeric_data_binding row121_view : (data.drop 121).take 1 = (data121.drop 0).take 1

numeric_data_binding row121_source : (data121.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate19 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[19]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw39 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

numeric_data_binding row121_entry : (originalEntries.drop 121).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate19 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[19]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw39 Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem row121_binding : (data.drop 121).take 1 = (originalEntries.drop 121).take 1 :=
  row121_view.trans (row121_source.trans row121_entry.symm)

numeric_data_binding row122_view : (data.drop 122).take 1 = (data121.drop 1).take 1

numeric_data_binding row122_source : (data121.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing [(GKRAddress.InnerLayer 5 0)])]

numeric_data_binding row122_entry : (originalEntries.drop 122).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing [(GKRAddress.InnerLayer 5 0)])]

theorem row122_binding : (data.drop 122).take 1 = (originalEntries.drop 122).take 1 :=
  row122_view.trans (row122_source.trans row122_entry.symm)

theorem entriesNode1_2 : (data.drop 1).take 2 = (originalEntries.drop 1).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 1 1 1 2 2 rfl rfl row1_binding row2_binding

theorem entriesNode0_3 : (data.drop 0).take 3 = (originalEntries.drop 0).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 1 2 1 3 rfl rfl row0_binding entriesNode1_2

theorem entriesNode3_2 : (data.drop 3).take 2 = (originalEntries.drop 3).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 3 1 1 4 2 rfl rfl row3_binding row4_binding

theorem entriesNode5_2 : (data.drop 5).take 2 = (originalEntries.drop 5).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 5 1 1 6 2 rfl rfl row5_binding row6_binding

theorem entriesNode3_4 : (data.drop 3).take 4 = (originalEntries.drop 3).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 3 2 2 5 4 rfl rfl entriesNode3_2 entriesNode5_2

theorem entriesNode0_7 : (data.drop 0).take 7 = (originalEntries.drop 0).take 7 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 3 4 3 7 rfl rfl entriesNode0_3 entriesNode3_4

theorem entriesNode7_2 : (data.drop 7).take 2 = (originalEntries.drop 7).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 7 1 1 8 2 rfl rfl row7_binding row8_binding

theorem entriesNode9_2 : (data.drop 9).take 2 = (originalEntries.drop 9).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 9 1 1 10 2 rfl rfl row9_binding row10_binding

theorem entriesNode7_4 : (data.drop 7).take 4 = (originalEntries.drop 7).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 7 2 2 9 4 rfl rfl entriesNode7_2 entriesNode9_2

theorem entriesNode11_2 : (data.drop 11).take 2 = (originalEntries.drop 11).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 11 1 1 12 2 rfl rfl row11_binding row12_binding

theorem entriesNode13_2 : (data.drop 13).take 2 = (originalEntries.drop 13).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 13 1 1 14 2 rfl rfl row13_binding row14_binding

theorem entriesNode11_4 : (data.drop 11).take 4 = (originalEntries.drop 11).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 11 2 2 13 4 rfl rfl entriesNode11_2 entriesNode13_2

theorem entriesNode7_8 : (data.drop 7).take 8 = (originalEntries.drop 7).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 7 4 4 11 8 rfl rfl entriesNode7_4 entriesNode11_4

theorem entriesNode0_15 : (data.drop 0).take 15 = (originalEntries.drop 0).take 15 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 7 8 7 15 rfl rfl entriesNode0_7 entriesNode7_8

theorem entriesNode16_2 : (data.drop 16).take 2 = (originalEntries.drop 16).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 16 1 1 17 2 rfl rfl row16_binding row17_binding

theorem entriesNode15_3 : (data.drop 15).take 3 = (originalEntries.drop 15).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 15 1 2 16 3 rfl rfl row15_binding entriesNode16_2

theorem entriesNode18_2 : (data.drop 18).take 2 = (originalEntries.drop 18).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 18 1 1 19 2 rfl rfl row18_binding row19_binding

theorem entriesNode20_2 : (data.drop 20).take 2 = (originalEntries.drop 20).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 20 1 1 21 2 rfl rfl row20_binding row21_binding

theorem entriesNode18_4 : (data.drop 18).take 4 = (originalEntries.drop 18).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 18 2 2 20 4 rfl rfl entriesNode18_2 entriesNode20_2

theorem entriesNode15_7 : (data.drop 15).take 7 = (originalEntries.drop 15).take 7 :=
  NumericWorkerPortChecks.merge_at data originalEntries 15 3 4 18 7 rfl rfl entriesNode15_3 entriesNode18_4

theorem entriesNode22_2 : (data.drop 22).take 2 = (originalEntries.drop 22).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 22 1 1 23 2 rfl rfl row22_binding row23_binding

theorem entriesNode24_2 : (data.drop 24).take 2 = (originalEntries.drop 24).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 24 1 1 25 2 rfl rfl row24_binding row25_binding

theorem entriesNode22_4 : (data.drop 22).take 4 = (originalEntries.drop 22).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 22 2 2 24 4 rfl rfl entriesNode22_2 entriesNode24_2

theorem entriesNode26_2 : (data.drop 26).take 2 = (originalEntries.drop 26).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 26 1 1 27 2 rfl rfl row26_binding row27_binding

theorem entriesNode28_2 : (data.drop 28).take 2 = (originalEntries.drop 28).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 28 1 1 29 2 rfl rfl row28_binding row29_binding

theorem entriesNode26_4 : (data.drop 26).take 4 = (originalEntries.drop 26).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 26 2 2 28 4 rfl rfl entriesNode26_2 entriesNode28_2

theorem entriesNode22_8 : (data.drop 22).take 8 = (originalEntries.drop 22).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 22 4 4 26 8 rfl rfl entriesNode22_4 entriesNode26_4

theorem entriesNode15_15 : (data.drop 15).take 15 = (originalEntries.drop 15).take 15 :=
  NumericWorkerPortChecks.merge_at data originalEntries 15 7 8 22 15 rfl rfl entriesNode15_7 entriesNode22_8

theorem entriesNode0_30 : (data.drop 0).take 30 = (originalEntries.drop 0).take 30 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 15 15 15 30 rfl rfl entriesNode0_15 entriesNode15_15

theorem entriesNode31_2 : (data.drop 31).take 2 = (originalEntries.drop 31).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 31 1 1 32 2 rfl rfl row31_binding row32_binding

theorem entriesNode30_3 : (data.drop 30).take 3 = (originalEntries.drop 30).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 30 1 2 31 3 rfl rfl row30_binding entriesNode31_2

theorem entriesNode33_2 : (data.drop 33).take 2 = (originalEntries.drop 33).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 33 1 1 34 2 rfl rfl row33_binding row34_binding

theorem entriesNode35_2 : (data.drop 35).take 2 = (originalEntries.drop 35).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 35 1 1 36 2 rfl rfl row35_binding row36_binding

theorem entriesNode33_4 : (data.drop 33).take 4 = (originalEntries.drop 33).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 33 2 2 35 4 rfl rfl entriesNode33_2 entriesNode35_2

theorem entriesNode30_7 : (data.drop 30).take 7 = (originalEntries.drop 30).take 7 :=
  NumericWorkerPortChecks.merge_at data originalEntries 30 3 4 33 7 rfl rfl entriesNode30_3 entriesNode33_4

theorem entriesNode37_2 : (data.drop 37).take 2 = (originalEntries.drop 37).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 37 1 1 38 2 rfl rfl row37_binding row38_binding

theorem entriesNode39_2 : (data.drop 39).take 2 = (originalEntries.drop 39).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 39 1 1 40 2 rfl rfl row39_binding row40_binding

theorem entriesNode37_4 : (data.drop 37).take 4 = (originalEntries.drop 37).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 37 2 2 39 4 rfl rfl entriesNode37_2 entriesNode39_2

theorem entriesNode41_2 : (data.drop 41).take 2 = (originalEntries.drop 41).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 41 1 1 42 2 rfl rfl row41_binding row42_binding

theorem entriesNode43_2 : (data.drop 43).take 2 = (originalEntries.drop 43).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 43 1 1 44 2 rfl rfl row43_binding row44_binding

theorem entriesNode41_4 : (data.drop 41).take 4 = (originalEntries.drop 41).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 41 2 2 43 4 rfl rfl entriesNode41_2 entriesNode43_2

theorem entriesNode37_8 : (data.drop 37).take 8 = (originalEntries.drop 37).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 37 4 4 41 8 rfl rfl entriesNode37_4 entriesNode41_4

theorem entriesNode30_15 : (data.drop 30).take 15 = (originalEntries.drop 30).take 15 :=
  NumericWorkerPortChecks.merge_at data originalEntries 30 7 8 37 15 rfl rfl entriesNode30_7 entriesNode37_8

theorem entriesNode45_2 : (data.drop 45).take 2 = (originalEntries.drop 45).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 45 1 1 46 2 rfl rfl row45_binding row46_binding

theorem entriesNode47_2 : (data.drop 47).take 2 = (originalEntries.drop 47).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 47 1 1 48 2 rfl rfl row47_binding row48_binding

theorem entriesNode45_4 : (data.drop 45).take 4 = (originalEntries.drop 45).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 45 2 2 47 4 rfl rfl entriesNode45_2 entriesNode47_2

theorem entriesNode49_2 : (data.drop 49).take 2 = (originalEntries.drop 49).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 49 1 1 50 2 rfl rfl row49_binding row50_binding

theorem entriesNode51_2 : (data.drop 51).take 2 = (originalEntries.drop 51).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 51 1 1 52 2 rfl rfl row51_binding row52_binding

theorem entriesNode49_4 : (data.drop 49).take 4 = (originalEntries.drop 49).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 49 2 2 51 4 rfl rfl entriesNode49_2 entriesNode51_2

theorem entriesNode45_8 : (data.drop 45).take 8 = (originalEntries.drop 45).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 45 4 4 49 8 rfl rfl entriesNode45_4 entriesNode49_4

theorem entriesNode53_2 : (data.drop 53).take 2 = (originalEntries.drop 53).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 53 1 1 54 2 rfl rfl row53_binding row54_binding

theorem entriesNode55_2 : (data.drop 55).take 2 = (originalEntries.drop 55).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 55 1 1 56 2 rfl rfl row55_binding row56_binding

theorem entriesNode53_4 : (data.drop 53).take 4 = (originalEntries.drop 53).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 53 2 2 55 4 rfl rfl entriesNode53_2 entriesNode55_2

theorem entriesNode57_2 : (data.drop 57).take 2 = (originalEntries.drop 57).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 57 1 1 58 2 rfl rfl row57_binding row58_binding

theorem entriesNode59_2 : (data.drop 59).take 2 = (originalEntries.drop 59).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 59 1 1 60 2 rfl rfl row59_binding row60_binding

theorem entriesNode57_4 : (data.drop 57).take 4 = (originalEntries.drop 57).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 57 2 2 59 4 rfl rfl entriesNode57_2 entriesNode59_2

theorem entriesNode53_8 : (data.drop 53).take 8 = (originalEntries.drop 53).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 53 4 4 57 8 rfl rfl entriesNode53_4 entriesNode57_4

theorem entriesNode45_16 : (data.drop 45).take 16 = (originalEntries.drop 45).take 16 :=
  NumericWorkerPortChecks.merge_at data originalEntries 45 8 8 53 16 rfl rfl entriesNode45_8 entriesNode53_8

theorem entriesNode30_31 : (data.drop 30).take 31 = (originalEntries.drop 30).take 31 :=
  NumericWorkerPortChecks.merge_at data originalEntries 30 15 16 45 31 rfl rfl entriesNode30_15 entriesNode45_16

theorem entriesNode0_61 : (data.drop 0).take 61 = (originalEntries.drop 0).take 61 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 30 31 30 61 rfl rfl entriesNode0_30 entriesNode30_31

theorem entriesNode62_2 : (data.drop 62).take 2 = (originalEntries.drop 62).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 62 1 1 63 2 rfl rfl row62_binding row63_binding

theorem entriesNode61_3 : (data.drop 61).take 3 = (originalEntries.drop 61).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 61 1 2 62 3 rfl rfl row61_binding entriesNode62_2

theorem entriesNode64_2 : (data.drop 64).take 2 = (originalEntries.drop 64).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 64 1 1 65 2 rfl rfl row64_binding row65_binding

theorem entriesNode66_2 : (data.drop 66).take 2 = (originalEntries.drop 66).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 66 1 1 67 2 rfl rfl row66_binding row67_binding

theorem entriesNode64_4 : (data.drop 64).take 4 = (originalEntries.drop 64).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 64 2 2 66 4 rfl rfl entriesNode64_2 entriesNode66_2

theorem entriesNode61_7 : (data.drop 61).take 7 = (originalEntries.drop 61).take 7 :=
  NumericWorkerPortChecks.merge_at data originalEntries 61 3 4 64 7 rfl rfl entriesNode61_3 entriesNode64_4

theorem entriesNode68_2 : (data.drop 68).take 2 = (originalEntries.drop 68).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 68 1 1 69 2 rfl rfl row68_binding row69_binding

theorem entriesNode70_2 : (data.drop 70).take 2 = (originalEntries.drop 70).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 70 1 1 71 2 rfl rfl row70_binding row71_binding

theorem entriesNode68_4 : (data.drop 68).take 4 = (originalEntries.drop 68).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 68 2 2 70 4 rfl rfl entriesNode68_2 entriesNode70_2

theorem entriesNode72_2 : (data.drop 72).take 2 = (originalEntries.drop 72).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 72 1 1 73 2 rfl rfl row72_binding row73_binding

theorem entriesNode74_2 : (data.drop 74).take 2 = (originalEntries.drop 74).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 74 1 1 75 2 rfl rfl row74_binding row75_binding

theorem entriesNode72_4 : (data.drop 72).take 4 = (originalEntries.drop 72).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 72 2 2 74 4 rfl rfl entriesNode72_2 entriesNode74_2

theorem entriesNode68_8 : (data.drop 68).take 8 = (originalEntries.drop 68).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 68 4 4 72 8 rfl rfl entriesNode68_4 entriesNode72_4

theorem entriesNode61_15 : (data.drop 61).take 15 = (originalEntries.drop 61).take 15 :=
  NumericWorkerPortChecks.merge_at data originalEntries 61 7 8 68 15 rfl rfl entriesNode61_7 entriesNode68_8

theorem entriesNode76_2 : (data.drop 76).take 2 = (originalEntries.drop 76).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 76 1 1 77 2 rfl rfl row76_binding row77_binding

theorem entriesNode78_2 : (data.drop 78).take 2 = (originalEntries.drop 78).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 78 1 1 79 2 rfl rfl row78_binding row79_binding

theorem entriesNode76_4 : (data.drop 76).take 4 = (originalEntries.drop 76).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 76 2 2 78 4 rfl rfl entriesNode76_2 entriesNode78_2

theorem entriesNode80_2 : (data.drop 80).take 2 = (originalEntries.drop 80).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 80 1 1 81 2 rfl rfl row80_binding row81_binding

theorem entriesNode82_2 : (data.drop 82).take 2 = (originalEntries.drop 82).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 82 1 1 83 2 rfl rfl row82_binding row83_binding

theorem entriesNode80_4 : (data.drop 80).take 4 = (originalEntries.drop 80).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 80 2 2 82 4 rfl rfl entriesNode80_2 entriesNode82_2

theorem entriesNode76_8 : (data.drop 76).take 8 = (originalEntries.drop 76).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 76 4 4 80 8 rfl rfl entriesNode76_4 entriesNode80_4

theorem entriesNode84_2 : (data.drop 84).take 2 = (originalEntries.drop 84).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 84 1 1 85 2 rfl rfl row84_binding row85_binding

theorem entriesNode86_2 : (data.drop 86).take 2 = (originalEntries.drop 86).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 86 1 1 87 2 rfl rfl row86_binding row87_binding

theorem entriesNode84_4 : (data.drop 84).take 4 = (originalEntries.drop 84).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 84 2 2 86 4 rfl rfl entriesNode84_2 entriesNode86_2

theorem entriesNode88_2 : (data.drop 88).take 2 = (originalEntries.drop 88).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 88 1 1 89 2 rfl rfl row88_binding row89_binding

theorem entriesNode90_2 : (data.drop 90).take 2 = (originalEntries.drop 90).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 90 1 1 91 2 rfl rfl row90_binding row91_binding

theorem entriesNode88_4 : (data.drop 88).take 4 = (originalEntries.drop 88).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 88 2 2 90 4 rfl rfl entriesNode88_2 entriesNode90_2

theorem entriesNode84_8 : (data.drop 84).take 8 = (originalEntries.drop 84).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 84 4 4 88 8 rfl rfl entriesNode84_4 entriesNode88_4

theorem entriesNode76_16 : (data.drop 76).take 16 = (originalEntries.drop 76).take 16 :=
  NumericWorkerPortChecks.merge_at data originalEntries 76 8 8 84 16 rfl rfl entriesNode76_8 entriesNode84_8

theorem entriesNode61_31 : (data.drop 61).take 31 = (originalEntries.drop 61).take 31 :=
  NumericWorkerPortChecks.merge_at data originalEntries 61 15 16 76 31 rfl rfl entriesNode61_15 entriesNode76_16

theorem entriesNode93_2 : (data.drop 93).take 2 = (originalEntries.drop 93).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 93 1 1 94 2 rfl rfl row93_binding row94_binding

theorem entriesNode92_3 : (data.drop 92).take 3 = (originalEntries.drop 92).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 92 1 2 93 3 rfl rfl row92_binding entriesNode93_2

theorem entriesNode95_2 : (data.drop 95).take 2 = (originalEntries.drop 95).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 95 1 1 96 2 rfl rfl row95_binding row96_binding

theorem entriesNode97_2 : (data.drop 97).take 2 = (originalEntries.drop 97).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 97 1 1 98 2 rfl rfl row97_binding row98_binding

theorem entriesNode95_4 : (data.drop 95).take 4 = (originalEntries.drop 95).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 95 2 2 97 4 rfl rfl entriesNode95_2 entriesNode97_2

theorem entriesNode92_7 : (data.drop 92).take 7 = (originalEntries.drop 92).take 7 :=
  NumericWorkerPortChecks.merge_at data originalEntries 92 3 4 95 7 rfl rfl entriesNode92_3 entriesNode95_4

theorem entriesNode99_2 : (data.drop 99).take 2 = (originalEntries.drop 99).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 99 1 1 100 2 rfl rfl row99_binding row100_binding

theorem entriesNode101_2 : (data.drop 101).take 2 = (originalEntries.drop 101).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 101 1 1 102 2 rfl rfl row101_binding row102_binding

theorem entriesNode99_4 : (data.drop 99).take 4 = (originalEntries.drop 99).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 99 2 2 101 4 rfl rfl entriesNode99_2 entriesNode101_2

theorem entriesNode103_2 : (data.drop 103).take 2 = (originalEntries.drop 103).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 103 1 1 104 2 rfl rfl row103_binding row104_binding

theorem entriesNode105_2 : (data.drop 105).take 2 = (originalEntries.drop 105).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 105 1 1 106 2 rfl rfl row105_binding row106_binding

theorem entriesNode103_4 : (data.drop 103).take 4 = (originalEntries.drop 103).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 103 2 2 105 4 rfl rfl entriesNode103_2 entriesNode105_2

theorem entriesNode99_8 : (data.drop 99).take 8 = (originalEntries.drop 99).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 99 4 4 103 8 rfl rfl entriesNode99_4 entriesNode103_4

theorem entriesNode92_15 : (data.drop 92).take 15 = (originalEntries.drop 92).take 15 :=
  NumericWorkerPortChecks.merge_at data originalEntries 92 7 8 99 15 rfl rfl entriesNode92_7 entriesNode99_8

theorem entriesNode107_2 : (data.drop 107).take 2 = (originalEntries.drop 107).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 107 1 1 108 2 rfl rfl row107_binding row108_binding

theorem entriesNode109_2 : (data.drop 109).take 2 = (originalEntries.drop 109).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 109 1 1 110 2 rfl rfl row109_binding row110_binding

theorem entriesNode107_4 : (data.drop 107).take 4 = (originalEntries.drop 107).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 107 2 2 109 4 rfl rfl entriesNode107_2 entriesNode109_2

theorem entriesNode111_2 : (data.drop 111).take 2 = (originalEntries.drop 111).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 111 1 1 112 2 rfl rfl row111_binding row112_binding

theorem entriesNode113_2 : (data.drop 113).take 2 = (originalEntries.drop 113).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 113 1 1 114 2 rfl rfl row113_binding row114_binding

theorem entriesNode111_4 : (data.drop 111).take 4 = (originalEntries.drop 111).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 111 2 2 113 4 rfl rfl entriesNode111_2 entriesNode113_2

theorem entriesNode107_8 : (data.drop 107).take 8 = (originalEntries.drop 107).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 107 4 4 111 8 rfl rfl entriesNode107_4 entriesNode111_4

theorem entriesNode115_2 : (data.drop 115).take 2 = (originalEntries.drop 115).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 115 1 1 116 2 rfl rfl row115_binding row116_binding

theorem entriesNode117_2 : (data.drop 117).take 2 = (originalEntries.drop 117).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 117 1 1 118 2 rfl rfl row117_binding row118_binding

theorem entriesNode115_4 : (data.drop 115).take 4 = (originalEntries.drop 115).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 115 2 2 117 4 rfl rfl entriesNode115_2 entriesNode117_2

theorem entriesNode119_2 : (data.drop 119).take 2 = (originalEntries.drop 119).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 119 1 1 120 2 rfl rfl row119_binding row120_binding

theorem entriesNode121_2 : (data.drop 121).take 2 = (originalEntries.drop 121).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 121 1 1 122 2 rfl rfl row121_binding row122_binding

theorem entriesNode119_4 : (data.drop 119).take 4 = (originalEntries.drop 119).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 119 2 2 121 4 rfl rfl entriesNode119_2 entriesNode121_2

theorem entriesNode115_8 : (data.drop 115).take 8 = (originalEntries.drop 115).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 115 4 4 119 8 rfl rfl entriesNode115_4 entriesNode119_4

theorem entriesNode107_16 : (data.drop 107).take 16 = (originalEntries.drop 107).take 16 :=
  NumericWorkerPortChecks.merge_at data originalEntries 107 8 8 115 16 rfl rfl entriesNode107_8 entriesNode115_8

theorem entriesNode92_31 : (data.drop 92).take 31 = (originalEntries.drop 92).take 31 :=
  NumericWorkerPortChecks.merge_at data originalEntries 92 15 16 107 31 rfl rfl entriesNode92_15 entriesNode107_16

theorem entriesNode61_62 : (data.drop 61).take 62 = (originalEntries.drop 61).take 62 :=
  NumericWorkerPortChecks.merge_at data originalEntries 61 31 31 92 62 rfl rfl entriesNode61_31 entriesNode92_31

theorem entriesNode0_123 : (data.drop 0).take 123 = (originalEntries.drop 0).take 123 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 61 62 61 123 rfl rfl entriesNode0_61 entriesNode61_62

theorem source_binding : data = originalEntries :=
  NumericQueryFrameChecks.complete_binding data originalEntries 123
    (by decide +kernel) (by decide +kernel) entriesNode0_123

end Airbender.Compiler.MemoryPayloadChecks.BigintCached
