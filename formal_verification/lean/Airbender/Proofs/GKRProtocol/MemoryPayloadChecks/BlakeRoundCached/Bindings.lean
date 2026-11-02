import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.BlakeRoundCached.Data
import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.BlakeRoundCached.ProjectionBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.MemoryPayloadChecks.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

attribute [local irreducible] originalEntries data

numeric_data_binding row0_view : (data.drop 0).take 1 = [projectionData]

theorem row0_source : [projectionData] = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing Airbender.Compiler.MemoryNative.BlakeRoundCached.native.projectionInputs)] :=
  congrArg List.singleton projection_source_binding

numeric_data_binding row0_entry : (originalEntries.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing Airbender.Compiler.MemoryNative.BlakeRoundCached.native.projectionInputs)]

theorem row0_binding : (data.drop 0).take 1 = (originalEntries.drop 0).take 1 :=
  row0_view.trans (row0_source.trans row0_entry.symm)

numeric_data_binding row1_view : (data.drop 1).take 1 = (data1.drop 0).take 1

numeric_data_binding row1_source : (data1.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [0] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf0).isSome))]

numeric_data_binding row1_entry : (originalEntries.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [0] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf0).isSome))]

theorem row1_binding : (data.drop 1).take 1 = (originalEntries.drop 1).take 1 :=
  row1_view.trans (row1_source.trans row1_entry.symm)

numeric_data_binding row2_view : (data.drop 2).take 1 = (data1.drop 1).take 1

numeric_data_binding row2_source : (data1.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw0).inputs)]

numeric_data_binding row2_entry : (originalEntries.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw0).inputs)]

theorem row2_binding : (data.drop 2).take 1 = (originalEntries.drop 2).take 1 :=
  row2_view.trans (row2_source.trans row2_entry.symm)

numeric_data_binding row3_view : (data.drop 3).take 1 = (data1.drop 2).take 1

numeric_data_binding row3_source : (data1.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [1] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf1).isSome))]

numeric_data_binding row3_entry : (originalEntries.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [1] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf1).isSome))]

theorem row3_binding : (data.drop 3).take 1 = (originalEntries.drop 3).take 1 :=
  row3_view.trans (row3_source.trans row3_entry.symm)

numeric_data_binding row4_view : (data.drop 4).take 1 = (data1.drop 3).take 1

numeric_data_binding row4_source : (data1.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw1).inputs)]

numeric_data_binding row4_entry : (originalEntries.drop 4).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw1).inputs)]

theorem row4_binding : (data.drop 4).take 1 = (originalEntries.drop 4).take 1 :=
  row4_view.trans (row4_source.trans row4_entry.symm)

numeric_data_binding row5_view : (data.drop 5).take 1 = (data5.drop 0).take 1

numeric_data_binding row5_source : (data5.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [2] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf2).isSome))]

numeric_data_binding row5_entry : (originalEntries.drop 5).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [2] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf2).isSome))]

theorem row5_binding : (data.drop 5).take 1 = (originalEntries.drop 5).take 1 :=
  row5_view.trans (row5_source.trans row5_entry.symm)

numeric_data_binding row6_view : (data.drop 6).take 1 = (data5.drop 1).take 1

numeric_data_binding row6_source : (data5.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw2).inputs)]

numeric_data_binding row6_entry : (originalEntries.drop 6).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw2).inputs)]

theorem row6_binding : (data.drop 6).take 1 = (originalEntries.drop 6).take 1 :=
  row6_view.trans (row6_source.trans row6_entry.symm)

numeric_data_binding row7_view : (data.drop 7).take 1 = (data5.drop 2).take 1

numeric_data_binding row7_source : (data5.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [3] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf3).isSome))]

numeric_data_binding row7_entry : (originalEntries.drop 7).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [3] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf3).isSome))]

theorem row7_binding : (data.drop 7).take 1 = (originalEntries.drop 7).take 1 :=
  row7_view.trans (row7_source.trans row7_entry.symm)

numeric_data_binding row8_view : (data.drop 8).take 1 = (data5.drop 3).take 1

numeric_data_binding row8_source : (data5.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw3).inputs)]

numeric_data_binding row8_entry : (originalEntries.drop 8).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw3).inputs)]

theorem row8_binding : (data.drop 8).take 1 = (originalEntries.drop 8).take 1 :=
  row8_view.trans (row8_source.trans row8_entry.symm)

numeric_data_binding row9_view : (data.drop 9).take 1 = (data9.drop 0).take 1

numeric_data_binding row9_source : (data9.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [4] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf4).isSome))]

numeric_data_binding row9_entry : (originalEntries.drop 9).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [4] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf4).isSome))]

theorem row9_binding : (data.drop 9).take 1 = (originalEntries.drop 9).take 1 :=
  row9_view.trans (row9_source.trans row9_entry.symm)

numeric_data_binding row10_view : (data.drop 10).take 1 = (data9.drop 1).take 1

numeric_data_binding row10_source : (data9.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw4).inputs)]

numeric_data_binding row10_entry : (originalEntries.drop 10).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw4).inputs)]

theorem row10_binding : (data.drop 10).take 1 = (originalEntries.drop 10).take 1 :=
  row10_view.trans (row10_source.trans row10_entry.symm)

numeric_data_binding row11_view : (data.drop 11).take 1 = (data9.drop 2).take 1

numeric_data_binding row11_source : (data9.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [5] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf5).isSome))]

numeric_data_binding row11_entry : (originalEntries.drop 11).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [5] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf5).isSome))]

theorem row11_binding : (data.drop 11).take 1 = (originalEntries.drop 11).take 1 :=
  row11_view.trans (row11_source.trans row11_entry.symm)

numeric_data_binding row12_view : (data.drop 12).take 1 = (data9.drop 3).take 1

numeric_data_binding row12_source : (data9.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw5).inputs)]

numeric_data_binding row12_entry : (originalEntries.drop 12).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw5).inputs)]

theorem row12_binding : (data.drop 12).take 1 = (originalEntries.drop 12).take 1 :=
  row12_view.trans (row12_source.trans row12_entry.symm)

numeric_data_binding row13_view : (data.drop 13).take 1 = (data13.drop 0).take 1

numeric_data_binding row13_source : (data13.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [6] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf6).isSome))]

numeric_data_binding row13_entry : (originalEntries.drop 13).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [6] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf6).isSome))]

theorem row13_binding : (data.drop 13).take 1 = (originalEntries.drop 13).take 1 :=
  row13_view.trans (row13_source.trans row13_entry.symm)

numeric_data_binding row14_view : (data.drop 14).take 1 = (data13.drop 1).take 1

numeric_data_binding row14_source : (data13.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw6).inputs)]

numeric_data_binding row14_entry : (originalEntries.drop 14).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw6).inputs)]

theorem row14_binding : (data.drop 14).take 1 = (originalEntries.drop 14).take 1 :=
  row14_view.trans (row14_source.trans row14_entry.symm)

numeric_data_binding row15_view : (data.drop 15).take 1 = (data13.drop 2).take 1

numeric_data_binding row15_source : (data13.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [7] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf7).isSome))]

numeric_data_binding row15_entry : (originalEntries.drop 15).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [7] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf7).isSome))]

theorem row15_binding : (data.drop 15).take 1 = (originalEntries.drop 15).take 1 :=
  row15_view.trans (row15_source.trans row15_entry.symm)

numeric_data_binding row16_view : (data.drop 16).take 1 = (data13.drop 3).take 1

numeric_data_binding row16_source : (data13.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw7).inputs)]

numeric_data_binding row16_entry : (originalEntries.drop 16).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw7).inputs)]

theorem row16_binding : (data.drop 16).take 1 = (originalEntries.drop 16).take 1 :=
  row16_view.trans (row16_source.trans row16_entry.symm)

numeric_data_binding row17_view : (data.drop 17).take 1 = (data17.drop 0).take 1

numeric_data_binding row17_source : (data17.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [8] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf8).isSome))]

numeric_data_binding row17_entry : (originalEntries.drop 17).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [8] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf8).isSome))]

theorem row17_binding : (data.drop 17).take 1 = (originalEntries.drop 17).take 1 :=
  row17_view.trans (row17_source.trans row17_entry.symm)

numeric_data_binding row18_view : (data.drop 18).take 1 = (data17.drop 1).take 1

numeric_data_binding row18_source : (data17.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw8).inputs)]

numeric_data_binding row18_entry : (originalEntries.drop 18).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw8).inputs)]

theorem row18_binding : (data.drop 18).take 1 = (originalEntries.drop 18).take 1 :=
  row18_view.trans (row18_source.trans row18_entry.symm)

numeric_data_binding row19_view : (data.drop 19).take 1 = (data17.drop 2).take 1

numeric_data_binding row19_source : (data17.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [9] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf9).isSome))]

numeric_data_binding row19_entry : (originalEntries.drop 19).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [9] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf9).isSome))]

theorem row19_binding : (data.drop 19).take 1 = (originalEntries.drop 19).take 1 :=
  row19_view.trans (row19_source.trans row19_entry.symm)

numeric_data_binding row20_view : (data.drop 20).take 1 = (data17.drop 3).take 1

numeric_data_binding row20_source : (data17.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw9).inputs)]

numeric_data_binding row20_entry : (originalEntries.drop 20).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw9).inputs)]

theorem row20_binding : (data.drop 20).take 1 = (originalEntries.drop 20).take 1 :=
  row20_view.trans (row20_source.trans row20_entry.symm)

numeric_data_binding row21_view : (data.drop 21).take 1 = (data21.drop 0).take 1

numeric_data_binding row21_source : (data21.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [10] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf10).isSome))]

numeric_data_binding row21_entry : (originalEntries.drop 21).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [10] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf10).isSome))]

theorem row21_binding : (data.drop 21).take 1 = (originalEntries.drop 21).take 1 :=
  row21_view.trans (row21_source.trans row21_entry.symm)

numeric_data_binding row22_view : (data.drop 22).take 1 = (data21.drop 1).take 1

numeric_data_binding row22_source : (data21.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw10).inputs)]

numeric_data_binding row22_entry : (originalEntries.drop 22).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw10).inputs)]

theorem row22_binding : (data.drop 22).take 1 = (originalEntries.drop 22).take 1 :=
  row22_view.trans (row22_source.trans row22_entry.symm)

numeric_data_binding row23_view : (data.drop 23).take 1 = (data21.drop 2).take 1

numeric_data_binding row23_source : (data21.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [11] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf11).isSome))]

numeric_data_binding row23_entry : (originalEntries.drop 23).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [11] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf11).isSome))]

theorem row23_binding : (data.drop 23).take 1 = (originalEntries.drop 23).take 1 :=
  row23_view.trans (row23_source.trans row23_entry.symm)

numeric_data_binding row24_view : (data.drop 24).take 1 = (data21.drop 3).take 1

numeric_data_binding row24_source : (data21.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw11).inputs)]

numeric_data_binding row24_entry : (originalEntries.drop 24).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw11).inputs)]

theorem row24_binding : (data.drop 24).take 1 = (originalEntries.drop 24).take 1 :=
  row24_view.trans (row24_source.trans row24_entry.symm)

numeric_data_binding row25_view : (data.drop 25).take 1 = (data25.drop 0).take 1

numeric_data_binding row25_source : (data25.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [12] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf12).isSome))]

numeric_data_binding row25_entry : (originalEntries.drop 25).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [12] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf12).isSome))]

theorem row25_binding : (data.drop 25).take 1 = (originalEntries.drop 25).take 1 :=
  row25_view.trans (row25_source.trans row25_entry.symm)

numeric_data_binding row26_view : (data.drop 26).take 1 = (data25.drop 1).take 1

numeric_data_binding row26_source : (data25.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw12).inputs)]

numeric_data_binding row26_entry : (originalEntries.drop 26).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw12).inputs)]

theorem row26_binding : (data.drop 26).take 1 = (originalEntries.drop 26).take 1 :=
  row26_view.trans (row26_source.trans row26_entry.symm)

numeric_data_binding row27_view : (data.drop 27).take 1 = (data25.drop 2).take 1

numeric_data_binding row27_source : (data25.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [13] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf13).isSome))]

numeric_data_binding row27_entry : (originalEntries.drop 27).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [13] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf13).isSome))]

theorem row27_binding : (data.drop 27).take 1 = (originalEntries.drop 27).take 1 :=
  row27_view.trans (row27_source.trans row27_entry.symm)

numeric_data_binding row28_view : (data.drop 28).take 1 = (data25.drop 3).take 1

numeric_data_binding row28_source : (data25.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw13).inputs)]

numeric_data_binding row28_entry : (originalEntries.drop 28).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw13).inputs)]

theorem row28_binding : (data.drop 28).take 1 = (originalEntries.drop 28).take 1 :=
  row28_view.trans (row28_source.trans row28_entry.symm)

numeric_data_binding row29_view : (data.drop 29).take 1 = (data29.drop 0).take 1

numeric_data_binding row29_source : (data29.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [14] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf14).isSome))]

numeric_data_binding row29_entry : (originalEntries.drop 29).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [14] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf14).isSome))]

theorem row29_binding : (data.drop 29).take 1 = (originalEntries.drop 29).take 1 :=
  row29_view.trans (row29_source.trans row29_entry.symm)

numeric_data_binding row30_view : (data.drop 30).take 1 = (data29.drop 1).take 1

numeric_data_binding row30_source : (data29.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw14).inputs)]

numeric_data_binding row30_entry : (originalEntries.drop 30).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw14).inputs)]

theorem row30_binding : (data.drop 30).take 1 = (originalEntries.drop 30).take 1 :=
  row30_view.trans (row30_source.trans row30_entry.symm)

numeric_data_binding row31_view : (data.drop 31).take 1 = (data29.drop 2).take 1

numeric_data_binding row31_source : (data29.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [15] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf15).isSome))]

numeric_data_binding row31_entry : (originalEntries.drop 31).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [15] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf15).isSome))]

theorem row31_binding : (data.drop 31).take 1 = (originalEntries.drop 31).take 1 :=
  row31_view.trans (row31_source.trans row31_entry.symm)

numeric_data_binding row32_view : (data.drop 32).take 1 = (data29.drop 3).take 1

numeric_data_binding row32_source : (data29.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw15).inputs)]

numeric_data_binding row32_entry : (originalEntries.drop 32).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw15).inputs)]

theorem row32_binding : (data.drop 32).take 1 = (originalEntries.drop 32).take 1 :=
  row32_view.trans (row32_source.trans row32_entry.symm)

numeric_data_binding row33_view : (data.drop 33).take 1 = (data33.drop 0).take 1

numeric_data_binding row33_source : (data33.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [16] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf16).isSome))]

numeric_data_binding row33_entry : (originalEntries.drop 33).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [16] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf16).isSome))]

theorem row33_binding : (data.drop 33).take 1 = (originalEntries.drop 33).take 1 :=
  row33_view.trans (row33_source.trans row33_entry.symm)

numeric_data_binding row34_view : (data.drop 34).take 1 = (data33.drop 1).take 1

numeric_data_binding row34_source : (data33.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw16).inputs)]

numeric_data_binding row34_entry : (originalEntries.drop 34).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw16).inputs)]

theorem row34_binding : (data.drop 34).take 1 = (originalEntries.drop 34).take 1 :=
  row34_view.trans (row34_source.trans row34_entry.symm)

numeric_data_binding row35_view : (data.drop 35).take 1 = (data33.drop 2).take 1

numeric_data_binding row35_source : (data33.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [17] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf17).isSome))]

numeric_data_binding row35_entry : (originalEntries.drop 35).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [17] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf17).isSome))]

theorem row35_binding : (data.drop 35).take 1 = (originalEntries.drop 35).take 1 :=
  row35_view.trans (row35_source.trans row35_entry.symm)

numeric_data_binding row36_view : (data.drop 36).take 1 = (data33.drop 3).take 1

numeric_data_binding row36_source : (data33.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw17).inputs)]

numeric_data_binding row36_entry : (originalEntries.drop 36).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw17).inputs)]

theorem row36_binding : (data.drop 36).take 1 = (originalEntries.drop 36).take 1 :=
  row36_view.trans (row36_source.trans row36_entry.symm)

numeric_data_binding row37_view : (data.drop 37).take 1 = (data37.drop 0).take 1

numeric_data_binding row37_source : (data37.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [18] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf18).isSome))]

numeric_data_binding row37_entry : (originalEntries.drop 37).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [18] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf18).isSome))]

theorem row37_binding : (data.drop 37).take 1 = (originalEntries.drop 37).take 1 :=
  row37_view.trans (row37_source.trans row37_entry.symm)

numeric_data_binding row38_view : (data.drop 38).take 1 = (data37.drop 1).take 1

numeric_data_binding row38_source : (data37.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw18).inputs)]

numeric_data_binding row38_entry : (originalEntries.drop 38).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw18).inputs)]

theorem row38_binding : (data.drop 38).take 1 = (originalEntries.drop 38).take 1 :=
  row38_view.trans (row38_source.trans row38_entry.symm)

numeric_data_binding row39_view : (data.drop 39).take 1 = (data37.drop 2).take 1

numeric_data_binding row39_source : (data37.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [19] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf19).isSome))]

numeric_data_binding row39_entry : (originalEntries.drop 39).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [19] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf19).isSome))]

theorem row39_binding : (data.drop 39).take 1 = (originalEntries.drop 39).take 1 :=
  row39_view.trans (row39_source.trans row39_entry.symm)

numeric_data_binding row40_view : (data.drop 40).take 1 = (data37.drop 3).take 1

numeric_data_binding row40_source : (data37.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw19).inputs)]

numeric_data_binding row40_entry : (originalEntries.drop 40).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw19).inputs)]

theorem row40_binding : (data.drop 40).take 1 = (originalEntries.drop 40).take 1 :=
  row40_view.trans (row40_source.trans row40_entry.symm)

numeric_data_binding row41_view : (data.drop 41).take 1 = (data41.drop 0).take 1

numeric_data_binding row41_source : (data41.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [20] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf20).isSome))]

numeric_data_binding row41_entry : (originalEntries.drop 41).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [20] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf20).isSome))]

theorem row41_binding : (data.drop 41).take 1 = (originalEntries.drop 41).take 1 :=
  row41_view.trans (row41_source.trans row41_entry.symm)

numeric_data_binding row42_view : (data.drop 42).take 1 = (data41.drop 1).take 1

numeric_data_binding row42_source : (data41.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw20).inputs)]

numeric_data_binding row42_entry : (originalEntries.drop 42).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw20).inputs)]

theorem row42_binding : (data.drop 42).take 1 = (originalEntries.drop 42).take 1 :=
  row42_view.trans (row42_source.trans row42_entry.symm)

numeric_data_binding row43_view : (data.drop 43).take 1 = (data41.drop 2).take 1

numeric_data_binding row43_source : (data41.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [21] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf21).isSome))]

numeric_data_binding row43_entry : (originalEntries.drop 43).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [21] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf21).isSome))]

theorem row43_binding : (data.drop 43).take 1 = (originalEntries.drop 43).take 1 :=
  row43_view.trans (row43_source.trans row43_entry.symm)

numeric_data_binding row44_view : (data.drop 44).take 1 = (data41.drop 3).take 1

numeric_data_binding row44_source : (data41.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw21).inputs)]

numeric_data_binding row44_entry : (originalEntries.drop 44).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw21).inputs)]

theorem row44_binding : (data.drop 44).take 1 = (originalEntries.drop 44).take 1 :=
  row44_view.trans (row44_source.trans row44_entry.symm)

numeric_data_binding row45_view : (data.drop 45).take 1 = (data45.drop 0).take 1

numeric_data_binding row45_source : (data45.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [22] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf22).isSome))]

numeric_data_binding row45_entry : (originalEntries.drop 45).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [22] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf22).isSome))]

theorem row45_binding : (data.drop 45).take 1 = (originalEntries.drop 45).take 1 :=
  row45_view.trans (row45_source.trans row45_entry.symm)

numeric_data_binding row46_view : (data.drop 46).take 1 = (data45.drop 1).take 1

numeric_data_binding row46_source : (data45.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw22).inputs)]

numeric_data_binding row46_entry : (originalEntries.drop 46).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw22).inputs)]

theorem row46_binding : (data.drop 46).take 1 = (originalEntries.drop 46).take 1 :=
  row46_view.trans (row46_source.trans row46_entry.symm)

numeric_data_binding row47_view : (data.drop 47).take 1 = (data45.drop 2).take 1

numeric_data_binding row47_source : (data45.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [23] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf23).isSome))]

numeric_data_binding row47_entry : (originalEntries.drop 47).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [23] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf23).isSome))]

theorem row47_binding : (data.drop 47).take 1 = (originalEntries.drop 47).take 1 :=
  row47_view.trans (row47_source.trans row47_entry.symm)

numeric_data_binding row48_view : (data.drop 48).take 1 = (data45.drop 3).take 1

numeric_data_binding row48_source : (data45.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw23).inputs)]

numeric_data_binding row48_entry : (originalEntries.drop 48).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw23).inputs)]

theorem row48_binding : (data.drop 48).take 1 = (originalEntries.drop 48).take 1 :=
  row48_view.trans (row48_source.trans row48_entry.symm)

numeric_data_binding row49_view : (data.drop 49).take 1 = (data49.drop 0).take 1

numeric_data_binding row49_source : (data49.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [24] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf24).isSome))]

numeric_data_binding row49_entry : (originalEntries.drop 49).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [24] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf24).isSome))]

theorem row49_binding : (data.drop 49).take 1 = (originalEntries.drop 49).take 1 :=
  row49_view.trans (row49_source.trans row49_entry.symm)

numeric_data_binding row50_view : (data.drop 50).take 1 = (data49.drop 1).take 1

numeric_data_binding row50_source : (data49.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw24).inputs)]

numeric_data_binding row50_entry : (originalEntries.drop 50).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw24).inputs)]

theorem row50_binding : (data.drop 50).take 1 = (originalEntries.drop 50).take 1 :=
  row50_view.trans (row50_source.trans row50_entry.symm)

numeric_data_binding row51_view : (data.drop 51).take 1 = (data49.drop 2).take 1

numeric_data_binding row51_source : (data49.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [25] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf25).isSome))]

numeric_data_binding row51_entry : (originalEntries.drop 51).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [25] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf25).isSome))]

theorem row51_binding : (data.drop 51).take 1 = (originalEntries.drop 51).take 1 :=
  row51_view.trans (row51_source.trans row51_entry.symm)

numeric_data_binding row52_view : (data.drop 52).take 1 = (data49.drop 3).take 1

numeric_data_binding row52_source : (data49.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw25).inputs)]

numeric_data_binding row52_entry : (originalEntries.drop 52).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw25).inputs)]

theorem row52_binding : (data.drop 52).take 1 = (originalEntries.drop 52).take 1 :=
  row52_view.trans (row52_source.trans row52_entry.symm)

numeric_data_binding row53_view : (data.drop 53).take 1 = (data53.drop 0).take 1

numeric_data_binding row53_source : (data53.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [26] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf26).isSome))]

numeric_data_binding row53_entry : (originalEntries.drop 53).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [26] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf26).isSome))]

theorem row53_binding : (data.drop 53).take 1 = (originalEntries.drop 53).take 1 :=
  row53_view.trans (row53_source.trans row53_entry.symm)

numeric_data_binding row54_view : (data.drop 54).take 1 = (data53.drop 1).take 1

numeric_data_binding row54_source : (data53.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw26).inputs)]

numeric_data_binding row54_entry : (originalEntries.drop 54).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw26).inputs)]

theorem row54_binding : (data.drop 54).take 1 = (originalEntries.drop 54).take 1 :=
  row54_view.trans (row54_source.trans row54_entry.symm)

numeric_data_binding row55_view : (data.drop 55).take 1 = (data53.drop 2).take 1

numeric_data_binding row55_source : (data53.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [27] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf27).isSome))]

numeric_data_binding row55_entry : (originalEntries.drop 55).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [27] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf27).isSome))]

theorem row55_binding : (data.drop 55).take 1 = (originalEntries.drop 55).take 1 :=
  row55_view.trans (row55_source.trans row55_entry.symm)

numeric_data_binding row56_view : (data.drop 56).take 1 = (data53.drop 3).take 1

numeric_data_binding row56_source : (data53.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw27).inputs)]

numeric_data_binding row56_entry : (originalEntries.drop 56).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw27).inputs)]

theorem row56_binding : (data.drop 56).take 1 = (originalEntries.drop 56).take 1 :=
  row56_view.trans (row56_source.trans row56_entry.symm)

numeric_data_binding row57_view : (data.drop 57).take 1 = (data57.drop 0).take 1

numeric_data_binding row57_source : (data57.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [28] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf28).isSome))]

numeric_data_binding row57_entry : (originalEntries.drop 57).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [28] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf28).isSome))]

theorem row57_binding : (data.drop 57).take 1 = (originalEntries.drop 57).take 1 :=
  row57_view.trans (row57_source.trans row57_entry.symm)

numeric_data_binding row58_view : (data.drop 58).take 1 = (data57.drop 1).take 1

numeric_data_binding row58_source : (data57.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw28).inputs)]

numeric_data_binding row58_entry : (originalEntries.drop 58).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw28).inputs)]

theorem row58_binding : (data.drop 58).take 1 = (originalEntries.drop 58).take 1 :=
  row58_view.trans (row58_source.trans row58_entry.symm)

numeric_data_binding row59_view : (data.drop 59).take 1 = (data57.drop 2).take 1

numeric_data_binding row59_source : (data57.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [29] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf29).isSome))]

numeric_data_binding row59_entry : (originalEntries.drop 59).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [29] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf29).isSome))]

theorem row59_binding : (data.drop 59).take 1 = (originalEntries.drop 59).take 1 :=
  row59_view.trans (row59_source.trans row59_entry.symm)

numeric_data_binding row60_view : (data.drop 60).take 1 = (data57.drop 3).take 1

numeric_data_binding row60_source : (data57.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw29).inputs)]

numeric_data_binding row60_entry : (originalEntries.drop 60).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw29).inputs)]

theorem row60_binding : (data.drop 60).take 1 = (originalEntries.drop 60).take 1 :=
  row60_view.trans (row60_source.trans row60_entry.symm)

numeric_data_binding row61_view : (data.drop 61).take 1 = (data61.drop 0).take 1

numeric_data_binding row61_source : (data61.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [30] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf30).isSome))]

numeric_data_binding row61_entry : (originalEntries.drop 61).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [30] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf30).isSome))]

theorem row61_binding : (data.drop 61).take 1 = (originalEntries.drop 61).take 1 :=
  row61_view.trans (row61_source.trans row61_entry.symm)

numeric_data_binding row62_view : (data.drop 62).take 1 = (data61.drop 1).take 1

numeric_data_binding row62_source : (data61.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw30).inputs)]

numeric_data_binding row62_entry : (originalEntries.drop 62).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw30).inputs)]

theorem row62_binding : (data.drop 62).take 1 = (originalEntries.drop 62).take 1 :=
  row62_view.trans (row62_source.trans row62_entry.symm)

numeric_data_binding row63_view : (data.drop 63).take 1 = (data61.drop 2).take 1

numeric_data_binding row63_source : (data61.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [31] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf31).isSome))]

numeric_data_binding row63_entry : (originalEntries.drop 63).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [31] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf31).isSome))]

theorem row63_binding : (data.drop 63).take 1 = (originalEntries.drop 63).take 1 :=
  row63_view.trans (row63_source.trans row63_entry.symm)

numeric_data_binding row64_view : (data.drop 64).take 1 = (data61.drop 3).take 1

numeric_data_binding row64_source : (data61.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw31).inputs)]

numeric_data_binding row64_entry : (originalEntries.drop 64).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw31).inputs)]

theorem row64_binding : (data.drop 64).take 1 = (originalEntries.drop 64).take 1 :=
  row64_view.trans (row64_source.trans row64_entry.symm)

numeric_data_binding row65_view : (data.drop 65).take 1 = (data65.drop 0).take 1

numeric_data_binding row65_source : (data65.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [32] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf32).isSome))]

numeric_data_binding row65_entry : (originalEntries.drop 65).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [32] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf32).isSome))]

theorem row65_binding : (data.drop 65).take 1 = (originalEntries.drop 65).take 1 :=
  row65_view.trans (row65_source.trans row65_entry.symm)

numeric_data_binding row66_view : (data.drop 66).take 1 = (data65.drop 1).take 1

numeric_data_binding row66_source : (data65.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw32).inputs)]

numeric_data_binding row66_entry : (originalEntries.drop 66).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw32).inputs)]

theorem row66_binding : (data.drop 66).take 1 = (originalEntries.drop 66).take 1 :=
  row66_view.trans (row66_source.trans row66_entry.symm)

numeric_data_binding row67_view : (data.drop 67).take 1 = (data65.drop 2).take 1

numeric_data_binding row67_source : (data65.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [33] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf33).isSome))]

numeric_data_binding row67_entry : (originalEntries.drop 67).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [33] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf33).isSome))]

theorem row67_binding : (data.drop 67).take 1 = (originalEntries.drop 67).take 1 :=
  row67_view.trans (row67_source.trans row67_entry.symm)

numeric_data_binding row68_view : (data.drop 68).take 1 = (data65.drop 3).take 1

numeric_data_binding row68_source : (data65.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw33).inputs)]

numeric_data_binding row68_entry : (originalEntries.drop 68).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw33).inputs)]

theorem row68_binding : (data.drop 68).take 1 = (originalEntries.drop 68).take 1 :=
  row68_view.trans (row68_source.trans row68_entry.symm)

numeric_data_binding row69_view : (data.drop 69).take 1 = (data69.drop 0).take 1

numeric_data_binding row69_source : (data69.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [34] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf34).isSome))]

numeric_data_binding row69_entry : (originalEntries.drop 69).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [34] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf34).isSome))]

theorem row69_binding : (data.drop 69).take 1 = (originalEntries.drop 69).take 1 :=
  row69_view.trans (row69_source.trans row69_entry.symm)

numeric_data_binding row70_view : (data.drop 70).take 1 = (data69.drop 1).take 1

numeric_data_binding row70_source : (data69.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw34).inputs)]

numeric_data_binding row70_entry : (originalEntries.drop 70).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw34).inputs)]

theorem row70_binding : (data.drop 70).take 1 = (originalEntries.drop 70).take 1 :=
  row70_view.trans (row70_source.trans row70_entry.symm)

numeric_data_binding row71_view : (data.drop 71).take 1 = (data69.drop 2).take 1

numeric_data_binding row71_source : (data69.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [35] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf35).isSome))]

numeric_data_binding row71_entry : (originalEntries.drop 71).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [35] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf35).isSome))]

theorem row71_binding : (data.drop 71).take 1 = (originalEntries.drop 71).take 1 :=
  row71_view.trans (row71_source.trans row71_entry.symm)

numeric_data_binding row72_view : (data.drop 72).take 1 = (data69.drop 3).take 1

numeric_data_binding row72_source : (data69.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw35).inputs)]

numeric_data_binding row72_entry : (originalEntries.drop 72).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw35).inputs)]

theorem row72_binding : (data.drop 72).take 1 = (originalEntries.drop 72).take 1 :=
  row72_view.trans (row72_source.trans row72_entry.symm)

numeric_data_binding row73_view : (data.drop 73).take 1 = (data73.drop 0).take 1

numeric_data_binding row73_source : (data73.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [36] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf36).isSome))]

numeric_data_binding row73_entry : (originalEntries.drop 73).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [36] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf36).isSome))]

theorem row73_binding : (data.drop 73).take 1 = (originalEntries.drop 73).take 1 :=
  row73_view.trans (row73_source.trans row73_entry.symm)

numeric_data_binding row74_view : (data.drop 74).take 1 = (data73.drop 1).take 1

numeric_data_binding row74_source : (data73.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw36).inputs)]

numeric_data_binding row74_entry : (originalEntries.drop 74).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw36).inputs)]

theorem row74_binding : (data.drop 74).take 1 = (originalEntries.drop 74).take 1 :=
  row74_view.trans (row74_source.trans row74_entry.symm)

numeric_data_binding row75_view : (data.drop 75).take 1 = (data73.drop 2).take 1

numeric_data_binding row75_source : (data73.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [37] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf37).isSome))]

numeric_data_binding row75_entry : (originalEntries.drop 75).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [37] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf37).isSome))]

theorem row75_binding : (data.drop 75).take 1 = (originalEntries.drop 75).take 1 :=
  row75_view.trans (row75_source.trans row75_entry.symm)

numeric_data_binding row76_view : (data.drop 76).take 1 = (data73.drop 3).take 1

numeric_data_binding row76_source : (data73.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw37).inputs)]

numeric_data_binding row76_entry : (originalEntries.drop 76).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw37).inputs)]

theorem row76_binding : (data.drop 76).take 1 = (originalEntries.drop 76).take 1 :=
  row76_view.trans (row76_source.trans row76_entry.symm)

numeric_data_binding row77_view : (data.drop 77).take 1 = (data77.drop 0).take 1

numeric_data_binding row77_source : (data77.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [38] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf38).isSome))]

numeric_data_binding row77_entry : (originalEntries.drop 77).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [38] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf38).isSome))]

theorem row77_binding : (data.drop 77).take 1 = (originalEntries.drop 77).take 1 :=
  row77_view.trans (row77_source.trans row77_entry.symm)

numeric_data_binding row78_view : (data.drop 78).take 1 = (data77.drop 1).take 1

numeric_data_binding row78_source : (data77.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw38).inputs)]

numeric_data_binding row78_entry : (originalEntries.drop 78).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw38).inputs)]

theorem row78_binding : (data.drop 78).take 1 = (originalEntries.drop 78).take 1 :=
  row78_view.trans (row78_source.trans row78_entry.symm)

numeric_data_binding row79_view : (data.drop 79).take 1 = (data77.drop 2).take 1

numeric_data_binding row79_source : (data77.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [39] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf39).isSome))]

numeric_data_binding row79_entry : (originalEntries.drop 79).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [39] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf39).isSome))]

theorem row79_binding : (data.drop 79).take 1 = (originalEntries.drop 79).take 1 :=
  row79_view.trans (row79_source.trans row79_entry.symm)

numeric_data_binding row80_view : (data.drop 80).take 1 = (data77.drop 3).take 1

numeric_data_binding row80_source : (data77.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw39).inputs)]

numeric_data_binding row80_entry : (originalEntries.drop 80).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw39).inputs)]

theorem row80_binding : (data.drop 80).take 1 = (originalEntries.drop 80).take 1 :=
  row80_view.trans (row80_source.trans row80_entry.symm)

numeric_data_binding row81_view : (data.drop 81).take 1 = (data81.drop 0).take 1

numeric_data_binding row81_source : (data81.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [40] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf40).isSome))]

numeric_data_binding row81_entry : (originalEntries.drop 81).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [40] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf40).isSome))]

theorem row81_binding : (data.drop 81).take 1 = (originalEntries.drop 81).take 1 :=
  row81_view.trans (row81_source.trans row81_entry.symm)

numeric_data_binding row82_view : (data.drop 82).take 1 = (data81.drop 1).take 1

numeric_data_binding row82_source : (data81.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw40).inputs)]

numeric_data_binding row82_entry : (originalEntries.drop 82).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw40).inputs)]

theorem row82_binding : (data.drop 82).take 1 = (originalEntries.drop 82).take 1 :=
  row82_view.trans (row82_source.trans row82_entry.symm)

numeric_data_binding row83_view : (data.drop 83).take 1 = (data81.drop 2).take 1

numeric_data_binding row83_source : (data81.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [41] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf41).isSome))]

numeric_data_binding row83_entry : (originalEntries.drop 83).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [41] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf41).isSome))]

theorem row83_binding : (data.drop 83).take 1 = (originalEntries.drop 83).take 1 :=
  row83_view.trans (row83_source.trans row83_entry.symm)

numeric_data_binding row84_view : (data.drop 84).take 1 = (data81.drop 3).take 1

numeric_data_binding row84_source : (data81.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw41).inputs)]

numeric_data_binding row84_entry : (originalEntries.drop 84).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw41).inputs)]

theorem row84_binding : (data.drop 84).take 1 = (originalEntries.drop 84).take 1 :=
  row84_view.trans (row84_source.trans row84_entry.symm)

numeric_data_binding row85_view : (data.drop 85).take 1 = (data85.drop 0).take 1

numeric_data_binding row85_source : (data85.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [42] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf42).isSome))]

numeric_data_binding row85_entry : (originalEntries.drop 85).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [42] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf42).isSome))]

theorem row85_binding : (data.drop 85).take 1 = (originalEntries.drop 85).take 1 :=
  row85_view.trans (row85_source.trans row85_entry.symm)

numeric_data_binding row86_view : (data.drop 86).take 1 = (data85.drop 1).take 1

numeric_data_binding row86_source : (data85.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw42).inputs)]

numeric_data_binding row86_entry : (originalEntries.drop 86).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw42).inputs)]

theorem row86_binding : (data.drop 86).take 1 = (originalEntries.drop 86).take 1 :=
  row86_view.trans (row86_source.trans row86_entry.symm)

numeric_data_binding row87_view : (data.drop 87).take 1 = (data85.drop 2).take 1

numeric_data_binding row87_source : (data85.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [43] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf43).isSome))]

numeric_data_binding row87_entry : (originalEntries.drop 87).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [43] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf43).isSome))]

theorem row87_binding : (data.drop 87).take 1 = (originalEntries.drop 87).take 1 :=
  row87_view.trans (row87_source.trans row87_entry.symm)

numeric_data_binding row88_view : (data.drop 88).take 1 = (data85.drop 3).take 1

numeric_data_binding row88_source : (data85.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw43).inputs)]

numeric_data_binding row88_entry : (originalEntries.drop 88).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw43).inputs)]

theorem row88_binding : (data.drop 88).take 1 = (originalEntries.drop 88).take 1 :=
  row88_view.trans (row88_source.trans row88_entry.symm)

numeric_data_binding row89_view : (data.drop 89).take 1 = (data89.drop 0).take 1

numeric_data_binding row89_source : (data89.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [44] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf44).isSome))]

numeric_data_binding row89_entry : (originalEntries.drop 89).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [44] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf44).isSome))]

theorem row89_binding : (data.drop 89).take 1 = (originalEntries.drop 89).take 1 :=
  row89_view.trans (row89_source.trans row89_entry.symm)

numeric_data_binding row90_view : (data.drop 90).take 1 = (data89.drop 1).take 1

numeric_data_binding row90_source : (data89.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw44).inputs)]

numeric_data_binding row90_entry : (originalEntries.drop 90).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw44).inputs)]

theorem row90_binding : (data.drop 90).take 1 = (originalEntries.drop 90).take 1 :=
  row90_view.trans (row90_source.trans row90_entry.symm)

numeric_data_binding row91_view : (data.drop 91).take 1 = (data89.drop 2).take 1

numeric_data_binding row91_source : (data89.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [45] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf45).isSome))]

numeric_data_binding row91_entry : (originalEntries.drop 91).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [45] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf45).isSome))]

theorem row91_binding : (data.drop 91).take 1 = (originalEntries.drop 91).take 1 :=
  row91_view.trans (row91_source.trans row91_entry.symm)

numeric_data_binding row92_view : (data.drop 92).take 1 = (data89.drop 3).take 1

numeric_data_binding row92_source : (data89.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw45).inputs)]

numeric_data_binding row92_entry : (originalEntries.drop 92).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw45).inputs)]

theorem row92_binding : (data.drop 92).take 1 = (originalEntries.drop 92).take 1 :=
  row92_view.trans (row92_source.trans row92_entry.symm)

numeric_data_binding row93_view : (data.drop 93).take 1 = (data93.drop 0).take 1

numeric_data_binding row93_source : (data93.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [46] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf46).isSome))]

numeric_data_binding row93_entry : (originalEntries.drop 93).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [46] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf46).isSome))]

theorem row93_binding : (data.drop 93).take 1 = (originalEntries.drop 93).take 1 :=
  row93_view.trans (row93_source.trans row93_entry.symm)

numeric_data_binding row94_view : (data.drop 94).take 1 = (data93.drop 1).take 1

numeric_data_binding row94_source : (data93.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw46).inputs)]

numeric_data_binding row94_entry : (originalEntries.drop 94).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw46).inputs)]

theorem row94_binding : (data.drop 94).take 1 = (originalEntries.drop 94).take 1 :=
  row94_view.trans (row94_source.trans row94_entry.symm)

numeric_data_binding row95_view : (data.drop 95).take 1 = (data93.drop 2).take 1

numeric_data_binding row95_source : (data93.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [47] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf47).isSome))]

numeric_data_binding row95_entry : (originalEntries.drop 95).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [47] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf47).isSome))]

theorem row95_binding : (data.drop 95).take 1 = (originalEntries.drop 95).take 1 :=
  row95_view.trans (row95_source.trans row95_entry.symm)

numeric_data_binding row96_view : (data.drop 96).take 1 = (data93.drop 3).take 1

numeric_data_binding row96_source : (data93.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw47).inputs)]

numeric_data_binding row96_entry : (originalEntries.drop 96).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw47).inputs)]

theorem row96_binding : (data.drop 96).take 1 = (originalEntries.drop 96).take 1 :=
  row96_view.trans (row96_source.trans row96_entry.symm)

numeric_data_binding row97_view : (data.drop 97).take 1 = (data97.drop 0).take 1

numeric_data_binding row97_source : (data97.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [48] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf48).isSome))]

numeric_data_binding row97_entry : (originalEntries.drop 97).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [48] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf48).isSome))]

theorem row97_binding : (data.drop 97).take 1 = (originalEntries.drop 97).take 1 :=
  row97_view.trans (row97_source.trans row97_entry.symm)

numeric_data_binding row98_view : (data.drop 98).take 1 = (data97.drop 1).take 1

numeric_data_binding row98_source : (data97.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw48).inputs)]

numeric_data_binding row98_entry : (originalEntries.drop 98).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw48).inputs)]

theorem row98_binding : (data.drop 98).take 1 = (originalEntries.drop 98).take 1 :=
  row98_view.trans (row98_source.trans row98_entry.symm)

numeric_data_binding row99_view : (data.drop 99).take 1 = (data97.drop 2).take 1

numeric_data_binding row99_source : (data97.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [49] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf49).isSome))]

numeric_data_binding row99_entry : (originalEntries.drop 99).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [49] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf49).isSome))]

theorem row99_binding : (data.drop 99).take 1 = (originalEntries.drop 99).take 1 :=
  row99_view.trans (row99_source.trans row99_entry.symm)

numeric_data_binding row100_view : (data.drop 100).take 1 = (data97.drop 3).take 1

numeric_data_binding row100_source : (data97.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw49).inputs)]

numeric_data_binding row100_entry : (originalEntries.drop 100).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw49).inputs)]

theorem row100_binding : (data.drop 100).take 1 = (originalEntries.drop 100).take 1 :=
  row100_view.trans (row100_source.trans row100_entry.symm)

numeric_data_binding row101_view : (data.drop 101).take 1 = (data101.drop 0).take 1

numeric_data_binding row101_source : (data101.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [50] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf50).isSome))]

numeric_data_binding row101_entry : (originalEntries.drop 101).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [50] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf50).isSome))]

theorem row101_binding : (data.drop 101).take 1 = (originalEntries.drop 101).take 1 :=
  row101_view.trans (row101_source.trans row101_entry.symm)

numeric_data_binding row102_view : (data.drop 102).take 1 = (data101.drop 1).take 1

numeric_data_binding row102_source : (data101.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw50).inputs)]

numeric_data_binding row102_entry : (originalEntries.drop 102).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw50).inputs)]

theorem row102_binding : (data.drop 102).take 1 = (originalEntries.drop 102).take 1 :=
  row102_view.trans (row102_source.trans row102_entry.symm)

numeric_data_binding row103_view : (data.drop 103).take 1 = (data101.drop 2).take 1

numeric_data_binding row103_source : (data101.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [51] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf51).isSome))]

numeric_data_binding row103_entry : (originalEntries.drop 103).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [51] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf51).isSome))]

theorem row103_binding : (data.drop 103).take 1 = (originalEntries.drop 103).take 1 :=
  row103_view.trans (row103_source.trans row103_entry.symm)

numeric_data_binding row104_view : (data.drop 104).take 1 = (data101.drop 3).take 1

numeric_data_binding row104_source : (data101.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw51).inputs)]

numeric_data_binding row104_entry : (originalEntries.drop 104).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw51).inputs)]

theorem row104_binding : (data.drop 104).take 1 = (originalEntries.drop 104).take 1 :=
  row104_view.trans (row104_source.trans row104_entry.symm)

numeric_data_binding row105_view : (data.drop 105).take 1 = (data105.drop 0).take 1

numeric_data_binding row105_source : (data105.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [52] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf52).isSome))]

numeric_data_binding row105_entry : (originalEntries.drop 105).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [52] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf52).isSome))]

theorem row105_binding : (data.drop 105).take 1 = (originalEntries.drop 105).take 1 :=
  row105_view.trans (row105_source.trans row105_entry.symm)

numeric_data_binding row106_view : (data.drop 106).take 1 = (data105.drop 1).take 1

numeric_data_binding row106_source : (data105.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw52).inputs)]

numeric_data_binding row106_entry : (originalEntries.drop 106).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw52).inputs)]

theorem row106_binding : (data.drop 106).take 1 = (originalEntries.drop 106).take 1 :=
  row106_view.trans (row106_source.trans row106_entry.symm)

numeric_data_binding row107_view : (data.drop 107).take 1 = (data105.drop 2).take 1

numeric_data_binding row107_source : (data105.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [53] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf53).isSome))]

numeric_data_binding row107_entry : (originalEntries.drop 107).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [53] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf53).isSome))]

theorem row107_binding : (data.drop 107).take 1 = (originalEntries.drop 107).take 1 :=
  row107_view.trans (row107_source.trans row107_entry.symm)

numeric_data_binding row108_view : (data.drop 108).take 1 = (data105.drop 3).take 1

numeric_data_binding row108_source : (data105.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw53).inputs)]

numeric_data_binding row108_entry : (originalEntries.drop 108).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw53).inputs)]

theorem row108_binding : (data.drop 108).take 1 = (originalEntries.drop 108).take 1 :=
  row108_view.trans (row108_source.trans row108_entry.symm)

numeric_data_binding row109_view : (data.drop 109).take 1 = (data109.drop 0).take 1

numeric_data_binding row109_source : (data109.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [54] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf54).isSome))]

numeric_data_binding row109_entry : (originalEntries.drop 109).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [54] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf54).isSome))]

theorem row109_binding : (data.drop 109).take 1 = (originalEntries.drop 109).take 1 :=
  row109_view.trans (row109_source.trans row109_entry.symm)

numeric_data_binding row110_view : (data.drop 110).take 1 = (data109.drop 1).take 1

numeric_data_binding row110_source : (data109.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw54).inputs)]

numeric_data_binding row110_entry : (originalEntries.drop 110).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw54).inputs)]

theorem row110_binding : (data.drop 110).take 1 = (originalEntries.drop 110).take 1 :=
  row110_view.trans (row110_source.trans row110_entry.symm)

numeric_data_binding row111_view : (data.drop 111).take 1 = (data109.drop 2).take 1

numeric_data_binding row111_source : (data109.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [55] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf55).isSome))]

numeric_data_binding row111_entry : (originalEntries.drop 111).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [55] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf55).isSome))]

theorem row111_binding : (data.drop 111).take 1 = (originalEntries.drop 111).take 1 :=
  row111_view.trans (row111_source.trans row111_entry.symm)

numeric_data_binding row112_view : (data.drop 112).take 1 = (data109.drop 3).take 1

numeric_data_binding row112_source : (data109.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw55).inputs)]

numeric_data_binding row112_entry : (originalEntries.drop 112).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw55).inputs)]

theorem row112_binding : (data.drop 112).take 1 = (originalEntries.drop 112).take 1 :=
  row112_view.trans (row112_source.trans row112_entry.symm)

numeric_data_binding row113_view : (data.drop 113).take 1 = (data113.drop 0).take 1

numeric_data_binding row113_source : (data113.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [56] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf56).isSome))]

numeric_data_binding row113_entry : (originalEntries.drop 113).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [56] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf56).isSome))]

theorem row113_binding : (data.drop 113).take 1 = (originalEntries.drop 113).take 1 :=
  row113_view.trans (row113_source.trans row113_entry.symm)

numeric_data_binding row114_view : (data.drop 114).take 1 = (data113.drop 1).take 1

numeric_data_binding row114_source : (data113.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw56).inputs)]

numeric_data_binding row114_entry : (originalEntries.drop 114).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw56).inputs)]

theorem row114_binding : (data.drop 114).take 1 = (originalEntries.drop 114).take 1 :=
  row114_view.trans (row114_source.trans row114_entry.symm)

numeric_data_binding row115_view : (data.drop 115).take 1 = (data113.drop 2).take 1

numeric_data_binding row115_source : (data113.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [57] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf57).isSome))]

numeric_data_binding row115_entry : (originalEntries.drop 115).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [57] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf57).isSome))]

theorem row115_binding : (data.drop 115).take 1 = (originalEntries.drop 115).take 1 :=
  row115_view.trans (row115_source.trans row115_entry.symm)

numeric_data_binding row116_view : (data.drop 116).take 1 = (data113.drop 3).take 1

numeric_data_binding row116_source : (data113.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw57).inputs)]

numeric_data_binding row116_entry : (originalEntries.drop 116).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw57).inputs)]

theorem row116_binding : (data.drop 116).take 1 = (originalEntries.drop 116).take 1 :=
  row116_view.trans (row116_source.trans row116_entry.symm)

numeric_data_binding row117_view : (data.drop 117).take 1 = (data117.drop 0).take 1

numeric_data_binding row117_source : (data117.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [58] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf58).isSome))]

numeric_data_binding row117_entry : (originalEntries.drop 117).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [58] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf58).isSome))]

theorem row117_binding : (data.drop 117).take 1 = (originalEntries.drop 117).take 1 :=
  row117_view.trans (row117_source.trans row117_entry.symm)

numeric_data_binding row118_view : (data.drop 118).take 1 = (data117.drop 1).take 1

numeric_data_binding row118_source : (data117.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw58).inputs)]

numeric_data_binding row118_entry : (originalEntries.drop 118).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw58).inputs)]

theorem row118_binding : (data.drop 118).take 1 = (originalEntries.drop 118).take 1 :=
  row118_view.trans (row118_source.trans row118_entry.symm)

numeric_data_binding row119_view : (data.drop 119).take 1 = (data117.drop 2).take 1

numeric_data_binding row119_source : (data117.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [59] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf59).isSome))]

numeric_data_binding row119_entry : (originalEntries.drop 119).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [59] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf59).isSome))]

theorem row119_binding : (data.drop 119).take 1 = (originalEntries.drop 119).take 1 :=
  row119_view.trans (row119_source.trans row119_entry.symm)

numeric_data_binding row120_view : (data.drop 120).take 1 = (data117.drop 3).take 1

numeric_data_binding row120_source : (data117.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw59).inputs)]

numeric_data_binding row120_entry : (originalEntries.drop 120).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw59).inputs)]

theorem row120_binding : (data.drop 120).take 1 = (originalEntries.drop 120).take 1 :=
  row120_view.trans (row120_source.trans row120_entry.symm)

numeric_data_binding row121_view : (data.drop 121).take 1 = (data121.drop 0).take 1

numeric_data_binding row121_source : (data121.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [60] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf60).isSome))]

numeric_data_binding row121_entry : (originalEntries.drop 121).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [60] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf60).isSome))]

theorem row121_binding : (data.drop 121).take 1 = (originalEntries.drop 121).take 1 :=
  row121_view.trans (row121_source.trans row121_entry.symm)

numeric_data_binding row122_view : (data.drop 122).take 1 = (data121.drop 1).take 1

numeric_data_binding row122_source : (data121.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw60).inputs)]

numeric_data_binding row122_entry : (originalEntries.drop 122).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw60).inputs)]

theorem row122_binding : (data.drop 122).take 1 = (originalEntries.drop 122).take 1 :=
  row122_view.trans (row122_source.trans row122_entry.symm)

numeric_data_binding row123_view : (data.drop 123).take 1 = (data121.drop 2).take 1

numeric_data_binding row123_source : (data121.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [61] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf61).isSome))]

numeric_data_binding row123_entry : (originalEntries.drop 123).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [61] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf61).isSome))]

theorem row123_binding : (data.drop 123).take 1 = (originalEntries.drop 123).take 1 :=
  row123_view.trans (row123_source.trans row123_entry.symm)

numeric_data_binding row124_view : (data.drop 124).take 1 = (data121.drop 3).take 1

numeric_data_binding row124_source : (data121.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw61).inputs)]

numeric_data_binding row124_entry : (originalEntries.drop 124).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw61).inputs)]

theorem row124_binding : (data.drop 124).take 1 = (originalEntries.drop 124).take 1 :=
  row124_view.trans (row124_source.trans row124_entry.symm)

numeric_data_binding row125_view : (data.drop 125).take 1 = (data125.drop 0).take 1

numeric_data_binding row125_source : (data125.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [62] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf62).isSome))]

numeric_data_binding row125_entry : (originalEntries.drop 125).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [62] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf62).isSome))]

theorem row125_binding : (data.drop 125).take 1 = (originalEntries.drop 125).take 1 :=
  row125_view.trans (row125_source.trans row125_entry.symm)

numeric_data_binding row126_view : (data.drop 126).take 1 = (data125.drop 1).take 1

numeric_data_binding row126_source : (data125.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw62).inputs)]

numeric_data_binding row126_entry : (originalEntries.drop 126).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw62).inputs)]

theorem row126_binding : (data.drop 126).take 1 = (originalEntries.drop 126).take 1 :=
  row126_view.trans (row126_source.trans row126_entry.symm)

numeric_data_binding row127_view : (data.drop 127).take 1 = (data125.drop 2).take 1

numeric_data_binding row127_source : (data125.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [63] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf63).isSome))]

numeric_data_binding row127_entry : (originalEntries.drop 127).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [63] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf63).isSome))]

theorem row127_binding : (data.drop 127).take 1 = (originalEntries.drop 127).take 1 :=
  row127_view.trans (row127_source.trans row127_entry.symm)

numeric_data_binding row128_view : (data.drop 128).take 1 = (data125.drop 3).take 1

numeric_data_binding row128_source : (data125.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw63).inputs)]

numeric_data_binding row128_entry : (originalEntries.drop 128).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw63).inputs)]

theorem row128_binding : (data.drop 128).take 1 = (originalEntries.drop 128).take 1 :=
  row128_view.trans (row128_source.trans row128_entry.symm)

numeric_data_binding row129_view : (data.drop 129).take 1 = (data129.drop 0).take 1

numeric_data_binding row129_source : (data129.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [64] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf64).isSome))]

numeric_data_binding row129_entry : (originalEntries.drop 129).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [64] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf64).isSome))]

theorem row129_binding : (data.drop 129).take 1 = (originalEntries.drop 129).take 1 :=
  row129_view.trans (row129_source.trans row129_entry.symm)

numeric_data_binding row130_view : (data.drop 130).take 1 = (data129.drop 1).take 1

numeric_data_binding row130_source : (data129.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw64).inputs)]

numeric_data_binding row130_entry : (originalEntries.drop 130).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw64).inputs)]

theorem row130_binding : (data.drop 130).take 1 = (originalEntries.drop 130).take 1 :=
  row130_view.trans (row130_source.trans row130_entry.symm)

numeric_data_binding row131_view : (data.drop 131).take 1 = (data129.drop 2).take 1

numeric_data_binding row131_source : (data129.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [65] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf65).isSome))]

numeric_data_binding row131_entry : (originalEntries.drop 131).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [65] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf65).isSome))]

theorem row131_binding : (data.drop 131).take 1 = (originalEntries.drop 131).take 1 :=
  row131_view.trans (row131_source.trans row131_entry.symm)

numeric_data_binding row132_view : (data.drop 132).take 1 = (data129.drop 3).take 1

numeric_data_binding row132_source : (data129.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw65).inputs)]

numeric_data_binding row132_entry : (originalEntries.drop 132).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw65).inputs)]

theorem row132_binding : (data.drop 132).take 1 = (originalEntries.drop 132).take 1 :=
  row132_view.trans (row132_source.trans row132_entry.symm)

numeric_data_binding row133_view : (data.drop 133).take 1 = (data133.drop 0).take 1

numeric_data_binding row133_source : (data133.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [66] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf66).isSome))]

numeric_data_binding row133_entry : (originalEntries.drop 133).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [66] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf66).isSome))]

theorem row133_binding : (data.drop 133).take 1 = (originalEntries.drop 133).take 1 :=
  row133_view.trans (row133_source.trans row133_entry.symm)

numeric_data_binding row134_view : (data.drop 134).take 1 = (data133.drop 1).take 1

numeric_data_binding row134_source : (data133.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw66).inputs)]

numeric_data_binding row134_entry : (originalEntries.drop 134).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw66).inputs)]

theorem row134_binding : (data.drop 134).take 1 = (originalEntries.drop 134).take 1 :=
  row134_view.trans (row134_source.trans row134_entry.symm)

numeric_data_binding row135_view : (data.drop 135).take 1 = (data133.drop 2).take 1

numeric_data_binding row135_source : (data133.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [67] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf67).isSome))]

numeric_data_binding row135_entry : (originalEntries.drop 135).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [67] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf67).isSome))]

theorem row135_binding : (data.drop 135).take 1 = (originalEntries.drop 135).take 1 :=
  row135_view.trans (row135_source.trans row135_entry.symm)

numeric_data_binding row136_view : (data.drop 136).take 1 = (data133.drop 3).take 1

numeric_data_binding row136_source : (data133.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw67).inputs)]

numeric_data_binding row136_entry : (originalEntries.drop 136).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw67).inputs)]

theorem row136_binding : (data.drop 136).take 1 = (originalEntries.drop 136).take 1 :=
  row136_view.trans (row136_source.trans row136_entry.symm)

numeric_data_binding row137_view : (data.drop 137).take 1 = (data137.drop 0).take 1

numeric_data_binding row137_source : (data137.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [68] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf68).isSome))]

numeric_data_binding row137_entry : (originalEntries.drop 137).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [68] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf68).isSome))]

theorem row137_binding : (data.drop 137).take 1 = (originalEntries.drop 137).take 1 :=
  row137_view.trans (row137_source.trans row137_entry.symm)

numeric_data_binding row138_view : (data.drop 138).take 1 = (data137.drop 1).take 1

numeric_data_binding row138_source : (data137.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw68).inputs)]

numeric_data_binding row138_entry : (originalEntries.drop 138).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw68).inputs)]

theorem row138_binding : (data.drop 138).take 1 = (originalEntries.drop 138).take 1 :=
  row138_view.trans (row138_source.trans row138_entry.symm)

numeric_data_binding row139_view : (data.drop 139).take 1 = (data137.drop 2).take 1

numeric_data_binding row139_source : (data137.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [69] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf69).isSome))]

numeric_data_binding row139_entry : (originalEntries.drop 139).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [69] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf69).isSome))]

theorem row139_binding : (data.drop 139).take 1 = (originalEntries.drop 139).take 1 :=
  row139_view.trans (row139_source.trans row139_entry.symm)

numeric_data_binding row140_view : (data.drop 140).take 1 = (data137.drop 3).take 1

numeric_data_binding row140_source : (data137.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw69).inputs)]

numeric_data_binding row140_entry : (originalEntries.drop 140).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw69).inputs)]

theorem row140_binding : (data.drop 140).take 1 = (originalEntries.drop 140).take 1 :=
  row140_view.trans (row140_source.trans row140_entry.symm)

numeric_data_binding row141_view : (data.drop 141).take 1 = (data141.drop 0).take 1

numeric_data_binding row141_source : (data141.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [70] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf70).isSome))]

numeric_data_binding row141_entry : (originalEntries.drop 141).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [70] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf70).isSome))]

theorem row141_binding : (data.drop 141).take 1 = (originalEntries.drop 141).take 1 :=
  row141_view.trans (row141_source.trans row141_entry.symm)

numeric_data_binding row142_view : (data.drop 142).take 1 = (data141.drop 1).take 1

numeric_data_binding row142_source : (data141.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw70).inputs)]

numeric_data_binding row142_entry : (originalEntries.drop 142).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw70).inputs)]

theorem row142_binding : (data.drop 142).take 1 = (originalEntries.drop 142).take 1 :=
  row142_view.trans (row142_source.trans row142_entry.symm)

numeric_data_binding row143_view : (data.drop 143).take 1 = (data141.drop 2).take 1

numeric_data_binding row143_source : (data141.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [71] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf71).isSome))]

numeric_data_binding row143_entry : (originalEntries.drop 143).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [71] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf71).isSome))]

theorem row143_binding : (data.drop 143).take 1 = (originalEntries.drop 143).take 1 :=
  row143_view.trans (row143_source.trans row143_entry.symm)

numeric_data_binding row144_view : (data.drop 144).take 1 = (data141.drop 3).take 1

numeric_data_binding row144_source : (data141.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw71).inputs)]

numeric_data_binding row144_entry : (originalEntries.drop 144).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw71).inputs)]

theorem row144_binding : (data.drop 144).take 1 = (originalEntries.drop 144).take 1 :=
  row144_view.trans (row144_source.trans row144_entry.symm)

numeric_data_binding row145_view : (data.drop 145).take 1 = (data145.drop 0).take 1

numeric_data_binding row145_source : (data145.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [72] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf72).isSome))]

numeric_data_binding row145_entry : (originalEntries.drop 145).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [72] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf72).isSome))]

theorem row145_binding : (data.drop 145).take 1 = (originalEntries.drop 145).take 1 :=
  row145_view.trans (row145_source.trans row145_entry.symm)

numeric_data_binding row146_view : (data.drop 146).take 1 = (data145.drop 1).take 1

numeric_data_binding row146_source : (data145.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw72).inputs)]

numeric_data_binding row146_entry : (originalEntries.drop 146).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw72).inputs)]

theorem row146_binding : (data.drop 146).take 1 = (originalEntries.drop 146).take 1 :=
  row146_view.trans (row146_source.trans row146_entry.symm)

numeric_data_binding row147_view : (data.drop 147).take 1 = (data145.drop 2).take 1

numeric_data_binding row147_source : (data145.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [73] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf73).isSome))]

numeric_data_binding row147_entry : (originalEntries.drop 147).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [73] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf73).isSome))]

theorem row147_binding : (data.drop 147).take 1 = (originalEntries.drop 147).take 1 :=
  row147_view.trans (row147_source.trans row147_entry.symm)

numeric_data_binding row148_view : (data.drop 148).take 1 = (data145.drop 3).take 1

numeric_data_binding row148_source : (data145.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw73).inputs)]

numeric_data_binding row148_entry : (originalEntries.drop 148).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw73).inputs)]

theorem row148_binding : (data.drop 148).take 1 = (originalEntries.drop 148).take 1 :=
  row148_view.trans (row148_source.trans row148_entry.symm)

numeric_data_binding row149_view : (data.drop 149).take 1 = (data149.drop 0).take 1

numeric_data_binding row149_source : (data149.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [74] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf74).isSome))]

numeric_data_binding row149_entry : (originalEntries.drop 149).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [74] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf74).isSome))]

theorem row149_binding : (data.drop 149).take 1 = (originalEntries.drop 149).take 1 :=
  row149_view.trans (row149_source.trans row149_entry.symm)

numeric_data_binding row150_view : (data.drop 150).take 1 = (data149.drop 1).take 1

numeric_data_binding row150_source : (data149.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw74).inputs)]

numeric_data_binding row150_entry : (originalEntries.drop 150).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw74).inputs)]

theorem row150_binding : (data.drop 150).take 1 = (originalEntries.drop 150).take 1 :=
  row150_view.trans (row150_source.trans row150_entry.symm)

numeric_data_binding row151_view : (data.drop 151).take 1 = (data149.drop 2).take 1

numeric_data_binding row151_source : (data149.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [75] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf75).isSome))]

numeric_data_binding row151_entry : (originalEntries.drop 151).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [75] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf75).isSome))]

theorem row151_binding : (data.drop 151).take 1 = (originalEntries.drop 151).take 1 :=
  row151_view.trans (row151_source.trans row151_entry.symm)

numeric_data_binding row152_view : (data.drop 152).take 1 = (data149.drop 3).take 1

numeric_data_binding row152_source : (data149.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw75).inputs)]

numeric_data_binding row152_entry : (originalEntries.drop 152).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw75).inputs)]

theorem row152_binding : (data.drop 152).take 1 = (originalEntries.drop 152).take 1 :=
  row152_view.trans (row152_source.trans row152_entry.symm)

numeric_data_binding row153_view : (data.drop 153).take 1 = (data153.drop 0).take 1

numeric_data_binding row153_source : (data153.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [76] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf76).isSome))]

numeric_data_binding row153_entry : (originalEntries.drop 153).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [76] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf76).isSome))]

theorem row153_binding : (data.drop 153).take 1 = (originalEntries.drop 153).take 1 :=
  row153_view.trans (row153_source.trans row153_entry.symm)

numeric_data_binding row154_view : (data.drop 154).take 1 = (data153.drop 1).take 1

numeric_data_binding row154_source : (data153.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw76).inputs)]

numeric_data_binding row154_entry : (originalEntries.drop 154).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw76).inputs)]

theorem row154_binding : (data.drop 154).take 1 = (originalEntries.drop 154).take 1 :=
  row154_view.trans (row154_source.trans row154_entry.symm)

numeric_data_binding row155_view : (data.drop 155).take 1 = (data153.drop 2).take 1

numeric_data_binding row155_source : (data153.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [77] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf77).isSome))]

numeric_data_binding row155_entry : (originalEntries.drop 155).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [77] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf77).isSome))]

theorem row155_binding : (data.drop 155).take 1 = (originalEntries.drop 155).take 1 :=
  row155_view.trans (row155_source.trans row155_entry.symm)

numeric_data_binding row156_view : (data.drop 156).take 1 = (data153.drop 3).take 1

numeric_data_binding row156_source : (data153.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw77).inputs)]

numeric_data_binding row156_entry : (originalEntries.drop 156).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw77).inputs)]

theorem row156_binding : (data.drop 156).take 1 = (originalEntries.drop 156).take 1 :=
  row156_view.trans (row156_source.trans row156_entry.symm)

numeric_data_binding row157_view : (data.drop 157).take 1 = (data157.drop 0).take 1

numeric_data_binding row157_source : (data157.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [78] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf78).isSome))]

numeric_data_binding row157_entry : (originalEntries.drop 157).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [78] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf78).isSome))]

theorem row157_binding : (data.drop 157).take 1 = (originalEntries.drop 157).take 1 :=
  row157_view.trans (row157_source.trans row157_entry.symm)

numeric_data_binding row158_view : (data.drop 158).take 1 = (data157.drop 1).take 1

numeric_data_binding row158_source : (data157.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw78).inputs)]

numeric_data_binding row158_entry : (originalEntries.drop 158).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw78).inputs)]

theorem row158_binding : (data.drop 158).take 1 = (originalEntries.drop 158).take 1 :=
  row158_view.trans (row158_source.trans row158_entry.symm)

numeric_data_binding row159_view : (data.drop 159).take 1 = (data157.drop 2).take 1

numeric_data_binding row159_source : (data157.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [79] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf79).isSome))]

numeric_data_binding row159_entry : (originalEntries.drop 159).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [79] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf79).isSome))]

theorem row159_binding : (data.drop 159).take 1 = (originalEntries.drop 159).take 1 :=
  row159_view.trans (row159_source.trans row159_entry.symm)

numeric_data_binding row160_view : (data.drop 160).take 1 = (data157.drop 3).take 1

numeric_data_binding row160_source : (data157.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw79).inputs)]

numeric_data_binding row160_entry : (originalEntries.drop 160).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw79).inputs)]

theorem row160_binding : (data.drop 160).take 1 = (originalEntries.drop 160).take 1 :=
  row160_view.trans (row160_source.trans row160_entry.symm)

numeric_data_binding row161_view : (data.drop 161).take 1 = (data161.drop 0).take 1

numeric_data_binding row161_source : (data161.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [80] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf80).isSome))]

numeric_data_binding row161_entry : (originalEntries.drop 161).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [80] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf80).isSome))]

theorem row161_binding : (data.drop 161).take 1 = (originalEntries.drop 161).take 1 :=
  row161_view.trans (row161_source.trans row161_entry.symm)

numeric_data_binding row162_view : (data.drop 162).take 1 = (data161.drop 1).take 1

numeric_data_binding row162_source : (data161.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw80).inputs)]

numeric_data_binding row162_entry : (originalEntries.drop 162).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw80).inputs)]

theorem row162_binding : (data.drop 162).take 1 = (originalEntries.drop 162).take 1 :=
  row162_view.trans (row162_source.trans row162_entry.symm)

numeric_data_binding row163_view : (data.drop 163).take 1 = (data161.drop 2).take 1

numeric_data_binding row163_source : (data161.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [81] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf81).isSome))]

numeric_data_binding row163_entry : (originalEntries.drop 163).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [81] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf81).isSome))]

theorem row163_binding : (data.drop 163).take 1 = (originalEntries.drop 163).take 1 :=
  row163_view.trans (row163_source.trans row163_entry.symm)

numeric_data_binding row164_view : (data.drop 164).take 1 = (data161.drop 3).take 1

numeric_data_binding row164_source : (data161.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw81).inputs)]

numeric_data_binding row164_entry : (originalEntries.drop 164).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw81).inputs)]

theorem row164_binding : (data.drop 164).take 1 = (originalEntries.drop 164).take 1 :=
  row164_view.trans (row164_source.trans row164_entry.symm)

numeric_data_binding row165_view : (data.drop 165).take 1 = (data165.drop 0).take 1

numeric_data_binding row165_source : (data165.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [82] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf82).isSome))]

numeric_data_binding row165_entry : (originalEntries.drop 165).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [82] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf82).isSome))]

theorem row165_binding : (data.drop 165).take 1 = (originalEntries.drop 165).take 1 :=
  row165_view.trans (row165_source.trans row165_entry.symm)

numeric_data_binding row166_view : (data.drop 166).take 1 = (data165.drop 1).take 1

numeric_data_binding row166_source : (data165.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw82).inputs)]

numeric_data_binding row166_entry : (originalEntries.drop 166).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw82).inputs)]

theorem row166_binding : (data.drop 166).take 1 = (originalEntries.drop 166).take 1 :=
  row166_view.trans (row166_source.trans row166_entry.symm)

numeric_data_binding row167_view : (data.drop 167).take 1 = (data165.drop 2).take 1

numeric_data_binding row167_source : (data165.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [83] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf83).isSome))]

numeric_data_binding row167_entry : (originalEntries.drop 167).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [83] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf83).isSome))]

theorem row167_binding : (data.drop 167).take 1 = (originalEntries.drop 167).take 1 :=
  row167_view.trans (row167_source.trans row167_entry.symm)

numeric_data_binding row168_view : (data.drop 168).take 1 = (data165.drop 3).take 1

numeric_data_binding row168_source : (data165.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw83).inputs)]

numeric_data_binding row168_entry : (originalEntries.drop 168).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw83).inputs)]

theorem row168_binding : (data.drop 168).take 1 = (originalEntries.drop 168).take 1 :=
  row168_view.trans (row168_source.trans row168_entry.symm)

numeric_data_binding row169_view : (data.drop 169).take 1 = (data169.drop 0).take 1

numeric_data_binding row169_source : (data169.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [84] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf84).isSome))]

numeric_data_binding row169_entry : (originalEntries.drop 169).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [84] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf84).isSome))]

theorem row169_binding : (data.drop 169).take 1 = (originalEntries.drop 169).take 1 :=
  row169_view.trans (row169_source.trans row169_entry.symm)

numeric_data_binding row170_view : (data.drop 170).take 1 = (data169.drop 1).take 1

numeric_data_binding row170_source : (data169.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw84).inputs)]

numeric_data_binding row170_entry : (originalEntries.drop 170).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw84).inputs)]

theorem row170_binding : (data.drop 170).take 1 = (originalEntries.drop 170).take 1 :=
  row170_view.trans (row170_source.trans row170_entry.symm)

numeric_data_binding row171_view : (data.drop 171).take 1 = (data169.drop 2).take 1

numeric_data_binding row171_source : (data169.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [85] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf85).isSome))]

numeric_data_binding row171_entry : (originalEntries.drop 171).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [85] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf85).isSome))]

theorem row171_binding : (data.drop 171).take 1 = (originalEntries.drop 171).take 1 :=
  row171_view.trans (row171_source.trans row171_entry.symm)

numeric_data_binding row172_view : (data.drop 172).take 1 = (data169.drop 3).take 1

numeric_data_binding row172_source : (data169.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw85).inputs)]

numeric_data_binding row172_entry : (originalEntries.drop 172).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw85).inputs)]

theorem row172_binding : (data.drop 172).take 1 = (originalEntries.drop 172).take 1 :=
  row172_view.trans (row172_source.trans row172_entry.symm)

numeric_data_binding row173_view : (data.drop 173).take 1 = (data173.drop 0).take 1

numeric_data_binding row173_source : (data173.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [86] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf86).isSome))]

numeric_data_binding row173_entry : (originalEntries.drop 173).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [86] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf86).isSome))]

theorem row173_binding : (data.drop 173).take 1 = (originalEntries.drop 173).take 1 :=
  row173_view.trans (row173_source.trans row173_entry.symm)

numeric_data_binding row174_view : (data.drop 174).take 1 = (data173.drop 1).take 1

numeric_data_binding row174_source : (data173.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw86).inputs)]

numeric_data_binding row174_entry : (originalEntries.drop 174).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw86).inputs)]

theorem row174_binding : (data.drop 174).take 1 = (originalEntries.drop 174).take 1 :=
  row174_view.trans (row174_source.trans row174_entry.symm)

numeric_data_binding row175_view : (data.drop 175).take 1 = (data173.drop 2).take 1

numeric_data_binding row175_source : (data173.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [87] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf87).isSome))]

numeric_data_binding row175_entry : (originalEntries.drop 175).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeRoundCached.native.definitions [87] Airbender.Compiler.MemoryNative.BlakeRoundCached.native.leaf87).isSome))]

theorem row175_binding : (data.drop 175).take 1 = (originalEntries.drop 175).take 1 :=
  row175_view.trans (row175_source.trans row175_entry.symm)

numeric_data_binding row176_view : (data.drop 176).take 1 = (data173.drop 3).take 1

numeric_data_binding row176_source : (data173.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw87).inputs)]

numeric_data_binding row176_entry : (originalEntries.drop 176).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw87).inputs)]

theorem row176_binding : (data.drop 176).take 1 = (originalEntries.drop 176).take 1 :=
  row176_view.trans (row176_source.trans row176_entry.symm)

numeric_data_binding row177_view : (data.drop 177).take 1 = (data177.drop 0).take 1

numeric_data_binding row177_source : (data177.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw0 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row177_entry : (originalEntries.drop 177).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw0 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row177_binding : (data.drop 177).take 1 = (originalEntries.drop 177).take 1 :=
  row177_view.trans (row177_source.trans row177_entry.symm)

numeric_data_binding row178_view : (data.drop 178).take 1 = (data177.drop 1).take 1

numeric_data_binding row178_source : (data177.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw1 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row178_entry : (originalEntries.drop 178).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw1 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row178_binding : (data.drop 178).take 1 = (originalEntries.drop 178).take 1 :=
  row178_view.trans (row178_source.trans row178_entry.symm)

numeric_data_binding row179_view : (data.drop 179).take 1 = (data177.drop 2).take 1

numeric_data_binding row179_source : (data177.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw4 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row179_entry : (originalEntries.drop 179).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw4 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row179_binding : (data.drop 179).take 1 = (originalEntries.drop 179).take 1 :=
  row179_view.trans (row179_source.trans row179_entry.symm)

numeric_data_binding row180_view : (data.drop 180).take 1 = (data177.drop 3).take 1

numeric_data_binding row180_source : (data177.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw5 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row180_entry : (originalEntries.drop 180).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw5 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row180_binding : (data.drop 180).take 1 = (originalEntries.drop 180).take 1 :=
  row180_view.trans (row180_source.trans row180_entry.symm)

numeric_data_binding row181_view : (data.drop 181).take 1 = (data181.drop 0).take 1

numeric_data_binding row181_source : (data181.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate4 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw8 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row181_entry : (originalEntries.drop 181).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate4 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw8 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row181_binding : (data.drop 181).take 1 = (originalEntries.drop 181).take 1 :=
  row181_view.trans (row181_source.trans row181_entry.symm)

numeric_data_binding row182_view : (data.drop 182).take 1 = (data181.drop 1).take 1

numeric_data_binding row182_source : (data181.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate5 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw9 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row182_entry : (originalEntries.drop 182).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate5 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw9 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row182_binding : (data.drop 182).take 1 = (originalEntries.drop 182).take 1 :=
  row182_view.trans (row182_source.trans row182_entry.symm)

numeric_data_binding row183_view : (data.drop 183).take 1 = (data181.drop 2).take 1

numeric_data_binding row183_source : (data181.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate6 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw12 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row183_entry : (originalEntries.drop 183).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate6 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw12 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row183_binding : (data.drop 183).take 1 = (originalEntries.drop 183).take 1 :=
  row183_view.trans (row183_source.trans row183_entry.symm)

numeric_data_binding row184_view : (data.drop 184).take 1 = (data181.drop 3).take 1

numeric_data_binding row184_source : (data181.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate7 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw13 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row184_entry : (originalEntries.drop 184).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate7 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw13 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row184_binding : (data.drop 184).take 1 = (originalEntries.drop 184).take 1 :=
  row184_view.trans (row184_source.trans row184_entry.symm)

numeric_data_binding row185_view : (data.drop 185).take 1 = (data185.drop 0).take 1

numeric_data_binding row185_source : (data185.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate8 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw16 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row185_entry : (originalEntries.drop 185).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate8 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw16 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row185_binding : (data.drop 185).take 1 = (originalEntries.drop 185).take 1 :=
  row185_view.trans (row185_source.trans row185_entry.symm)

numeric_data_binding row186_view : (data.drop 186).take 1 = (data185.drop 1).take 1

numeric_data_binding row186_source : (data185.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate9 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw17 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row186_entry : (originalEntries.drop 186).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate9 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw17 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row186_binding : (data.drop 186).take 1 = (originalEntries.drop 186).take 1 :=
  row186_view.trans (row186_source.trans row186_entry.symm)

numeric_data_binding row187_view : (data.drop 187).take 1 = (data185.drop 2).take 1

numeric_data_binding row187_source : (data185.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate10 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw20 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row187_entry : (originalEntries.drop 187).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate10 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw20 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row187_binding : (data.drop 187).take 1 = (originalEntries.drop 187).take 1 :=
  row187_view.trans (row187_source.trans row187_entry.symm)

numeric_data_binding row188_view : (data.drop 188).take 1 = (data185.drop 3).take 1

numeric_data_binding row188_source : (data185.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate11 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw21 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row188_entry : (originalEntries.drop 188).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate11 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw21 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row188_binding : (data.drop 188).take 1 = (originalEntries.drop 188).take 1 :=
  row188_view.trans (row188_source.trans row188_entry.symm)

numeric_data_binding row189_view : (data.drop 189).take 1 = (data189.drop 0).take 1

numeric_data_binding row189_source : (data189.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate12 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw24 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row189_entry : (originalEntries.drop 189).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate12 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw24 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row189_binding : (data.drop 189).take 1 = (originalEntries.drop 189).take 1 :=
  row189_view.trans (row189_source.trans row189_entry.symm)

numeric_data_binding row190_view : (data.drop 190).take 1 = (data189.drop 1).take 1

numeric_data_binding row190_source : (data189.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate13 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw25 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row190_entry : (originalEntries.drop 190).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate13 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw25 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row190_binding : (data.drop 190).take 1 = (originalEntries.drop 190).take 1 :=
  row190_view.trans (row190_source.trans row190_entry.symm)

numeric_data_binding row191_view : (data.drop 191).take 1 = (data189.drop 2).take 1

numeric_data_binding row191_source : (data189.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate14 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw28 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row191_entry : (originalEntries.drop 191).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate14 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw28 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row191_binding : (data.drop 191).take 1 = (originalEntries.drop 191).take 1 :=
  row191_view.trans (row191_source.trans row191_entry.symm)

numeric_data_binding row192_view : (data.drop 192).take 1 = (data189.drop 3).take 1

numeric_data_binding row192_source : (data189.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate15 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[15]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw29 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row192_entry : (originalEntries.drop 192).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate15 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[15]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw29 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row192_binding : (data.drop 192).take 1 = (originalEntries.drop 192).take 1 :=
  row192_view.trans (row192_source.trans row192_entry.symm)

numeric_data_binding row193_view : (data.drop 193).take 1 = (data193.drop 0).take 1

numeric_data_binding row193_source : (data193.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate16 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[16]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw32 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row193_entry : (originalEntries.drop 193).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate16 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[16]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw32 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row193_binding : (data.drop 193).take 1 = (originalEntries.drop 193).take 1 :=
  row193_view.trans (row193_source.trans row193_entry.symm)

numeric_data_binding row194_view : (data.drop 194).take 1 = (data193.drop 1).take 1

numeric_data_binding row194_source : (data193.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate17 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[17]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw33 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row194_entry : (originalEntries.drop 194).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate17 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[17]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw33 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row194_binding : (data.drop 194).take 1 = (originalEntries.drop 194).take 1 :=
  row194_view.trans (row194_source.trans row194_entry.symm)

numeric_data_binding row195_view : (data.drop 195).take 1 = (data193.drop 2).take 1

numeric_data_binding row195_source : (data193.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate18 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[18]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw36 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row195_entry : (originalEntries.drop 195).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate18 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[18]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw36 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row195_binding : (data.drop 195).take 1 = (originalEntries.drop 195).take 1 :=
  row195_view.trans (row195_source.trans row195_entry.symm)

numeric_data_binding row196_view : (data.drop 196).take 1 = (data193.drop 3).take 1

numeric_data_binding row196_source : (data193.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate19 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[19]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw37 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row196_entry : (originalEntries.drop 196).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate19 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[19]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw37 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row196_binding : (data.drop 196).take 1 = (originalEntries.drop 196).take 1 :=
  row196_view.trans (row196_source.trans row196_entry.symm)

numeric_data_binding row197_view : (data.drop 197).take 1 = (data197.drop 0).take 1

numeric_data_binding row197_source : (data197.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate20 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[20]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw40 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row197_entry : (originalEntries.drop 197).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate20 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[20]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw40 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row197_binding : (data.drop 197).take 1 = (originalEntries.drop 197).take 1 :=
  row197_view.trans (row197_source.trans row197_entry.symm)

numeric_data_binding row198_view : (data.drop 198).take 1 = (data197.drop 1).take 1

numeric_data_binding row198_source : (data197.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate21 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[21]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw41 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row198_entry : (originalEntries.drop 198).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate21 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[21]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw41 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row198_binding : (data.drop 198).take 1 = (originalEntries.drop 198).take 1 :=
  row198_view.trans (row198_source.trans row198_entry.symm)

numeric_data_binding row199_view : (data.drop 199).take 1 = (data197.drop 2).take 1

numeric_data_binding row199_source : (data197.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate22 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[22]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw44 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row199_entry : (originalEntries.drop 199).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate22 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[22]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw44 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row199_binding : (data.drop 199).take 1 = (originalEntries.drop 199).take 1 :=
  row199_view.trans (row199_source.trans row199_entry.symm)

numeric_data_binding row200_view : (data.drop 200).take 1 = (data197.drop 3).take 1

numeric_data_binding row200_source : (data197.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate23 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[23]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw45 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row200_entry : (originalEntries.drop 200).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate23 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[23]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw45 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row200_binding : (data.drop 200).take 1 = (originalEntries.drop 200).take 1 :=
  row200_view.trans (row200_source.trans row200_entry.symm)

numeric_data_binding row201_view : (data.drop 201).take 1 = (data201.drop 0).take 1

numeric_data_binding row201_source : (data201.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate24 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[24]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw48 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row201_entry : (originalEntries.drop 201).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate24 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[24]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw48 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row201_binding : (data.drop 201).take 1 = (originalEntries.drop 201).take 1 :=
  row201_view.trans (row201_source.trans row201_entry.symm)

numeric_data_binding row202_view : (data.drop 202).take 1 = (data201.drop 1).take 1

numeric_data_binding row202_source : (data201.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate25 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[25]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw49 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row202_entry : (originalEntries.drop 202).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate25 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[25]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw49 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row202_binding : (data.drop 202).take 1 = (originalEntries.drop 202).take 1 :=
  row202_view.trans (row202_source.trans row202_entry.symm)

numeric_data_binding row203_view : (data.drop 203).take 1 = (data201.drop 2).take 1

numeric_data_binding row203_source : (data201.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate26 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[26]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw52 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row203_entry : (originalEntries.drop 203).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate26 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[26]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw52 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row203_binding : (data.drop 203).take 1 = (originalEntries.drop 203).take 1 :=
  row203_view.trans (row203_source.trans row203_entry.symm)

numeric_data_binding row204_view : (data.drop 204).take 1 = (data201.drop 3).take 1

numeric_data_binding row204_source : (data201.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate27 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[27]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw53 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row204_entry : (originalEntries.drop 204).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate27 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[27]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw53 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row204_binding : (data.drop 204).take 1 = (originalEntries.drop 204).take 1 :=
  row204_view.trans (row204_source.trans row204_entry.symm)

numeric_data_binding row205_view : (data.drop 205).take 1 = (data205.drop 0).take 1

numeric_data_binding row205_source : (data205.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate28 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[28]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw56 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row205_entry : (originalEntries.drop 205).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate28 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[28]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw56 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row205_binding : (data.drop 205).take 1 = (originalEntries.drop 205).take 1 :=
  row205_view.trans (row205_source.trans row205_entry.symm)

numeric_data_binding row206_view : (data.drop 206).take 1 = (data205.drop 1).take 1

numeric_data_binding row206_source : (data205.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate29 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[29]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw57 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row206_entry : (originalEntries.drop 206).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate29 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[29]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw57 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row206_binding : (data.drop 206).take 1 = (originalEntries.drop 206).take 1 :=
  row206_view.trans (row206_source.trans row206_entry.symm)

numeric_data_binding row207_view : (data.drop 207).take 1 = (data205.drop 2).take 1

numeric_data_binding row207_source : (data205.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate30 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[30]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw60 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row207_entry : (originalEntries.drop 207).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate30 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[30]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw60 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row207_binding : (data.drop 207).take 1 = (originalEntries.drop 207).take 1 :=
  row207_view.trans (row207_source.trans row207_entry.symm)

numeric_data_binding row208_view : (data.drop 208).take 1 = (data205.drop 3).take 1

numeric_data_binding row208_source : (data205.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate31 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[31]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw61 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row208_entry : (originalEntries.drop 208).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate31 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[31]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw61 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row208_binding : (data.drop 208).take 1 = (originalEntries.drop 208).take 1 :=
  row208_view.trans (row208_source.trans row208_entry.symm)

numeric_data_binding row209_view : (data.drop 209).take 1 = (data209.drop 0).take 1

numeric_data_binding row209_source : (data209.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate32 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[32]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw64 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row209_entry : (originalEntries.drop 209).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate32 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[32]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw64 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row209_binding : (data.drop 209).take 1 = (originalEntries.drop 209).take 1 :=
  row209_view.trans (row209_source.trans row209_entry.symm)

numeric_data_binding row210_view : (data.drop 210).take 1 = (data209.drop 1).take 1

numeric_data_binding row210_source : (data209.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate33 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[33]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw65 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row210_entry : (originalEntries.drop 210).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate33 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[33]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw65 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row210_binding : (data.drop 210).take 1 = (originalEntries.drop 210).take 1 :=
  row210_view.trans (row210_source.trans row210_entry.symm)

numeric_data_binding row211_view : (data.drop 211).take 1 = (data209.drop 2).take 1

numeric_data_binding row211_source : (data209.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate34 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[34]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw68 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row211_entry : (originalEntries.drop 211).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate34 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[34]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw68 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row211_binding : (data.drop 211).take 1 = (originalEntries.drop 211).take 1 :=
  row211_view.trans (row211_source.trans row211_entry.symm)

numeric_data_binding row212_view : (data.drop 212).take 1 = (data209.drop 3).take 1

numeric_data_binding row212_source : (data209.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate35 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[35]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw69 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row212_entry : (originalEntries.drop 212).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate35 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[35]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw69 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row212_binding : (data.drop 212).take 1 = (originalEntries.drop 212).take 1 :=
  row212_view.trans (row212_source.trans row212_entry.symm)

numeric_data_binding row213_view : (data.drop 213).take 1 = (data213.drop 0).take 1

numeric_data_binding row213_source : (data213.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate36 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[36]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw72 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row213_entry : (originalEntries.drop 213).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate36 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[36]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw72 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row213_binding : (data.drop 213).take 1 = (originalEntries.drop 213).take 1 :=
  row213_view.trans (row213_source.trans row213_entry.symm)

numeric_data_binding row214_view : (data.drop 214).take 1 = (data213.drop 1).take 1

numeric_data_binding row214_source : (data213.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate37 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[37]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw73 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row214_entry : (originalEntries.drop 214).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate37 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[37]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw73 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row214_binding : (data.drop 214).take 1 = (originalEntries.drop 214).take 1 :=
  row214_view.trans (row214_source.trans row214_entry.symm)

numeric_data_binding row215_view : (data.drop 215).take 1 = (data213.drop 2).take 1

numeric_data_binding row215_source : (data213.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate38 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[38]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw76 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row215_entry : (originalEntries.drop 215).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate38 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[38]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw76 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row215_binding : (data.drop 215).take 1 = (originalEntries.drop 215).take 1 :=
  row215_view.trans (row215_source.trans row215_entry.symm)

numeric_data_binding row216_view : (data.drop 216).take 1 = (data213.drop 3).take 1

numeric_data_binding row216_source : (data213.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate39 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[39]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw77 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row216_entry : (originalEntries.drop 216).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate39 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[39]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw77 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row216_binding : (data.drop 216).take 1 = (originalEntries.drop 216).take 1 :=
  row216_view.trans (row216_source.trans row216_entry.symm)

numeric_data_binding row217_view : (data.drop 217).take 1 = (data217.drop 0).take 1

numeric_data_binding row217_source : (data217.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate40 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[40]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw80 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row217_entry : (originalEntries.drop 217).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate40 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[40]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw80 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row217_binding : (data.drop 217).take 1 = (originalEntries.drop 217).take 1 :=
  row217_view.trans (row217_source.trans row217_entry.symm)

numeric_data_binding row218_view : (data.drop 218).take 1 = (data217.drop 1).take 1

numeric_data_binding row218_source : (data217.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate41 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[41]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw81 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row218_entry : (originalEntries.drop 218).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate41 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[41]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw81 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row218_binding : (data.drop 218).take 1 = (originalEntries.drop 218).take 1 :=
  row218_view.trans (row218_source.trans row218_entry.symm)

numeric_data_binding row219_view : (data.drop 219).take 1 = (data217.drop 2).take 1

numeric_data_binding row219_source : (data217.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate42 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[42]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw84 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row219_entry : (originalEntries.drop 219).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate42 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[42]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw84 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row219_binding : (data.drop 219).take 1 = (originalEntries.drop 219).take 1 :=
  row219_view.trans (row219_source.trans row219_entry.symm)

numeric_data_binding row220_view : (data.drop 220).take 1 = (data217.drop 3).take 1

numeric_data_binding row220_source : (data217.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate43 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[43]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw85 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row220_entry : (originalEntries.drop 220).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadCertificate43 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows)[43]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw85 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row220_binding : (data.drop 220).take 1 = (originalEntries.drop 220).take 1 :=
  row220_view.trans (row220_source.trans row220_entry.symm)

numeric_data_binding row221_view : (data.drop 221).take 1 = (data221.drop 0).take 1

numeric_data_binding row221_source : (data221.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing [(GKRAddress.InnerLayer 6 0)])]

numeric_data_binding row221_entry : (originalEntries.drop 221).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing [(GKRAddress.InnerLayer 6 0)])]

theorem row221_binding : (data.drop 221).take 1 = (originalEntries.drop 221).take 1 :=
  row221_view.trans (row221_source.trans row221_entry.symm)

numeric_data_binding row222_view : (data.drop 222).take 1 = (data221.drop 1).take 1

numeric_data_binding row222_source : (data221.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw2 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row222_entry : (originalEntries.drop 222).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw2 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row222_binding : (data.drop 222).take 1 = (originalEntries.drop 222).take 1 :=
  row222_view.trans (row222_source.trans row222_entry.symm)

numeric_data_binding row223_view : (data.drop 223).take 1 = (data221.drop 2).take 1

numeric_data_binding row223_source : (data221.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw3 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row223_entry : (originalEntries.drop 223).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw3 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row223_binding : (data.drop 223).take 1 = (originalEntries.drop 223).take 1 :=
  row223_view.trans (row223_source.trans row223_entry.symm)

numeric_data_binding row224_view : (data.drop 224).take 1 = (data221.drop 3).take 1

numeric_data_binding row224_source : (data221.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw6 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row224_entry : (originalEntries.drop 224).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw6 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row224_binding : (data.drop 224).take 1 = (originalEntries.drop 224).take 1 :=
  row224_view.trans (row224_source.trans row224_entry.symm)

numeric_data_binding row225_view : (data.drop 225).take 1 = (data225.drop 0).take 1

numeric_data_binding row225_source : (data225.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw7 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row225_entry : (originalEntries.drop 225).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw7 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row225_binding : (data.drop 225).take 1 = (originalEntries.drop 225).take 1 :=
  row225_view.trans (row225_source.trans row225_entry.symm)

numeric_data_binding row226_view : (data.drop 226).take 1 = (data225.drop 1).take 1

numeric_data_binding row226_source : (data225.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate4 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw10 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row226_entry : (originalEntries.drop 226).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate4 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw10 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row226_binding : (data.drop 226).take 1 = (originalEntries.drop 226).take 1 :=
  row226_view.trans (row226_source.trans row226_entry.symm)

numeric_data_binding row227_view : (data.drop 227).take 1 = (data225.drop 2).take 1

numeric_data_binding row227_source : (data225.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate5 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw11 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row227_entry : (originalEntries.drop 227).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate5 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw11 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row227_binding : (data.drop 227).take 1 = (originalEntries.drop 227).take 1 :=
  row227_view.trans (row227_source.trans row227_entry.symm)

numeric_data_binding row228_view : (data.drop 228).take 1 = (data225.drop 3).take 1

numeric_data_binding row228_source : (data225.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate6 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw14 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row228_entry : (originalEntries.drop 228).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate6 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw14 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row228_binding : (data.drop 228).take 1 = (originalEntries.drop 228).take 1 :=
  row228_view.trans (row228_source.trans row228_entry.symm)

numeric_data_binding row229_view : (data.drop 229).take 1 = (data229.drop 0).take 1

numeric_data_binding row229_source : (data229.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate7 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw15 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row229_entry : (originalEntries.drop 229).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate7 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw15 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row229_binding : (data.drop 229).take 1 = (originalEntries.drop 229).take 1 :=
  row229_view.trans (row229_source.trans row229_entry.symm)

numeric_data_binding row230_view : (data.drop 230).take 1 = (data229.drop 1).take 1

numeric_data_binding row230_source : (data229.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate8 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw18 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row230_entry : (originalEntries.drop 230).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate8 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw18 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row230_binding : (data.drop 230).take 1 = (originalEntries.drop 230).take 1 :=
  row230_view.trans (row230_source.trans row230_entry.symm)

numeric_data_binding row231_view : (data.drop 231).take 1 = (data229.drop 2).take 1

numeric_data_binding row231_source : (data229.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate9 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw19 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row231_entry : (originalEntries.drop 231).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate9 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw19 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row231_binding : (data.drop 231).take 1 = (originalEntries.drop 231).take 1 :=
  row231_view.trans (row231_source.trans row231_entry.symm)

numeric_data_binding row232_view : (data.drop 232).take 1 = (data229.drop 3).take 1

numeric_data_binding row232_source : (data229.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate10 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw22 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row232_entry : (originalEntries.drop 232).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate10 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw22 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row232_binding : (data.drop 232).take 1 = (originalEntries.drop 232).take 1 :=
  row232_view.trans (row232_source.trans row232_entry.symm)

numeric_data_binding row233_view : (data.drop 233).take 1 = (data233.drop 0).take 1

numeric_data_binding row233_source : (data233.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate11 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw23 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row233_entry : (originalEntries.drop 233).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate11 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw23 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row233_binding : (data.drop 233).take 1 = (originalEntries.drop 233).take 1 :=
  row233_view.trans (row233_source.trans row233_entry.symm)

numeric_data_binding row234_view : (data.drop 234).take 1 = (data233.drop 1).take 1

numeric_data_binding row234_source : (data233.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate12 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw26 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row234_entry : (originalEntries.drop 234).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate12 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw26 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row234_binding : (data.drop 234).take 1 = (originalEntries.drop 234).take 1 :=
  row234_view.trans (row234_source.trans row234_entry.symm)

numeric_data_binding row235_view : (data.drop 235).take 1 = (data233.drop 2).take 1

numeric_data_binding row235_source : (data233.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate13 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw27 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row235_entry : (originalEntries.drop 235).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate13 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw27 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row235_binding : (data.drop 235).take 1 = (originalEntries.drop 235).take 1 :=
  row235_view.trans (row235_source.trans row235_entry.symm)

numeric_data_binding row236_view : (data.drop 236).take 1 = (data233.drop 3).take 1

numeric_data_binding row236_source : (data233.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate14 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw30 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row236_entry : (originalEntries.drop 236).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate14 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw30 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row236_binding : (data.drop 236).take 1 = (originalEntries.drop 236).take 1 :=
  row236_view.trans (row236_source.trans row236_entry.symm)

numeric_data_binding row237_view : (data.drop 237).take 1 = (data237.drop 0).take 1

numeric_data_binding row237_source : (data237.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate15 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[15]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw31 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row237_entry : (originalEntries.drop 237).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate15 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[15]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw31 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row237_binding : (data.drop 237).take 1 = (originalEntries.drop 237).take 1 :=
  row237_view.trans (row237_source.trans row237_entry.symm)

numeric_data_binding row238_view : (data.drop 238).take 1 = (data237.drop 1).take 1

numeric_data_binding row238_source : (data237.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate16 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[16]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw34 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row238_entry : (originalEntries.drop 238).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate16 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[16]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw34 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row238_binding : (data.drop 238).take 1 = (originalEntries.drop 238).take 1 :=
  row238_view.trans (row238_source.trans row238_entry.symm)

numeric_data_binding row239_view : (data.drop 239).take 1 = (data237.drop 2).take 1

numeric_data_binding row239_source : (data237.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate17 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[17]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw35 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row239_entry : (originalEntries.drop 239).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate17 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[17]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw35 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row239_binding : (data.drop 239).take 1 = (originalEntries.drop 239).take 1 :=
  row239_view.trans (row239_source.trans row239_entry.symm)

numeric_data_binding row240_view : (data.drop 240).take 1 = (data237.drop 3).take 1

numeric_data_binding row240_source : (data237.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate18 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[18]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw38 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row240_entry : (originalEntries.drop 240).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate18 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[18]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw38 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row240_binding : (data.drop 240).take 1 = (originalEntries.drop 240).take 1 :=
  row240_view.trans (row240_source.trans row240_entry.symm)

numeric_data_binding row241_view : (data.drop 241).take 1 = (data241.drop 0).take 1

numeric_data_binding row241_source : (data241.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate19 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[19]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw39 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row241_entry : (originalEntries.drop 241).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate19 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[19]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw39 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row241_binding : (data.drop 241).take 1 = (originalEntries.drop 241).take 1 :=
  row241_view.trans (row241_source.trans row241_entry.symm)

numeric_data_binding row242_view : (data.drop 242).take 1 = (data241.drop 1).take 1

numeric_data_binding row242_source : (data241.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate20 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[20]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw42 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row242_entry : (originalEntries.drop 242).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate20 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[20]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw42 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row242_binding : (data.drop 242).take 1 = (originalEntries.drop 242).take 1 :=
  row242_view.trans (row242_source.trans row242_entry.symm)

numeric_data_binding row243_view : (data.drop 243).take 1 = (data241.drop 2).take 1

numeric_data_binding row243_source : (data241.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate21 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[21]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw43 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row243_entry : (originalEntries.drop 243).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate21 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[21]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw43 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row243_binding : (data.drop 243).take 1 = (originalEntries.drop 243).take 1 :=
  row243_view.trans (row243_source.trans row243_entry.symm)

numeric_data_binding row244_view : (data.drop 244).take 1 = (data241.drop 3).take 1

numeric_data_binding row244_source : (data241.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate22 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[22]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw46 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row244_entry : (originalEntries.drop 244).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate22 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[22]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw46 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row244_binding : (data.drop 244).take 1 = (originalEntries.drop 244).take 1 :=
  row244_view.trans (row244_source.trans row244_entry.symm)

numeric_data_binding row245_view : (data.drop 245).take 1 = (data245.drop 0).take 1

numeric_data_binding row245_source : (data245.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate23 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[23]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw47 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row245_entry : (originalEntries.drop 245).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate23 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[23]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw47 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row245_binding : (data.drop 245).take 1 = (originalEntries.drop 245).take 1 :=
  row245_view.trans (row245_source.trans row245_entry.symm)

numeric_data_binding row246_view : (data.drop 246).take 1 = (data245.drop 1).take 1

numeric_data_binding row246_source : (data245.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate24 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[24]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw50 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row246_entry : (originalEntries.drop 246).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate24 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[24]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw50 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row246_binding : (data.drop 246).take 1 = (originalEntries.drop 246).take 1 :=
  row246_view.trans (row246_source.trans row246_entry.symm)

numeric_data_binding row247_view : (data.drop 247).take 1 = (data245.drop 2).take 1

numeric_data_binding row247_source : (data245.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate25 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[25]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw51 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row247_entry : (originalEntries.drop 247).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate25 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[25]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw51 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row247_binding : (data.drop 247).take 1 = (originalEntries.drop 247).take 1 :=
  row247_view.trans (row247_source.trans row247_entry.symm)

numeric_data_binding row248_view : (data.drop 248).take 1 = (data245.drop 3).take 1

numeric_data_binding row248_source : (data245.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate26 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[26]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw54 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row248_entry : (originalEntries.drop 248).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate26 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[26]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw54 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row248_binding : (data.drop 248).take 1 = (originalEntries.drop 248).take 1 :=
  row248_view.trans (row248_source.trans row248_entry.symm)

numeric_data_binding row249_view : (data.drop 249).take 1 = (data249.drop 0).take 1

numeric_data_binding row249_source : (data249.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate27 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[27]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw55 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row249_entry : (originalEntries.drop 249).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate27 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[27]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw55 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row249_binding : (data.drop 249).take 1 = (originalEntries.drop 249).take 1 :=
  row249_view.trans (row249_source.trans row249_entry.symm)

numeric_data_binding row250_view : (data.drop 250).take 1 = (data249.drop 1).take 1

numeric_data_binding row250_source : (data249.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate28 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[28]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw58 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row250_entry : (originalEntries.drop 250).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate28 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[28]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw58 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row250_binding : (data.drop 250).take 1 = (originalEntries.drop 250).take 1 :=
  row250_view.trans (row250_source.trans row250_entry.symm)

numeric_data_binding row251_view : (data.drop 251).take 1 = (data249.drop 2).take 1

numeric_data_binding row251_source : (data249.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate29 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[29]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw59 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row251_entry : (originalEntries.drop 251).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate29 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[29]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw59 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row251_binding : (data.drop 251).take 1 = (originalEntries.drop 251).take 1 :=
  row251_view.trans (row251_source.trans row251_entry.symm)

numeric_data_binding row252_view : (data.drop 252).take 1 = (data249.drop 3).take 1

numeric_data_binding row252_source : (data249.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate30 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[30]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw62 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row252_entry : (originalEntries.drop 252).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate30 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[30]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw62 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row252_binding : (data.drop 252).take 1 = (originalEntries.drop 252).take 1 :=
  row252_view.trans (row252_source.trans row252_entry.symm)

numeric_data_binding row253_view : (data.drop 253).take 1 = (data253.drop 0).take 1

numeric_data_binding row253_source : (data253.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate31 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[31]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw63 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row253_entry : (originalEntries.drop 253).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate31 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[31]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw63 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row253_binding : (data.drop 253).take 1 = (originalEntries.drop 253).take 1 :=
  row253_view.trans (row253_source.trans row253_entry.symm)

numeric_data_binding row254_view : (data.drop 254).take 1 = (data253.drop 1).take 1

numeric_data_binding row254_source : (data253.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate32 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[32]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw66 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row254_entry : (originalEntries.drop 254).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate32 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[32]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw66 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row254_binding : (data.drop 254).take 1 = (originalEntries.drop 254).take 1 :=
  row254_view.trans (row254_source.trans row254_entry.symm)

numeric_data_binding row255_view : (data.drop 255).take 1 = (data253.drop 2).take 1

numeric_data_binding row255_source : (data253.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate33 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[33]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw67 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row255_entry : (originalEntries.drop 255).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate33 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[33]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw67 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row255_binding : (data.drop 255).take 1 = (originalEntries.drop 255).take 1 :=
  row255_view.trans (row255_source.trans row255_entry.symm)

numeric_data_binding row256_view : (data.drop 256).take 1 = (data253.drop 3).take 1

numeric_data_binding row256_source : (data253.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate34 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[34]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw70 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row256_entry : (originalEntries.drop 256).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate34 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[34]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw70 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row256_binding : (data.drop 256).take 1 = (originalEntries.drop 256).take 1 :=
  row256_view.trans (row256_source.trans row256_entry.symm)

numeric_data_binding row257_view : (data.drop 257).take 1 = (data257.drop 0).take 1

numeric_data_binding row257_source : (data257.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate35 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[35]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw71 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row257_entry : (originalEntries.drop 257).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate35 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[35]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw71 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row257_binding : (data.drop 257).take 1 = (originalEntries.drop 257).take 1 :=
  row257_view.trans (row257_source.trans row257_entry.symm)

numeric_data_binding row258_view : (data.drop 258).take 1 = (data257.drop 1).take 1

numeric_data_binding row258_source : (data257.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate36 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[36]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw74 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row258_entry : (originalEntries.drop 258).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate36 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[36]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw74 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row258_binding : (data.drop 258).take 1 = (originalEntries.drop 258).take 1 :=
  row258_view.trans (row258_source.trans row258_entry.symm)

numeric_data_binding row259_view : (data.drop 259).take 1 = (data257.drop 2).take 1

numeric_data_binding row259_source : (data257.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate37 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[37]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw75 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row259_entry : (originalEntries.drop 259).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate37 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[37]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw75 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row259_binding : (data.drop 259).take 1 = (originalEntries.drop 259).take 1 :=
  row259_view.trans (row259_source.trans row259_entry.symm)

numeric_data_binding row260_view : (data.drop 260).take 1 = (data257.drop 3).take 1

numeric_data_binding row260_source : (data257.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate38 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[38]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw78 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row260_entry : (originalEntries.drop 260).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate38 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[38]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw78 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row260_binding : (data.drop 260).take 1 = (originalEntries.drop 260).take 1 :=
  row260_view.trans (row260_source.trans row260_entry.symm)

numeric_data_binding row261_view : (data.drop 261).take 1 = (data261.drop 0).take 1

numeric_data_binding row261_source : (data261.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate39 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[39]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw79 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row261_entry : (originalEntries.drop 261).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate39 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[39]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw79 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row261_binding : (data.drop 261).take 1 = (originalEntries.drop 261).take 1 :=
  row261_view.trans (row261_source.trans row261_entry.symm)

numeric_data_binding row262_view : (data.drop 262).take 1 = (data261.drop 1).take 1

numeric_data_binding row262_source : (data261.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate40 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[40]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw82 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row262_entry : (originalEntries.drop 262).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate40 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[40]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw82 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row262_binding : (data.drop 262).take 1 = (originalEntries.drop 262).take 1 :=
  row262_view.trans (row262_source.trans row262_entry.symm)

numeric_data_binding row263_view : (data.drop 263).take 1 = (data261.drop 2).take 1

numeric_data_binding row263_source : (data261.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate41 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[41]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw83 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row263_entry : (originalEntries.drop 263).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate41 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[41]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw83 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row263_binding : (data.drop 263).take 1 = (originalEntries.drop 263).take 1 :=
  row263_view.trans (row263_source.trans row263_entry.symm)

numeric_data_binding row264_view : (data.drop 264).take 1 = (data261.drop 3).take 1

numeric_data_binding row264_source : (data261.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate42 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[42]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw86 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row264_entry : (originalEntries.drop 264).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate42 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[42]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw86 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row264_binding : (data.drop 264).take 1 = (originalEntries.drop 264).take 1 :=
  row264_view.trans (row264_source.trans row264_entry.symm)

numeric_data_binding row265_view : (data.drop 265).take 1 = (data265.drop 0).take 1

numeric_data_binding row265_source : (data265.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate43 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[43]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw87 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

numeric_data_binding row265_entry : (originalEntries.drop 265).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteCertificate43 (((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows)[43]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.MemoryNative.BlakeRoundCached.native.raw87 Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing)]

theorem row265_binding : (data.drop 265).take 1 = (originalEntries.drop 265).take 1 :=
  row265_view.trans (row265_source.trans row265_entry.symm)

numeric_data_binding row266_view : (data.drop 266).take 1 = (data265.drop 1).take 1

numeric_data_binding row266_source : (data265.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing [(GKRAddress.InnerLayer 6 0)])]

numeric_data_binding row266_entry : (originalEntries.drop 266).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing [(GKRAddress.InnerLayer 6 0)])]

theorem row266_binding : (data.drop 266).take 1 = (originalEntries.drop 266).take 1 :=
  row266_view.trans (row266_source.trans row266_entry.symm)

theorem entriesNode0_2 : (data.drop 0).take 2 = (originalEntries.drop 0).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 1 1 1 2 rfl rfl row0_binding row1_binding

theorem entriesNode2_2 : (data.drop 2).take 2 = (originalEntries.drop 2).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 2 1 1 3 2 rfl rfl row2_binding row3_binding

theorem entriesNode0_4 : (data.drop 0).take 4 = (originalEntries.drop 0).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 2 2 2 4 rfl rfl entriesNode0_2 entriesNode2_2

theorem entriesNode4_2 : (data.drop 4).take 2 = (originalEntries.drop 4).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 4 1 1 5 2 rfl rfl row4_binding row5_binding

theorem entriesNode6_2 : (data.drop 6).take 2 = (originalEntries.drop 6).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 6 1 1 7 2 rfl rfl row6_binding row7_binding

theorem entriesNode4_4 : (data.drop 4).take 4 = (originalEntries.drop 4).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 4 2 2 6 4 rfl rfl entriesNode4_2 entriesNode6_2

theorem entriesNode0_8 : (data.drop 0).take 8 = (originalEntries.drop 0).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 4 4 4 8 rfl rfl entriesNode0_4 entriesNode4_4

theorem entriesNode8_2 : (data.drop 8).take 2 = (originalEntries.drop 8).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 8 1 1 9 2 rfl rfl row8_binding row9_binding

theorem entriesNode10_2 : (data.drop 10).take 2 = (originalEntries.drop 10).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 10 1 1 11 2 rfl rfl row10_binding row11_binding

theorem entriesNode8_4 : (data.drop 8).take 4 = (originalEntries.drop 8).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 8 2 2 10 4 rfl rfl entriesNode8_2 entriesNode10_2

theorem entriesNode12_2 : (data.drop 12).take 2 = (originalEntries.drop 12).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 12 1 1 13 2 rfl rfl row12_binding row13_binding

theorem entriesNode14_2 : (data.drop 14).take 2 = (originalEntries.drop 14).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 14 1 1 15 2 rfl rfl row14_binding row15_binding

theorem entriesNode12_4 : (data.drop 12).take 4 = (originalEntries.drop 12).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 12 2 2 14 4 rfl rfl entriesNode12_2 entriesNode14_2

theorem entriesNode8_8 : (data.drop 8).take 8 = (originalEntries.drop 8).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 8 4 4 12 8 rfl rfl entriesNode8_4 entriesNode12_4

theorem entriesNode0_16 : (data.drop 0).take 16 = (originalEntries.drop 0).take 16 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 8 8 8 16 rfl rfl entriesNode0_8 entriesNode8_8

theorem entriesNode16_2 : (data.drop 16).take 2 = (originalEntries.drop 16).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 16 1 1 17 2 rfl rfl row16_binding row17_binding

theorem entriesNode18_2 : (data.drop 18).take 2 = (originalEntries.drop 18).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 18 1 1 19 2 rfl rfl row18_binding row19_binding

theorem entriesNode16_4 : (data.drop 16).take 4 = (originalEntries.drop 16).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 16 2 2 18 4 rfl rfl entriesNode16_2 entriesNode18_2

theorem entriesNode20_2 : (data.drop 20).take 2 = (originalEntries.drop 20).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 20 1 1 21 2 rfl rfl row20_binding row21_binding

theorem entriesNode22_2 : (data.drop 22).take 2 = (originalEntries.drop 22).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 22 1 1 23 2 rfl rfl row22_binding row23_binding

theorem entriesNode20_4 : (data.drop 20).take 4 = (originalEntries.drop 20).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 20 2 2 22 4 rfl rfl entriesNode20_2 entriesNode22_2

theorem entriesNode16_8 : (data.drop 16).take 8 = (originalEntries.drop 16).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 16 4 4 20 8 rfl rfl entriesNode16_4 entriesNode20_4

theorem entriesNode24_2 : (data.drop 24).take 2 = (originalEntries.drop 24).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 24 1 1 25 2 rfl rfl row24_binding row25_binding

theorem entriesNode26_2 : (data.drop 26).take 2 = (originalEntries.drop 26).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 26 1 1 27 2 rfl rfl row26_binding row27_binding

theorem entriesNode24_4 : (data.drop 24).take 4 = (originalEntries.drop 24).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 24 2 2 26 4 rfl rfl entriesNode24_2 entriesNode26_2

theorem entriesNode28_2 : (data.drop 28).take 2 = (originalEntries.drop 28).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 28 1 1 29 2 rfl rfl row28_binding row29_binding

theorem entriesNode31_2 : (data.drop 31).take 2 = (originalEntries.drop 31).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 31 1 1 32 2 rfl rfl row31_binding row32_binding

theorem entriesNode30_3 : (data.drop 30).take 3 = (originalEntries.drop 30).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 30 1 2 31 3 rfl rfl row30_binding entriesNode31_2

theorem entriesNode28_5 : (data.drop 28).take 5 = (originalEntries.drop 28).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 28 2 3 30 5 rfl rfl entriesNode28_2 entriesNode30_3

theorem entriesNode24_9 : (data.drop 24).take 9 = (originalEntries.drop 24).take 9 :=
  NumericWorkerPortChecks.merge_at data originalEntries 24 4 5 28 9 rfl rfl entriesNode24_4 entriesNode28_5

theorem entriesNode16_17 : (data.drop 16).take 17 = (originalEntries.drop 16).take 17 :=
  NumericWorkerPortChecks.merge_at data originalEntries 16 8 9 24 17 rfl rfl entriesNode16_8 entriesNode24_9

theorem entriesNode0_33 : (data.drop 0).take 33 = (originalEntries.drop 0).take 33 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 16 17 16 33 rfl rfl entriesNode0_16 entriesNode16_17

theorem entriesNode33_2 : (data.drop 33).take 2 = (originalEntries.drop 33).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 33 1 1 34 2 rfl rfl row33_binding row34_binding

theorem entriesNode35_2 : (data.drop 35).take 2 = (originalEntries.drop 35).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 35 1 1 36 2 rfl rfl row35_binding row36_binding

theorem entriesNode33_4 : (data.drop 33).take 4 = (originalEntries.drop 33).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 33 2 2 35 4 rfl rfl entriesNode33_2 entriesNode35_2

theorem entriesNode37_2 : (data.drop 37).take 2 = (originalEntries.drop 37).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 37 1 1 38 2 rfl rfl row37_binding row38_binding

theorem entriesNode39_2 : (data.drop 39).take 2 = (originalEntries.drop 39).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 39 1 1 40 2 rfl rfl row39_binding row40_binding

theorem entriesNode37_4 : (data.drop 37).take 4 = (originalEntries.drop 37).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 37 2 2 39 4 rfl rfl entriesNode37_2 entriesNode39_2

theorem entriesNode33_8 : (data.drop 33).take 8 = (originalEntries.drop 33).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 33 4 4 37 8 rfl rfl entriesNode33_4 entriesNode37_4

theorem entriesNode41_2 : (data.drop 41).take 2 = (originalEntries.drop 41).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 41 1 1 42 2 rfl rfl row41_binding row42_binding

theorem entriesNode43_2 : (data.drop 43).take 2 = (originalEntries.drop 43).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 43 1 1 44 2 rfl rfl row43_binding row44_binding

theorem entriesNode41_4 : (data.drop 41).take 4 = (originalEntries.drop 41).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 41 2 2 43 4 rfl rfl entriesNode41_2 entriesNode43_2

theorem entriesNode45_2 : (data.drop 45).take 2 = (originalEntries.drop 45).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 45 1 1 46 2 rfl rfl row45_binding row46_binding

theorem entriesNode47_2 : (data.drop 47).take 2 = (originalEntries.drop 47).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 47 1 1 48 2 rfl rfl row47_binding row48_binding

theorem entriesNode45_4 : (data.drop 45).take 4 = (originalEntries.drop 45).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 45 2 2 47 4 rfl rfl entriesNode45_2 entriesNode47_2

theorem entriesNode41_8 : (data.drop 41).take 8 = (originalEntries.drop 41).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 41 4 4 45 8 rfl rfl entriesNode41_4 entriesNode45_4

theorem entriesNode33_16 : (data.drop 33).take 16 = (originalEntries.drop 33).take 16 :=
  NumericWorkerPortChecks.merge_at data originalEntries 33 8 8 41 16 rfl rfl entriesNode33_8 entriesNode41_8

theorem entriesNode49_2 : (data.drop 49).take 2 = (originalEntries.drop 49).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 49 1 1 50 2 rfl rfl row49_binding row50_binding

theorem entriesNode51_2 : (data.drop 51).take 2 = (originalEntries.drop 51).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 51 1 1 52 2 rfl rfl row51_binding row52_binding

theorem entriesNode49_4 : (data.drop 49).take 4 = (originalEntries.drop 49).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 49 2 2 51 4 rfl rfl entriesNode49_2 entriesNode51_2

theorem entriesNode53_2 : (data.drop 53).take 2 = (originalEntries.drop 53).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 53 1 1 54 2 rfl rfl row53_binding row54_binding

theorem entriesNode55_2 : (data.drop 55).take 2 = (originalEntries.drop 55).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 55 1 1 56 2 rfl rfl row55_binding row56_binding

theorem entriesNode53_4 : (data.drop 53).take 4 = (originalEntries.drop 53).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 53 2 2 55 4 rfl rfl entriesNode53_2 entriesNode55_2

theorem entriesNode49_8 : (data.drop 49).take 8 = (originalEntries.drop 49).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 49 4 4 53 8 rfl rfl entriesNode49_4 entriesNode53_4

theorem entriesNode57_2 : (data.drop 57).take 2 = (originalEntries.drop 57).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 57 1 1 58 2 rfl rfl row57_binding row58_binding

theorem entriesNode59_2 : (data.drop 59).take 2 = (originalEntries.drop 59).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 59 1 1 60 2 rfl rfl row59_binding row60_binding

theorem entriesNode57_4 : (data.drop 57).take 4 = (originalEntries.drop 57).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 57 2 2 59 4 rfl rfl entriesNode57_2 entriesNode59_2

theorem entriesNode61_2 : (data.drop 61).take 2 = (originalEntries.drop 61).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 61 1 1 62 2 rfl rfl row61_binding row62_binding

theorem entriesNode64_2 : (data.drop 64).take 2 = (originalEntries.drop 64).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 64 1 1 65 2 rfl rfl row64_binding row65_binding

theorem entriesNode63_3 : (data.drop 63).take 3 = (originalEntries.drop 63).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 63 1 2 64 3 rfl rfl row63_binding entriesNode64_2

theorem entriesNode61_5 : (data.drop 61).take 5 = (originalEntries.drop 61).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 61 2 3 63 5 rfl rfl entriesNode61_2 entriesNode63_3

theorem entriesNode57_9 : (data.drop 57).take 9 = (originalEntries.drop 57).take 9 :=
  NumericWorkerPortChecks.merge_at data originalEntries 57 4 5 61 9 rfl rfl entriesNode57_4 entriesNode61_5

theorem entriesNode49_17 : (data.drop 49).take 17 = (originalEntries.drop 49).take 17 :=
  NumericWorkerPortChecks.merge_at data originalEntries 49 8 9 57 17 rfl rfl entriesNode49_8 entriesNode57_9

theorem entriesNode33_33 : (data.drop 33).take 33 = (originalEntries.drop 33).take 33 :=
  NumericWorkerPortChecks.merge_at data originalEntries 33 16 17 49 33 rfl rfl entriesNode33_16 entriesNode49_17

theorem entriesNode0_66 : (data.drop 0).take 66 = (originalEntries.drop 0).take 66 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 33 33 33 66 rfl rfl entriesNode0_33 entriesNode33_33

theorem entriesNode66_2 : (data.drop 66).take 2 = (originalEntries.drop 66).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 66 1 1 67 2 rfl rfl row66_binding row67_binding

theorem entriesNode68_2 : (data.drop 68).take 2 = (originalEntries.drop 68).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 68 1 1 69 2 rfl rfl row68_binding row69_binding

theorem entriesNode66_4 : (data.drop 66).take 4 = (originalEntries.drop 66).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 66 2 2 68 4 rfl rfl entriesNode66_2 entriesNode68_2

theorem entriesNode70_2 : (data.drop 70).take 2 = (originalEntries.drop 70).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 70 1 1 71 2 rfl rfl row70_binding row71_binding

theorem entriesNode72_2 : (data.drop 72).take 2 = (originalEntries.drop 72).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 72 1 1 73 2 rfl rfl row72_binding row73_binding

theorem entriesNode70_4 : (data.drop 70).take 4 = (originalEntries.drop 70).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 70 2 2 72 4 rfl rfl entriesNode70_2 entriesNode72_2

theorem entriesNode66_8 : (data.drop 66).take 8 = (originalEntries.drop 66).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 66 4 4 70 8 rfl rfl entriesNode66_4 entriesNode70_4

theorem entriesNode74_2 : (data.drop 74).take 2 = (originalEntries.drop 74).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 74 1 1 75 2 rfl rfl row74_binding row75_binding

theorem entriesNode76_2 : (data.drop 76).take 2 = (originalEntries.drop 76).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 76 1 1 77 2 rfl rfl row76_binding row77_binding

theorem entriesNode74_4 : (data.drop 74).take 4 = (originalEntries.drop 74).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 74 2 2 76 4 rfl rfl entriesNode74_2 entriesNode76_2

theorem entriesNode78_2 : (data.drop 78).take 2 = (originalEntries.drop 78).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 78 1 1 79 2 rfl rfl row78_binding row79_binding

theorem entriesNode80_2 : (data.drop 80).take 2 = (originalEntries.drop 80).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 80 1 1 81 2 rfl rfl row80_binding row81_binding

theorem entriesNode78_4 : (data.drop 78).take 4 = (originalEntries.drop 78).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 78 2 2 80 4 rfl rfl entriesNode78_2 entriesNode80_2

theorem entriesNode74_8 : (data.drop 74).take 8 = (originalEntries.drop 74).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 74 4 4 78 8 rfl rfl entriesNode74_4 entriesNode78_4

theorem entriesNode66_16 : (data.drop 66).take 16 = (originalEntries.drop 66).take 16 :=
  NumericWorkerPortChecks.merge_at data originalEntries 66 8 8 74 16 rfl rfl entriesNode66_8 entriesNode74_8

theorem entriesNode82_2 : (data.drop 82).take 2 = (originalEntries.drop 82).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 82 1 1 83 2 rfl rfl row82_binding row83_binding

theorem entriesNode84_2 : (data.drop 84).take 2 = (originalEntries.drop 84).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 84 1 1 85 2 rfl rfl row84_binding row85_binding

theorem entriesNode82_4 : (data.drop 82).take 4 = (originalEntries.drop 82).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 82 2 2 84 4 rfl rfl entriesNode82_2 entriesNode84_2

theorem entriesNode86_2 : (data.drop 86).take 2 = (originalEntries.drop 86).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 86 1 1 87 2 rfl rfl row86_binding row87_binding

theorem entriesNode88_2 : (data.drop 88).take 2 = (originalEntries.drop 88).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 88 1 1 89 2 rfl rfl row88_binding row89_binding

theorem entriesNode86_4 : (data.drop 86).take 4 = (originalEntries.drop 86).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 86 2 2 88 4 rfl rfl entriesNode86_2 entriesNode88_2

theorem entriesNode82_8 : (data.drop 82).take 8 = (originalEntries.drop 82).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 82 4 4 86 8 rfl rfl entriesNode82_4 entriesNode86_4

theorem entriesNode90_2 : (data.drop 90).take 2 = (originalEntries.drop 90).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 90 1 1 91 2 rfl rfl row90_binding row91_binding

theorem entriesNode92_2 : (data.drop 92).take 2 = (originalEntries.drop 92).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 92 1 1 93 2 rfl rfl row92_binding row93_binding

theorem entriesNode90_4 : (data.drop 90).take 4 = (originalEntries.drop 90).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 90 2 2 92 4 rfl rfl entriesNode90_2 entriesNode92_2

theorem entriesNode94_2 : (data.drop 94).take 2 = (originalEntries.drop 94).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 94 1 1 95 2 rfl rfl row94_binding row95_binding

theorem entriesNode97_2 : (data.drop 97).take 2 = (originalEntries.drop 97).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 97 1 1 98 2 rfl rfl row97_binding row98_binding

theorem entriesNode96_3 : (data.drop 96).take 3 = (originalEntries.drop 96).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 96 1 2 97 3 rfl rfl row96_binding entriesNode97_2

theorem entriesNode94_5 : (data.drop 94).take 5 = (originalEntries.drop 94).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 94 2 3 96 5 rfl rfl entriesNode94_2 entriesNode96_3

theorem entriesNode90_9 : (data.drop 90).take 9 = (originalEntries.drop 90).take 9 :=
  NumericWorkerPortChecks.merge_at data originalEntries 90 4 5 94 9 rfl rfl entriesNode90_4 entriesNode94_5

theorem entriesNode82_17 : (data.drop 82).take 17 = (originalEntries.drop 82).take 17 :=
  NumericWorkerPortChecks.merge_at data originalEntries 82 8 9 90 17 rfl rfl entriesNode82_8 entriesNode90_9

theorem entriesNode66_33 : (data.drop 66).take 33 = (originalEntries.drop 66).take 33 :=
  NumericWorkerPortChecks.merge_at data originalEntries 66 16 17 82 33 rfl rfl entriesNode66_16 entriesNode82_17

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

theorem entriesNode107_2 : (data.drop 107).take 2 = (originalEntries.drop 107).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 107 1 1 108 2 rfl rfl row107_binding row108_binding

theorem entriesNode109_2 : (data.drop 109).take 2 = (originalEntries.drop 109).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 109 1 1 110 2 rfl rfl row109_binding row110_binding

theorem entriesNode107_4 : (data.drop 107).take 4 = (originalEntries.drop 107).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 107 2 2 109 4 rfl rfl entriesNode107_2 entriesNode109_2

theorem entriesNode111_2 : (data.drop 111).take 2 = (originalEntries.drop 111).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 111 1 1 112 2 rfl rfl row111_binding row112_binding

theorem entriesNode114_2 : (data.drop 114).take 2 = (originalEntries.drop 114).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 114 1 1 115 2 rfl rfl row114_binding row115_binding

theorem entriesNode113_3 : (data.drop 113).take 3 = (originalEntries.drop 113).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 113 1 2 114 3 rfl rfl row113_binding entriesNode114_2

theorem entriesNode111_5 : (data.drop 111).take 5 = (originalEntries.drop 111).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 111 2 3 113 5 rfl rfl entriesNode111_2 entriesNode113_3

theorem entriesNode107_9 : (data.drop 107).take 9 = (originalEntries.drop 107).take 9 :=
  NumericWorkerPortChecks.merge_at data originalEntries 107 4 5 111 9 rfl rfl entriesNode107_4 entriesNode111_5

theorem entriesNode99_17 : (data.drop 99).take 17 = (originalEntries.drop 99).take 17 :=
  NumericWorkerPortChecks.merge_at data originalEntries 99 8 9 107 17 rfl rfl entriesNode99_8 entriesNode107_9

theorem entriesNode116_2 : (data.drop 116).take 2 = (originalEntries.drop 116).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 116 1 1 117 2 rfl rfl row116_binding row117_binding

theorem entriesNode118_2 : (data.drop 118).take 2 = (originalEntries.drop 118).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 118 1 1 119 2 rfl rfl row118_binding row119_binding

theorem entriesNode116_4 : (data.drop 116).take 4 = (originalEntries.drop 116).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 116 2 2 118 4 rfl rfl entriesNode116_2 entriesNode118_2

theorem entriesNode120_2 : (data.drop 120).take 2 = (originalEntries.drop 120).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 120 1 1 121 2 rfl rfl row120_binding row121_binding

theorem entriesNode122_2 : (data.drop 122).take 2 = (originalEntries.drop 122).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 122 1 1 123 2 rfl rfl row122_binding row123_binding

theorem entriesNode120_4 : (data.drop 120).take 4 = (originalEntries.drop 120).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 120 2 2 122 4 rfl rfl entriesNode120_2 entriesNode122_2

theorem entriesNode116_8 : (data.drop 116).take 8 = (originalEntries.drop 116).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 116 4 4 120 8 rfl rfl entriesNode116_4 entriesNode120_4

theorem entriesNode124_2 : (data.drop 124).take 2 = (originalEntries.drop 124).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 124 1 1 125 2 rfl rfl row124_binding row125_binding

theorem entriesNode126_2 : (data.drop 126).take 2 = (originalEntries.drop 126).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 126 1 1 127 2 rfl rfl row126_binding row127_binding

theorem entriesNode124_4 : (data.drop 124).take 4 = (originalEntries.drop 124).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 124 2 2 126 4 rfl rfl entriesNode124_2 entriesNode126_2

theorem entriesNode128_2 : (data.drop 128).take 2 = (originalEntries.drop 128).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 128 1 1 129 2 rfl rfl row128_binding row129_binding

theorem entriesNode131_2 : (data.drop 131).take 2 = (originalEntries.drop 131).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 131 1 1 132 2 rfl rfl row131_binding row132_binding

theorem entriesNode130_3 : (data.drop 130).take 3 = (originalEntries.drop 130).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 130 1 2 131 3 rfl rfl row130_binding entriesNode131_2

theorem entriesNode128_5 : (data.drop 128).take 5 = (originalEntries.drop 128).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 128 2 3 130 5 rfl rfl entriesNode128_2 entriesNode130_3

theorem entriesNode124_9 : (data.drop 124).take 9 = (originalEntries.drop 124).take 9 :=
  NumericWorkerPortChecks.merge_at data originalEntries 124 4 5 128 9 rfl rfl entriesNode124_4 entriesNode128_5

theorem entriesNode116_17 : (data.drop 116).take 17 = (originalEntries.drop 116).take 17 :=
  NumericWorkerPortChecks.merge_at data originalEntries 116 8 9 124 17 rfl rfl entriesNode116_8 entriesNode124_9

theorem entriesNode99_34 : (data.drop 99).take 34 = (originalEntries.drop 99).take 34 :=
  NumericWorkerPortChecks.merge_at data originalEntries 99 17 17 116 34 rfl rfl entriesNode99_17 entriesNode116_17

theorem entriesNode66_67 : (data.drop 66).take 67 = (originalEntries.drop 66).take 67 :=
  NumericWorkerPortChecks.merge_at data originalEntries 66 33 34 99 67 rfl rfl entriesNode66_33 entriesNode99_34

theorem entriesNode0_133 : (data.drop 0).take 133 = (originalEntries.drop 0).take 133 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 66 67 66 133 rfl rfl entriesNode0_66 entriesNode66_67

theorem entriesNode133_2 : (data.drop 133).take 2 = (originalEntries.drop 133).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 133 1 1 134 2 rfl rfl row133_binding row134_binding

theorem entriesNode135_2 : (data.drop 135).take 2 = (originalEntries.drop 135).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 135 1 1 136 2 rfl rfl row135_binding row136_binding

theorem entriesNode133_4 : (data.drop 133).take 4 = (originalEntries.drop 133).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 133 2 2 135 4 rfl rfl entriesNode133_2 entriesNode135_2

theorem entriesNode137_2 : (data.drop 137).take 2 = (originalEntries.drop 137).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 137 1 1 138 2 rfl rfl row137_binding row138_binding

theorem entriesNode139_2 : (data.drop 139).take 2 = (originalEntries.drop 139).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 139 1 1 140 2 rfl rfl row139_binding row140_binding

theorem entriesNode137_4 : (data.drop 137).take 4 = (originalEntries.drop 137).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 137 2 2 139 4 rfl rfl entriesNode137_2 entriesNode139_2

theorem entriesNode133_8 : (data.drop 133).take 8 = (originalEntries.drop 133).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 133 4 4 137 8 rfl rfl entriesNode133_4 entriesNode137_4

theorem entriesNode141_2 : (data.drop 141).take 2 = (originalEntries.drop 141).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 141 1 1 142 2 rfl rfl row141_binding row142_binding

theorem entriesNode143_2 : (data.drop 143).take 2 = (originalEntries.drop 143).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 143 1 1 144 2 rfl rfl row143_binding row144_binding

theorem entriesNode141_4 : (data.drop 141).take 4 = (originalEntries.drop 141).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 141 2 2 143 4 rfl rfl entriesNode141_2 entriesNode143_2

theorem entriesNode145_2 : (data.drop 145).take 2 = (originalEntries.drop 145).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 145 1 1 146 2 rfl rfl row145_binding row146_binding

theorem entriesNode147_2 : (data.drop 147).take 2 = (originalEntries.drop 147).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 147 1 1 148 2 rfl rfl row147_binding row148_binding

theorem entriesNode145_4 : (data.drop 145).take 4 = (originalEntries.drop 145).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 145 2 2 147 4 rfl rfl entriesNode145_2 entriesNode147_2

theorem entriesNode141_8 : (data.drop 141).take 8 = (originalEntries.drop 141).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 141 4 4 145 8 rfl rfl entriesNode141_4 entriesNode145_4

theorem entriesNode133_16 : (data.drop 133).take 16 = (originalEntries.drop 133).take 16 :=
  NumericWorkerPortChecks.merge_at data originalEntries 133 8 8 141 16 rfl rfl entriesNode133_8 entriesNode141_8

theorem entriesNode149_2 : (data.drop 149).take 2 = (originalEntries.drop 149).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 149 1 1 150 2 rfl rfl row149_binding row150_binding

theorem entriesNode151_2 : (data.drop 151).take 2 = (originalEntries.drop 151).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 151 1 1 152 2 rfl rfl row151_binding row152_binding

theorem entriesNode149_4 : (data.drop 149).take 4 = (originalEntries.drop 149).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 149 2 2 151 4 rfl rfl entriesNode149_2 entriesNode151_2

theorem entriesNode153_2 : (data.drop 153).take 2 = (originalEntries.drop 153).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 153 1 1 154 2 rfl rfl row153_binding row154_binding

theorem entriesNode155_2 : (data.drop 155).take 2 = (originalEntries.drop 155).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 155 1 1 156 2 rfl rfl row155_binding row156_binding

theorem entriesNode153_4 : (data.drop 153).take 4 = (originalEntries.drop 153).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 153 2 2 155 4 rfl rfl entriesNode153_2 entriesNode155_2

theorem entriesNode149_8 : (data.drop 149).take 8 = (originalEntries.drop 149).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 149 4 4 153 8 rfl rfl entriesNode149_4 entriesNode153_4

theorem entriesNode157_2 : (data.drop 157).take 2 = (originalEntries.drop 157).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 157 1 1 158 2 rfl rfl row157_binding row158_binding

theorem entriesNode159_2 : (data.drop 159).take 2 = (originalEntries.drop 159).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 159 1 1 160 2 rfl rfl row159_binding row160_binding

theorem entriesNode157_4 : (data.drop 157).take 4 = (originalEntries.drop 157).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 157 2 2 159 4 rfl rfl entriesNode157_2 entriesNode159_2

theorem entriesNode161_2 : (data.drop 161).take 2 = (originalEntries.drop 161).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 161 1 1 162 2 rfl rfl row161_binding row162_binding

theorem entriesNode164_2 : (data.drop 164).take 2 = (originalEntries.drop 164).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 164 1 1 165 2 rfl rfl row164_binding row165_binding

theorem entriesNode163_3 : (data.drop 163).take 3 = (originalEntries.drop 163).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 163 1 2 164 3 rfl rfl row163_binding entriesNode164_2

theorem entriesNode161_5 : (data.drop 161).take 5 = (originalEntries.drop 161).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 161 2 3 163 5 rfl rfl entriesNode161_2 entriesNode163_3

theorem entriesNode157_9 : (data.drop 157).take 9 = (originalEntries.drop 157).take 9 :=
  NumericWorkerPortChecks.merge_at data originalEntries 157 4 5 161 9 rfl rfl entriesNode157_4 entriesNode161_5

theorem entriesNode149_17 : (data.drop 149).take 17 = (originalEntries.drop 149).take 17 :=
  NumericWorkerPortChecks.merge_at data originalEntries 149 8 9 157 17 rfl rfl entriesNode149_8 entriesNode157_9

theorem entriesNode133_33 : (data.drop 133).take 33 = (originalEntries.drop 133).take 33 :=
  NumericWorkerPortChecks.merge_at data originalEntries 133 16 17 149 33 rfl rfl entriesNode133_16 entriesNode149_17

theorem entriesNode166_2 : (data.drop 166).take 2 = (originalEntries.drop 166).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 166 1 1 167 2 rfl rfl row166_binding row167_binding

theorem entriesNode168_2 : (data.drop 168).take 2 = (originalEntries.drop 168).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 168 1 1 169 2 rfl rfl row168_binding row169_binding

theorem entriesNode166_4 : (data.drop 166).take 4 = (originalEntries.drop 166).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 166 2 2 168 4 rfl rfl entriesNode166_2 entriesNode168_2

theorem entriesNode170_2 : (data.drop 170).take 2 = (originalEntries.drop 170).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 170 1 1 171 2 rfl rfl row170_binding row171_binding

theorem entriesNode172_2 : (data.drop 172).take 2 = (originalEntries.drop 172).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 172 1 1 173 2 rfl rfl row172_binding row173_binding

theorem entriesNode170_4 : (data.drop 170).take 4 = (originalEntries.drop 170).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 170 2 2 172 4 rfl rfl entriesNode170_2 entriesNode172_2

theorem entriesNode166_8 : (data.drop 166).take 8 = (originalEntries.drop 166).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 166 4 4 170 8 rfl rfl entriesNode166_4 entriesNode170_4

theorem entriesNode174_2 : (data.drop 174).take 2 = (originalEntries.drop 174).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 174 1 1 175 2 rfl rfl row174_binding row175_binding

theorem entriesNode176_2 : (data.drop 176).take 2 = (originalEntries.drop 176).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 176 1 1 177 2 rfl rfl row176_binding row177_binding

theorem entriesNode174_4 : (data.drop 174).take 4 = (originalEntries.drop 174).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 174 2 2 176 4 rfl rfl entriesNode174_2 entriesNode176_2

theorem entriesNode178_2 : (data.drop 178).take 2 = (originalEntries.drop 178).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 178 1 1 179 2 rfl rfl row178_binding row179_binding

theorem entriesNode181_2 : (data.drop 181).take 2 = (originalEntries.drop 181).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 181 1 1 182 2 rfl rfl row181_binding row182_binding

theorem entriesNode180_3 : (data.drop 180).take 3 = (originalEntries.drop 180).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 180 1 2 181 3 rfl rfl row180_binding entriesNode181_2

theorem entriesNode178_5 : (data.drop 178).take 5 = (originalEntries.drop 178).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 178 2 3 180 5 rfl rfl entriesNode178_2 entriesNode180_3

theorem entriesNode174_9 : (data.drop 174).take 9 = (originalEntries.drop 174).take 9 :=
  NumericWorkerPortChecks.merge_at data originalEntries 174 4 5 178 9 rfl rfl entriesNode174_4 entriesNode178_5

theorem entriesNode166_17 : (data.drop 166).take 17 = (originalEntries.drop 166).take 17 :=
  NumericWorkerPortChecks.merge_at data originalEntries 166 8 9 174 17 rfl rfl entriesNode166_8 entriesNode174_9

theorem entriesNode183_2 : (data.drop 183).take 2 = (originalEntries.drop 183).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 183 1 1 184 2 rfl rfl row183_binding row184_binding

theorem entriesNode185_2 : (data.drop 185).take 2 = (originalEntries.drop 185).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 185 1 1 186 2 rfl rfl row185_binding row186_binding

theorem entriesNode183_4 : (data.drop 183).take 4 = (originalEntries.drop 183).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 183 2 2 185 4 rfl rfl entriesNode183_2 entriesNode185_2

theorem entriesNode187_2 : (data.drop 187).take 2 = (originalEntries.drop 187).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 187 1 1 188 2 rfl rfl row187_binding row188_binding

theorem entriesNode189_2 : (data.drop 189).take 2 = (originalEntries.drop 189).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 189 1 1 190 2 rfl rfl row189_binding row190_binding

theorem entriesNode187_4 : (data.drop 187).take 4 = (originalEntries.drop 187).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 187 2 2 189 4 rfl rfl entriesNode187_2 entriesNode189_2

theorem entriesNode183_8 : (data.drop 183).take 8 = (originalEntries.drop 183).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 183 4 4 187 8 rfl rfl entriesNode183_4 entriesNode187_4

theorem entriesNode191_2 : (data.drop 191).take 2 = (originalEntries.drop 191).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 191 1 1 192 2 rfl rfl row191_binding row192_binding

theorem entriesNode193_2 : (data.drop 193).take 2 = (originalEntries.drop 193).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 193 1 1 194 2 rfl rfl row193_binding row194_binding

theorem entriesNode191_4 : (data.drop 191).take 4 = (originalEntries.drop 191).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 191 2 2 193 4 rfl rfl entriesNode191_2 entriesNode193_2

theorem entriesNode195_2 : (data.drop 195).take 2 = (originalEntries.drop 195).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 195 1 1 196 2 rfl rfl row195_binding row196_binding

theorem entriesNode198_2 : (data.drop 198).take 2 = (originalEntries.drop 198).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 198 1 1 199 2 rfl rfl row198_binding row199_binding

theorem entriesNode197_3 : (data.drop 197).take 3 = (originalEntries.drop 197).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 197 1 2 198 3 rfl rfl row197_binding entriesNode198_2

theorem entriesNode195_5 : (data.drop 195).take 5 = (originalEntries.drop 195).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 195 2 3 197 5 rfl rfl entriesNode195_2 entriesNode197_3

theorem entriesNode191_9 : (data.drop 191).take 9 = (originalEntries.drop 191).take 9 :=
  NumericWorkerPortChecks.merge_at data originalEntries 191 4 5 195 9 rfl rfl entriesNode191_4 entriesNode195_5

theorem entriesNode183_17 : (data.drop 183).take 17 = (originalEntries.drop 183).take 17 :=
  NumericWorkerPortChecks.merge_at data originalEntries 183 8 9 191 17 rfl rfl entriesNode183_8 entriesNode191_9

theorem entriesNode166_34 : (data.drop 166).take 34 = (originalEntries.drop 166).take 34 :=
  NumericWorkerPortChecks.merge_at data originalEntries 166 17 17 183 34 rfl rfl entriesNode166_17 entriesNode183_17

theorem entriesNode133_67 : (data.drop 133).take 67 = (originalEntries.drop 133).take 67 :=
  NumericWorkerPortChecks.merge_at data originalEntries 133 33 34 166 67 rfl rfl entriesNode133_33 entriesNode166_34

theorem entriesNode200_2 : (data.drop 200).take 2 = (originalEntries.drop 200).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 200 1 1 201 2 rfl rfl row200_binding row201_binding

theorem entriesNode202_2 : (data.drop 202).take 2 = (originalEntries.drop 202).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 202 1 1 203 2 rfl rfl row202_binding row203_binding

theorem entriesNode200_4 : (data.drop 200).take 4 = (originalEntries.drop 200).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 200 2 2 202 4 rfl rfl entriesNode200_2 entriesNode202_2

theorem entriesNode204_2 : (data.drop 204).take 2 = (originalEntries.drop 204).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 204 1 1 205 2 rfl rfl row204_binding row205_binding

theorem entriesNode206_2 : (data.drop 206).take 2 = (originalEntries.drop 206).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 206 1 1 207 2 rfl rfl row206_binding row207_binding

theorem entriesNode204_4 : (data.drop 204).take 4 = (originalEntries.drop 204).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 204 2 2 206 4 rfl rfl entriesNode204_2 entriesNode206_2

theorem entriesNode200_8 : (data.drop 200).take 8 = (originalEntries.drop 200).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 200 4 4 204 8 rfl rfl entriesNode200_4 entriesNode204_4

theorem entriesNode208_2 : (data.drop 208).take 2 = (originalEntries.drop 208).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 208 1 1 209 2 rfl rfl row208_binding row209_binding

theorem entriesNode210_2 : (data.drop 210).take 2 = (originalEntries.drop 210).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 210 1 1 211 2 rfl rfl row210_binding row211_binding

theorem entriesNode208_4 : (data.drop 208).take 4 = (originalEntries.drop 208).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 208 2 2 210 4 rfl rfl entriesNode208_2 entriesNode210_2

theorem entriesNode212_2 : (data.drop 212).take 2 = (originalEntries.drop 212).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 212 1 1 213 2 rfl rfl row212_binding row213_binding

theorem entriesNode214_2 : (data.drop 214).take 2 = (originalEntries.drop 214).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 214 1 1 215 2 rfl rfl row214_binding row215_binding

theorem entriesNode212_4 : (data.drop 212).take 4 = (originalEntries.drop 212).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 212 2 2 214 4 rfl rfl entriesNode212_2 entriesNode214_2

theorem entriesNode208_8 : (data.drop 208).take 8 = (originalEntries.drop 208).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 208 4 4 212 8 rfl rfl entriesNode208_4 entriesNode212_4

theorem entriesNode200_16 : (data.drop 200).take 16 = (originalEntries.drop 200).take 16 :=
  NumericWorkerPortChecks.merge_at data originalEntries 200 8 8 208 16 rfl rfl entriesNode200_8 entriesNode208_8

theorem entriesNode216_2 : (data.drop 216).take 2 = (originalEntries.drop 216).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 216 1 1 217 2 rfl rfl row216_binding row217_binding

theorem entriesNode218_2 : (data.drop 218).take 2 = (originalEntries.drop 218).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 218 1 1 219 2 rfl rfl row218_binding row219_binding

theorem entriesNode216_4 : (data.drop 216).take 4 = (originalEntries.drop 216).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 216 2 2 218 4 rfl rfl entriesNode216_2 entriesNode218_2

theorem entriesNode220_2 : (data.drop 220).take 2 = (originalEntries.drop 220).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 220 1 1 221 2 rfl rfl row220_binding row221_binding

theorem entriesNode222_2 : (data.drop 222).take 2 = (originalEntries.drop 222).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 222 1 1 223 2 rfl rfl row222_binding row223_binding

theorem entriesNode220_4 : (data.drop 220).take 4 = (originalEntries.drop 220).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 220 2 2 222 4 rfl rfl entriesNode220_2 entriesNode222_2

theorem entriesNode216_8 : (data.drop 216).take 8 = (originalEntries.drop 216).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 216 4 4 220 8 rfl rfl entriesNode216_4 entriesNode220_4

theorem entriesNode224_2 : (data.drop 224).take 2 = (originalEntries.drop 224).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 224 1 1 225 2 rfl rfl row224_binding row225_binding

theorem entriesNode226_2 : (data.drop 226).take 2 = (originalEntries.drop 226).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 226 1 1 227 2 rfl rfl row226_binding row227_binding

theorem entriesNode224_4 : (data.drop 224).take 4 = (originalEntries.drop 224).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 224 2 2 226 4 rfl rfl entriesNode224_2 entriesNode226_2

theorem entriesNode228_2 : (data.drop 228).take 2 = (originalEntries.drop 228).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 228 1 1 229 2 rfl rfl row228_binding row229_binding

theorem entriesNode231_2 : (data.drop 231).take 2 = (originalEntries.drop 231).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 231 1 1 232 2 rfl rfl row231_binding row232_binding

theorem entriesNode230_3 : (data.drop 230).take 3 = (originalEntries.drop 230).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 230 1 2 231 3 rfl rfl row230_binding entriesNode231_2

theorem entriesNode228_5 : (data.drop 228).take 5 = (originalEntries.drop 228).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 228 2 3 230 5 rfl rfl entriesNode228_2 entriesNode230_3

theorem entriesNode224_9 : (data.drop 224).take 9 = (originalEntries.drop 224).take 9 :=
  NumericWorkerPortChecks.merge_at data originalEntries 224 4 5 228 9 rfl rfl entriesNode224_4 entriesNode228_5

theorem entriesNode216_17 : (data.drop 216).take 17 = (originalEntries.drop 216).take 17 :=
  NumericWorkerPortChecks.merge_at data originalEntries 216 8 9 224 17 rfl rfl entriesNode216_8 entriesNode224_9

theorem entriesNode200_33 : (data.drop 200).take 33 = (originalEntries.drop 200).take 33 :=
  NumericWorkerPortChecks.merge_at data originalEntries 200 16 17 216 33 rfl rfl entriesNode200_16 entriesNode216_17

theorem entriesNode233_2 : (data.drop 233).take 2 = (originalEntries.drop 233).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 233 1 1 234 2 rfl rfl row233_binding row234_binding

theorem entriesNode235_2 : (data.drop 235).take 2 = (originalEntries.drop 235).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 235 1 1 236 2 rfl rfl row235_binding row236_binding

theorem entriesNode233_4 : (data.drop 233).take 4 = (originalEntries.drop 233).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 233 2 2 235 4 rfl rfl entriesNode233_2 entriesNode235_2

theorem entriesNode237_2 : (data.drop 237).take 2 = (originalEntries.drop 237).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 237 1 1 238 2 rfl rfl row237_binding row238_binding

theorem entriesNode239_2 : (data.drop 239).take 2 = (originalEntries.drop 239).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 239 1 1 240 2 rfl rfl row239_binding row240_binding

theorem entriesNode237_4 : (data.drop 237).take 4 = (originalEntries.drop 237).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 237 2 2 239 4 rfl rfl entriesNode237_2 entriesNode239_2

theorem entriesNode233_8 : (data.drop 233).take 8 = (originalEntries.drop 233).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 233 4 4 237 8 rfl rfl entriesNode233_4 entriesNode237_4

theorem entriesNode241_2 : (data.drop 241).take 2 = (originalEntries.drop 241).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 241 1 1 242 2 rfl rfl row241_binding row242_binding

theorem entriesNode243_2 : (data.drop 243).take 2 = (originalEntries.drop 243).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 243 1 1 244 2 rfl rfl row243_binding row244_binding

theorem entriesNode241_4 : (data.drop 241).take 4 = (originalEntries.drop 241).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 241 2 2 243 4 rfl rfl entriesNode241_2 entriesNode243_2

theorem entriesNode245_2 : (data.drop 245).take 2 = (originalEntries.drop 245).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 245 1 1 246 2 rfl rfl row245_binding row246_binding

theorem entriesNode248_2 : (data.drop 248).take 2 = (originalEntries.drop 248).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 248 1 1 249 2 rfl rfl row248_binding row249_binding

theorem entriesNode247_3 : (data.drop 247).take 3 = (originalEntries.drop 247).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 247 1 2 248 3 rfl rfl row247_binding entriesNode248_2

theorem entriesNode245_5 : (data.drop 245).take 5 = (originalEntries.drop 245).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 245 2 3 247 5 rfl rfl entriesNode245_2 entriesNode247_3

theorem entriesNode241_9 : (data.drop 241).take 9 = (originalEntries.drop 241).take 9 :=
  NumericWorkerPortChecks.merge_at data originalEntries 241 4 5 245 9 rfl rfl entriesNode241_4 entriesNode245_5

theorem entriesNode233_17 : (data.drop 233).take 17 = (originalEntries.drop 233).take 17 :=
  NumericWorkerPortChecks.merge_at data originalEntries 233 8 9 241 17 rfl rfl entriesNode233_8 entriesNode241_9

theorem entriesNode250_2 : (data.drop 250).take 2 = (originalEntries.drop 250).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 250 1 1 251 2 rfl rfl row250_binding row251_binding

theorem entriesNode252_2 : (data.drop 252).take 2 = (originalEntries.drop 252).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 252 1 1 253 2 rfl rfl row252_binding row253_binding

theorem entriesNode250_4 : (data.drop 250).take 4 = (originalEntries.drop 250).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 250 2 2 252 4 rfl rfl entriesNode250_2 entriesNode252_2

theorem entriesNode254_2 : (data.drop 254).take 2 = (originalEntries.drop 254).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 254 1 1 255 2 rfl rfl row254_binding row255_binding

theorem entriesNode256_2 : (data.drop 256).take 2 = (originalEntries.drop 256).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 256 1 1 257 2 rfl rfl row256_binding row257_binding

theorem entriesNode254_4 : (data.drop 254).take 4 = (originalEntries.drop 254).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 254 2 2 256 4 rfl rfl entriesNode254_2 entriesNode256_2

theorem entriesNode250_8 : (data.drop 250).take 8 = (originalEntries.drop 250).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 250 4 4 254 8 rfl rfl entriesNode250_4 entriesNode254_4

theorem entriesNode258_2 : (data.drop 258).take 2 = (originalEntries.drop 258).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 258 1 1 259 2 rfl rfl row258_binding row259_binding

theorem entriesNode260_2 : (data.drop 260).take 2 = (originalEntries.drop 260).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 260 1 1 261 2 rfl rfl row260_binding row261_binding

theorem entriesNode258_4 : (data.drop 258).take 4 = (originalEntries.drop 258).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 258 2 2 260 4 rfl rfl entriesNode258_2 entriesNode260_2

theorem entriesNode262_2 : (data.drop 262).take 2 = (originalEntries.drop 262).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 262 1 1 263 2 rfl rfl row262_binding row263_binding

theorem entriesNode265_2 : (data.drop 265).take 2 = (originalEntries.drop 265).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 265 1 1 266 2 rfl rfl row265_binding row266_binding

theorem entriesNode264_3 : (data.drop 264).take 3 = (originalEntries.drop 264).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 264 1 2 265 3 rfl rfl row264_binding entriesNode265_2

theorem entriesNode262_5 : (data.drop 262).take 5 = (originalEntries.drop 262).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 262 2 3 264 5 rfl rfl entriesNode262_2 entriesNode264_3

theorem entriesNode258_9 : (data.drop 258).take 9 = (originalEntries.drop 258).take 9 :=
  NumericWorkerPortChecks.merge_at data originalEntries 258 4 5 262 9 rfl rfl entriesNode258_4 entriesNode262_5

theorem entriesNode250_17 : (data.drop 250).take 17 = (originalEntries.drop 250).take 17 :=
  NumericWorkerPortChecks.merge_at data originalEntries 250 8 9 258 17 rfl rfl entriesNode250_8 entriesNode258_9

theorem entriesNode233_34 : (data.drop 233).take 34 = (originalEntries.drop 233).take 34 :=
  NumericWorkerPortChecks.merge_at data originalEntries 233 17 17 250 34 rfl rfl entriesNode233_17 entriesNode250_17

theorem entriesNode200_67 : (data.drop 200).take 67 = (originalEntries.drop 200).take 67 :=
  NumericWorkerPortChecks.merge_at data originalEntries 200 33 34 233 67 rfl rfl entriesNode200_33 entriesNode233_34

theorem entriesNode133_134 : (data.drop 133).take 134 = (originalEntries.drop 133).take 134 :=
  NumericWorkerPortChecks.merge_at data originalEntries 133 67 67 200 134 rfl rfl entriesNode133_67 entriesNode200_67

theorem entriesNode0_267 : (data.drop 0).take 267 = (originalEntries.drop 0).take 267 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 133 134 133 267 rfl rfl entriesNode0_133 entriesNode133_134

theorem source_binding : data = originalEntries :=
  NumericQueryFrameChecks.complete_binding data originalEntries 267
    (by decide +kernel) (by decide +kernel) entriesNode0_267

end Airbender.Compiler.MemoryPayloadChecks.BlakeRoundCached
