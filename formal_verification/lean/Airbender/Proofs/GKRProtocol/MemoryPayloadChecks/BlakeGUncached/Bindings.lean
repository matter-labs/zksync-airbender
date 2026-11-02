import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.BlakeGUncached.Data
import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.BlakeGUncached.ProjectionBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.MemoryPayloadChecks.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

attribute [local irreducible] originalEntries data

numeric_data_binding row0_view : (data.drop 0).take 1 = [projectionData]

theorem row0_source : [projectionData] = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing Airbender.Compiler.MemoryNative.BlakeGUncached.native.projectionInputs)] :=
  congrArg List.singleton projection_source_binding

numeric_data_binding row0_entry : (originalEntries.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing Airbender.Compiler.MemoryNative.BlakeGUncached.native.projectionInputs)]

theorem row0_binding : (data.drop 0).take 1 = (originalEntries.drop 0).take 1 :=
  row0_view.trans (row0_source.trans row0_entry.symm)

numeric_data_binding row1_view : (data.drop 1).take 1 = (data1.drop 0).take 1

numeric_data_binding row1_source : (data1.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf0).isSome))]

numeric_data_binding row1_entry : (originalEntries.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf0).isSome))]

theorem row1_binding : (data.drop 1).take 1 = (originalEntries.drop 1).take 1 :=
  row1_view.trans (row1_source.trans row1_entry.symm)

numeric_data_binding row2_view : (data.drop 2).take 1 = (data1.drop 1).take 1

numeric_data_binding row2_source : (data1.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw0).inputs)]

numeric_data_binding row2_entry : (originalEntries.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw0).inputs)]

theorem row2_binding : (data.drop 2).take 1 = (originalEntries.drop 2).take 1 :=
  row2_view.trans (row2_source.trans row2_entry.symm)

numeric_data_binding row3_view : (data.drop 3).take 1 = (data1.drop 2).take 1

numeric_data_binding row3_source : (data1.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf1).isSome))]

numeric_data_binding row3_entry : (originalEntries.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf1).isSome))]

theorem row3_binding : (data.drop 3).take 1 = (originalEntries.drop 3).take 1 :=
  row3_view.trans (row3_source.trans row3_entry.symm)

numeric_data_binding row4_view : (data.drop 4).take 1 = (data1.drop 3).take 1

numeric_data_binding row4_source : (data1.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw1).inputs)]

numeric_data_binding row4_entry : (originalEntries.drop 4).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw1).inputs)]

theorem row4_binding : (data.drop 4).take 1 = (originalEntries.drop 4).take 1 :=
  row4_view.trans (row4_source.trans row4_entry.symm)

numeric_data_binding row5_view : (data.drop 5).take 1 = (data5.drop 0).take 1

numeric_data_binding row5_source : (data5.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf2).isSome))]

numeric_data_binding row5_entry : (originalEntries.drop 5).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf2).isSome))]

theorem row5_binding : (data.drop 5).take 1 = (originalEntries.drop 5).take 1 :=
  row5_view.trans (row5_source.trans row5_entry.symm)

numeric_data_binding row6_view : (data.drop 6).take 1 = (data5.drop 1).take 1

numeric_data_binding row6_source : (data5.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw2).inputs)]

numeric_data_binding row6_entry : (originalEntries.drop 6).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw2).inputs)]

theorem row6_binding : (data.drop 6).take 1 = (originalEntries.drop 6).take 1 :=
  row6_view.trans (row6_source.trans row6_entry.symm)

numeric_data_binding row7_view : (data.drop 7).take 1 = (data5.drop 2).take 1

numeric_data_binding row7_source : (data5.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf3).isSome))]

numeric_data_binding row7_entry : (originalEntries.drop 7).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf3).isSome))]

theorem row7_binding : (data.drop 7).take 1 = (originalEntries.drop 7).take 1 :=
  row7_view.trans (row7_source.trans row7_entry.symm)

numeric_data_binding row8_view : (data.drop 8).take 1 = (data5.drop 3).take 1

numeric_data_binding row8_source : (data5.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw3).inputs)]

numeric_data_binding row8_entry : (originalEntries.drop 8).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw3).inputs)]

theorem row8_binding : (data.drop 8).take 1 = (originalEntries.drop 8).take 1 :=
  row8_view.trans (row8_source.trans row8_entry.symm)

numeric_data_binding row9_view : (data.drop 9).take 1 = (data9.drop 0).take 1

numeric_data_binding row9_source : (data9.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf4).isSome))]

numeric_data_binding row9_entry : (originalEntries.drop 9).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf4).isSome))]

theorem row9_binding : (data.drop 9).take 1 = (originalEntries.drop 9).take 1 :=
  row9_view.trans (row9_source.trans row9_entry.symm)

numeric_data_binding row10_view : (data.drop 10).take 1 = (data9.drop 1).take 1

numeric_data_binding row10_source : (data9.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw4).inputs)]

numeric_data_binding row10_entry : (originalEntries.drop 10).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw4).inputs)]

theorem row10_binding : (data.drop 10).take 1 = (originalEntries.drop 10).take 1 :=
  row10_view.trans (row10_source.trans row10_entry.symm)

numeric_data_binding row11_view : (data.drop 11).take 1 = (data9.drop 2).take 1

numeric_data_binding row11_source : (data9.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf5).isSome))]

numeric_data_binding row11_entry : (originalEntries.drop 11).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf5).isSome))]

theorem row11_binding : (data.drop 11).take 1 = (originalEntries.drop 11).take 1 :=
  row11_view.trans (row11_source.trans row11_entry.symm)

numeric_data_binding row12_view : (data.drop 12).take 1 = (data9.drop 3).take 1

numeric_data_binding row12_source : (data9.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw5).inputs)]

numeric_data_binding row12_entry : (originalEntries.drop 12).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw5).inputs)]

theorem row12_binding : (data.drop 12).take 1 = (originalEntries.drop 12).take 1 :=
  row12_view.trans (row12_source.trans row12_entry.symm)

numeric_data_binding row13_view : (data.drop 13).take 1 = (data13.drop 0).take 1

numeric_data_binding row13_source : (data13.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf6).isSome))]

numeric_data_binding row13_entry : (originalEntries.drop 13).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf6).isSome))]

theorem row13_binding : (data.drop 13).take 1 = (originalEntries.drop 13).take 1 :=
  row13_view.trans (row13_source.trans row13_entry.symm)

numeric_data_binding row14_view : (data.drop 14).take 1 = (data13.drop 1).take 1

numeric_data_binding row14_source : (data13.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw6).inputs)]

numeric_data_binding row14_entry : (originalEntries.drop 14).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw6).inputs)]

theorem row14_binding : (data.drop 14).take 1 = (originalEntries.drop 14).take 1 :=
  row14_view.trans (row14_source.trans row14_entry.symm)

numeric_data_binding row15_view : (data.drop 15).take 1 = (data13.drop 2).take 1

numeric_data_binding row15_source : (data13.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf7).isSome))]

numeric_data_binding row15_entry : (originalEntries.drop 15).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf7).isSome))]

theorem row15_binding : (data.drop 15).take 1 = (originalEntries.drop 15).take 1 :=
  row15_view.trans (row15_source.trans row15_entry.symm)

numeric_data_binding row16_view : (data.drop 16).take 1 = (data13.drop 3).take 1

numeric_data_binding row16_source : (data13.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw7).inputs)]

numeric_data_binding row16_entry : (originalEntries.drop 16).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw7).inputs)]

theorem row16_binding : (data.drop 16).take 1 = (originalEntries.drop 16).take 1 :=
  row16_view.trans (row16_source.trans row16_entry.symm)

numeric_data_binding row17_view : (data.drop 17).take 1 = (data17.drop 0).take 1

numeric_data_binding row17_source : (data17.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf8).isSome))]

numeric_data_binding row17_entry : (originalEntries.drop 17).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf8).isSome))]

theorem row17_binding : (data.drop 17).take 1 = (originalEntries.drop 17).take 1 :=
  row17_view.trans (row17_source.trans row17_entry.symm)

numeric_data_binding row18_view : (data.drop 18).take 1 = (data17.drop 1).take 1

numeric_data_binding row18_source : (data17.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw8).inputs)]

numeric_data_binding row18_entry : (originalEntries.drop 18).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw8).inputs)]

theorem row18_binding : (data.drop 18).take 1 = (originalEntries.drop 18).take 1 :=
  row18_view.trans (row18_source.trans row18_entry.symm)

numeric_data_binding row19_view : (data.drop 19).take 1 = (data17.drop 2).take 1

numeric_data_binding row19_source : (data17.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf9).isSome))]

numeric_data_binding row19_entry : (originalEntries.drop 19).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf9).isSome))]

theorem row19_binding : (data.drop 19).take 1 = (originalEntries.drop 19).take 1 :=
  row19_view.trans (row19_source.trans row19_entry.symm)

numeric_data_binding row20_view : (data.drop 20).take 1 = (data17.drop 3).take 1

numeric_data_binding row20_source : (data17.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw9).inputs)]

numeric_data_binding row20_entry : (originalEntries.drop 20).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw9).inputs)]

theorem row20_binding : (data.drop 20).take 1 = (originalEntries.drop 20).take 1 :=
  row20_view.trans (row20_source.trans row20_entry.symm)

numeric_data_binding row21_view : (data.drop 21).take 1 = (data21.drop 0).take 1

numeric_data_binding row21_source : (data21.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf10).isSome))]

numeric_data_binding row21_entry : (originalEntries.drop 21).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf10).isSome))]

theorem row21_binding : (data.drop 21).take 1 = (originalEntries.drop 21).take 1 :=
  row21_view.trans (row21_source.trans row21_entry.symm)

numeric_data_binding row22_view : (data.drop 22).take 1 = (data21.drop 1).take 1

numeric_data_binding row22_source : (data21.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw10).inputs)]

numeric_data_binding row22_entry : (originalEntries.drop 22).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw10).inputs)]

theorem row22_binding : (data.drop 22).take 1 = (originalEntries.drop 22).take 1 :=
  row22_view.trans (row22_source.trans row22_entry.symm)

numeric_data_binding row23_view : (data.drop 23).take 1 = (data21.drop 2).take 1

numeric_data_binding row23_source : (data21.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf11).isSome))]

numeric_data_binding row23_entry : (originalEntries.drop 23).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf11).isSome))]

theorem row23_binding : (data.drop 23).take 1 = (originalEntries.drop 23).take 1 :=
  row23_view.trans (row23_source.trans row23_entry.symm)

numeric_data_binding row24_view : (data.drop 24).take 1 = (data21.drop 3).take 1

numeric_data_binding row24_source : (data21.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw11).inputs)]

numeric_data_binding row24_entry : (originalEntries.drop 24).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw11).inputs)]

theorem row24_binding : (data.drop 24).take 1 = (originalEntries.drop 24).take 1 :=
  row24_view.trans (row24_source.trans row24_entry.symm)

numeric_data_binding row25_view : (data.drop 25).take 1 = (data25.drop 0).take 1

numeric_data_binding row25_source : (data25.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf12).isSome))]

numeric_data_binding row25_entry : (originalEntries.drop 25).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf12).isSome))]

theorem row25_binding : (data.drop 25).take 1 = (originalEntries.drop 25).take 1 :=
  row25_view.trans (row25_source.trans row25_entry.symm)

numeric_data_binding row26_view : (data.drop 26).take 1 = (data25.drop 1).take 1

numeric_data_binding row26_source : (data25.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw12).inputs)]

numeric_data_binding row26_entry : (originalEntries.drop 26).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw12).inputs)]

theorem row26_binding : (data.drop 26).take 1 = (originalEntries.drop 26).take 1 :=
  row26_view.trans (row26_source.trans row26_entry.symm)

numeric_data_binding row27_view : (data.drop 27).take 1 = (data25.drop 2).take 1

numeric_data_binding row27_source : (data25.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf13).isSome))]

numeric_data_binding row27_entry : (originalEntries.drop 27).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf13).isSome))]

theorem row27_binding : (data.drop 27).take 1 = (originalEntries.drop 27).take 1 :=
  row27_view.trans (row27_source.trans row27_entry.symm)

numeric_data_binding row28_view : (data.drop 28).take 1 = (data25.drop 3).take 1

numeric_data_binding row28_source : (data25.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw13).inputs)]

numeric_data_binding row28_entry : (originalEntries.drop 28).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw13).inputs)]

theorem row28_binding : (data.drop 28).take 1 = (originalEntries.drop 28).take 1 :=
  row28_view.trans (row28_source.trans row28_entry.symm)

numeric_data_binding row29_view : (data.drop 29).take 1 = (data29.drop 0).take 1

numeric_data_binding row29_source : (data29.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf14).isSome))]

numeric_data_binding row29_entry : (originalEntries.drop 29).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf14).isSome))]

theorem row29_binding : (data.drop 29).take 1 = (originalEntries.drop 29).take 1 :=
  row29_view.trans (row29_source.trans row29_entry.symm)

numeric_data_binding row30_view : (data.drop 30).take 1 = (data29.drop 1).take 1

numeric_data_binding row30_source : (data29.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw14).inputs)]

numeric_data_binding row30_entry : (originalEntries.drop 30).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw14).inputs)]

theorem row30_binding : (data.drop 30).take 1 = (originalEntries.drop 30).take 1 :=
  row30_view.trans (row30_source.trans row30_entry.symm)

numeric_data_binding row31_view : (data.drop 31).take 1 = (data29.drop 2).take 1

numeric_data_binding row31_source : (data29.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf15).isSome))]

numeric_data_binding row31_entry : (originalEntries.drop 31).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf15).isSome))]

theorem row31_binding : (data.drop 31).take 1 = (originalEntries.drop 31).take 1 :=
  row31_view.trans (row31_source.trans row31_entry.symm)

numeric_data_binding row32_view : (data.drop 32).take 1 = (data29.drop 3).take 1

numeric_data_binding row32_source : (data29.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw15).inputs)]

numeric_data_binding row32_entry : (originalEntries.drop 32).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw15).inputs)]

theorem row32_binding : (data.drop 32).take 1 = (originalEntries.drop 32).take 1 :=
  row32_view.trans (row32_source.trans row32_entry.symm)

numeric_data_binding row33_view : (data.drop 33).take 1 = (data33.drop 0).take 1

numeric_data_binding row33_source : (data33.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf16).isSome))]

numeric_data_binding row33_entry : (originalEntries.drop 33).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf16).isSome))]

theorem row33_binding : (data.drop 33).take 1 = (originalEntries.drop 33).take 1 :=
  row33_view.trans (row33_source.trans row33_entry.symm)

numeric_data_binding row34_view : (data.drop 34).take 1 = (data33.drop 1).take 1

numeric_data_binding row34_source : (data33.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw16).inputs)]

numeric_data_binding row34_entry : (originalEntries.drop 34).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw16).inputs)]

theorem row34_binding : (data.drop 34).take 1 = (originalEntries.drop 34).take 1 :=
  row34_view.trans (row34_source.trans row34_entry.symm)

numeric_data_binding row35_view : (data.drop 35).take 1 = (data33.drop 2).take 1

numeric_data_binding row35_source : (data33.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf17).isSome))]

numeric_data_binding row35_entry : (originalEntries.drop 35).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf17).isSome))]

theorem row35_binding : (data.drop 35).take 1 = (originalEntries.drop 35).take 1 :=
  row35_view.trans (row35_source.trans row35_entry.symm)

numeric_data_binding row36_view : (data.drop 36).take 1 = (data33.drop 3).take 1

numeric_data_binding row36_source : (data33.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw17).inputs)]

numeric_data_binding row36_entry : (originalEntries.drop 36).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw17).inputs)]

theorem row36_binding : (data.drop 36).take 1 = (originalEntries.drop 36).take 1 :=
  row36_view.trans (row36_source.trans row36_entry.symm)

numeric_data_binding row37_view : (data.drop 37).take 1 = (data37.drop 0).take 1

numeric_data_binding row37_source : (data37.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf18).isSome))]

numeric_data_binding row37_entry : (originalEntries.drop 37).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf18).isSome))]

theorem row37_binding : (data.drop 37).take 1 = (originalEntries.drop 37).take 1 :=
  row37_view.trans (row37_source.trans row37_entry.symm)

numeric_data_binding row38_view : (data.drop 38).take 1 = (data37.drop 1).take 1

numeric_data_binding row38_source : (data37.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw18).inputs)]

numeric_data_binding row38_entry : (originalEntries.drop 38).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw18).inputs)]

theorem row38_binding : (data.drop 38).take 1 = (originalEntries.drop 38).take 1 :=
  row38_view.trans (row38_source.trans row38_entry.symm)

numeric_data_binding row39_view : (data.drop 39).take 1 = (data37.drop 2).take 1

numeric_data_binding row39_source : (data37.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf19).isSome))]

numeric_data_binding row39_entry : (originalEntries.drop 39).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions [] Airbender.Compiler.MemoryNative.BlakeGUncached.native.leaf19).isSome))]

theorem row39_binding : (data.drop 39).take 1 = (originalEntries.drop 39).take 1 :=
  row39_view.trans (row39_source.trans row39_entry.symm)

numeric_data_binding row40_view : (data.drop 40).take 1 = (data37.drop 3).take 1

numeric_data_binding row40_source : (data37.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw19).inputs)]

numeric_data_binding row40_entry : (originalEntries.drop 40).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing (Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw19).inputs)]

theorem row40_binding : (data.drop 40).take 1 = (originalEntries.drop 40).take 1 :=
  row40_view.trans (row40_source.trans row40_entry.symm)

numeric_data_binding row41_view : (data.drop 41).take 1 = (data41.drop 0).take 1

numeric_data_binding row41_source : (data41.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw0 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row41_entry : (originalEntries.drop 41).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw0 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row41_binding : (data.drop 41).take 1 = (originalEntries.drop 41).take 1 :=
  row41_view.trans (row41_source.trans row41_entry.symm)

numeric_data_binding row42_view : (data.drop 42).take 1 = (data41.drop 1).take 1

numeric_data_binding row42_source : (data41.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw1 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row42_entry : (originalEntries.drop 42).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw1 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row42_binding : (data.drop 42).take 1 = (originalEntries.drop 42).take 1 :=
  row42_view.trans (row42_source.trans row42_entry.symm)

numeric_data_binding row43_view : (data.drop 43).take 1 = (data41.drop 2).take 1

numeric_data_binding row43_source : (data41.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw4 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row43_entry : (originalEntries.drop 43).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw4 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row43_binding : (data.drop 43).take 1 = (originalEntries.drop 43).take 1 :=
  row43_view.trans (row43_source.trans row43_entry.symm)

numeric_data_binding row44_view : (data.drop 44).take 1 = (data41.drop 3).take 1

numeric_data_binding row44_source : (data41.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw5 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row44_entry : (originalEntries.drop 44).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw5 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row44_binding : (data.drop 44).take 1 = (originalEntries.drop 44).take 1 :=
  row44_view.trans (row44_source.trans row44_entry.symm)

numeric_data_binding row45_view : (data.drop 45).take 1 = (data45.drop 0).take 1

numeric_data_binding row45_source : (data45.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate4 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw8 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row45_entry : (originalEntries.drop 45).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate4 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw8 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row45_binding : (data.drop 45).take 1 = (originalEntries.drop 45).take 1 :=
  row45_view.trans (row45_source.trans row45_entry.symm)

numeric_data_binding row46_view : (data.drop 46).take 1 = (data45.drop 1).take 1

numeric_data_binding row46_source : (data45.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate5 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw9 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row46_entry : (originalEntries.drop 46).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate5 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw9 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row46_binding : (data.drop 46).take 1 = (originalEntries.drop 46).take 1 :=
  row46_view.trans (row46_source.trans row46_entry.symm)

numeric_data_binding row47_view : (data.drop 47).take 1 = (data45.drop 2).take 1

numeric_data_binding row47_source : (data45.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate6 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw12 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row47_entry : (originalEntries.drop 47).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate6 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw12 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row47_binding : (data.drop 47).take 1 = (originalEntries.drop 47).take 1 :=
  row47_view.trans (row47_source.trans row47_entry.symm)

numeric_data_binding row48_view : (data.drop 48).take 1 = (data45.drop 3).take 1

numeric_data_binding row48_source : (data45.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate7 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw13 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row48_entry : (originalEntries.drop 48).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate7 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw13 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row48_binding : (data.drop 48).take 1 = (originalEntries.drop 48).take 1 :=
  row48_view.trans (row48_source.trans row48_entry.symm)

numeric_data_binding row49_view : (data.drop 49).take 1 = (data49.drop 0).take 1

numeric_data_binding row49_source : (data49.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate8 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw16 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row49_entry : (originalEntries.drop 49).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate8 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw16 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row49_binding : (data.drop 49).take 1 = (originalEntries.drop 49).take 1 :=
  row49_view.trans (row49_source.trans row49_entry.symm)

numeric_data_binding row50_view : (data.drop 50).take 1 = (data49.drop 1).take 1

numeric_data_binding row50_source : (data49.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate9 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw17 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row50_entry : (originalEntries.drop 50).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadCertificate9 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw17 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row50_binding : (data.drop 50).take 1 = (originalEntries.drop 50).take 1 :=
  row50_view.trans (row50_source.trans row50_entry.symm)

numeric_data_binding row51_view : (data.drop 51).take 1 = (data49.drop 2).take 1

numeric_data_binding row51_source : (data49.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing [(GKRAddress.InnerLayer 4 0)])]

numeric_data_binding row51_entry : (originalEntries.drop 51).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing [(GKRAddress.InnerLayer 4 0)])]

theorem row51_binding : (data.drop 51).take 1 = (originalEntries.drop 51).take 1 :=
  row51_view.trans (row51_source.trans row51_entry.symm)

numeric_data_binding row52_view : (data.drop 52).take 1 = (data49.drop 3).take 1

numeric_data_binding row52_source : (data49.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw2 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row52_entry : (originalEntries.drop 52).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw2 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row52_binding : (data.drop 52).take 1 = (originalEntries.drop 52).take 1 :=
  row52_view.trans (row52_source.trans row52_entry.symm)

numeric_data_binding row53_view : (data.drop 53).take 1 = (data53.drop 0).take 1

numeric_data_binding row53_source : (data53.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw3 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row53_entry : (originalEntries.drop 53).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw3 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row53_binding : (data.drop 53).take 1 = (originalEntries.drop 53).take 1 :=
  row53_view.trans (row53_source.trans row53_entry.symm)

numeric_data_binding row54_view : (data.drop 54).take 1 = (data53.drop 1).take 1

numeric_data_binding row54_source : (data53.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw6 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row54_entry : (originalEntries.drop 54).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw6 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row54_binding : (data.drop 54).take 1 = (originalEntries.drop 54).take 1 :=
  row54_view.trans (row54_source.trans row54_entry.symm)

numeric_data_binding row55_view : (data.drop 55).take 1 = (data53.drop 2).take 1

numeric_data_binding row55_source : (data53.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw7 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row55_entry : (originalEntries.drop 55).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw7 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row55_binding : (data.drop 55).take 1 = (originalEntries.drop 55).take 1 :=
  row55_view.trans (row55_source.trans row55_entry.symm)

numeric_data_binding row56_view : (data.drop 56).take 1 = (data53.drop 3).take 1

numeric_data_binding row56_source : (data53.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate4 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw10 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row56_entry : (originalEntries.drop 56).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate4 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw10 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row56_binding : (data.drop 56).take 1 = (originalEntries.drop 56).take 1 :=
  row56_view.trans (row56_source.trans row56_entry.symm)

numeric_data_binding row57_view : (data.drop 57).take 1 = (data57.drop 0).take 1

numeric_data_binding row57_source : (data57.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate5 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw11 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row57_entry : (originalEntries.drop 57).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate5 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw11 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row57_binding : (data.drop 57).take 1 = (originalEntries.drop 57).take 1 :=
  row57_view.trans (row57_source.trans row57_entry.symm)

numeric_data_binding row58_view : (data.drop 58).take 1 = (data57.drop 1).take 1

numeric_data_binding row58_source : (data57.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate6 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw14 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row58_entry : (originalEntries.drop 58).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate6 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw14 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row58_binding : (data.drop 58).take 1 = (originalEntries.drop 58).take 1 :=
  row58_view.trans (row58_source.trans row58_entry.symm)

numeric_data_binding row59_view : (data.drop 59).take 1 = (data57.drop 2).take 1

numeric_data_binding row59_source : (data57.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate7 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw15 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row59_entry : (originalEntries.drop 59).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate7 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw15 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row59_binding : (data.drop 59).take 1 = (originalEntries.drop 59).take 1 :=
  row59_view.trans (row59_source.trans row59_entry.symm)

numeric_data_binding row60_view : (data.drop 60).take 1 = (data57.drop 3).take 1

numeric_data_binding row60_source : (data57.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate8 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw18 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row60_entry : (originalEntries.drop 60).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate8 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw18 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row60_binding : (data.drop 60).take 1 = (originalEntries.drop 60).take 1 :=
  row60_view.trans (row60_source.trans row60_entry.symm)

numeric_data_binding row61_view : (data.drop 61).take 1 = (data61.drop 0).take 1

numeric_data_binding row61_source : (data61.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate9 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw19 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row61_entry : (originalEntries.drop 61).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteCertificate9 (((Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryNative.BlakeGUncached.native.raw19 Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row61_binding : (data.drop 61).take 1 = (originalEntries.drop 61).take 1 :=
  row61_view.trans (row61_source.trans row61_entry.symm)

numeric_data_binding row62_view : (data.drop 62).take 1 = (data61.drop 1).take 1

numeric_data_binding row62_source : (data61.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing [(GKRAddress.InnerLayer 4 0)])]

numeric_data_binding row62_entry : (originalEntries.drop 62).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing [(GKRAddress.InnerLayer 4 0)])]

theorem row62_binding : (data.drop 62).take 1 = (originalEntries.drop 62).take 1 :=
  row62_view.trans (row62_source.trans row62_entry.symm)

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

theorem entriesNode15_2 : (data.drop 15).take 2 = (originalEntries.drop 15).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 15 1 1 16 2 rfl rfl row15_binding row16_binding

theorem entriesNode17_2 : (data.drop 17).take 2 = (originalEntries.drop 17).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 17 1 1 18 2 rfl rfl row17_binding row18_binding

theorem entriesNode15_4 : (data.drop 15).take 4 = (originalEntries.drop 15).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 15 2 2 17 4 rfl rfl entriesNode15_2 entriesNode17_2

theorem entriesNode19_2 : (data.drop 19).take 2 = (originalEntries.drop 19).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 19 1 1 20 2 rfl rfl row19_binding row20_binding

theorem entriesNode21_2 : (data.drop 21).take 2 = (originalEntries.drop 21).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 21 1 1 22 2 rfl rfl row21_binding row22_binding

theorem entriesNode19_4 : (data.drop 19).take 4 = (originalEntries.drop 19).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 19 2 2 21 4 rfl rfl entriesNode19_2 entriesNode21_2

theorem entriesNode15_8 : (data.drop 15).take 8 = (originalEntries.drop 15).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 15 4 4 19 8 rfl rfl entriesNode15_4 entriesNode19_4

theorem entriesNode23_2 : (data.drop 23).take 2 = (originalEntries.drop 23).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 23 1 1 24 2 rfl rfl row23_binding row24_binding

theorem entriesNode25_2 : (data.drop 25).take 2 = (originalEntries.drop 25).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 25 1 1 26 2 rfl rfl row25_binding row26_binding

theorem entriesNode23_4 : (data.drop 23).take 4 = (originalEntries.drop 23).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 23 2 2 25 4 rfl rfl entriesNode23_2 entriesNode25_2

theorem entriesNode27_2 : (data.drop 27).take 2 = (originalEntries.drop 27).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 27 1 1 28 2 rfl rfl row27_binding row28_binding

theorem entriesNode29_2 : (data.drop 29).take 2 = (originalEntries.drop 29).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 29 1 1 30 2 rfl rfl row29_binding row30_binding

theorem entriesNode27_4 : (data.drop 27).take 4 = (originalEntries.drop 27).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 27 2 2 29 4 rfl rfl entriesNode27_2 entriesNode29_2

theorem entriesNode23_8 : (data.drop 23).take 8 = (originalEntries.drop 23).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 23 4 4 27 8 rfl rfl entriesNode23_4 entriesNode27_4

theorem entriesNode15_16 : (data.drop 15).take 16 = (originalEntries.drop 15).take 16 :=
  NumericWorkerPortChecks.merge_at data originalEntries 15 8 8 23 16 rfl rfl entriesNode15_8 entriesNode23_8

theorem entriesNode0_31 : (data.drop 0).take 31 = (originalEntries.drop 0).take 31 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 15 16 15 31 rfl rfl entriesNode0_15 entriesNode15_16

theorem entriesNode31_2 : (data.drop 31).take 2 = (originalEntries.drop 31).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 31 1 1 32 2 rfl rfl row31_binding row32_binding

theorem entriesNode33_2 : (data.drop 33).take 2 = (originalEntries.drop 33).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 33 1 1 34 2 rfl rfl row33_binding row34_binding

theorem entriesNode31_4 : (data.drop 31).take 4 = (originalEntries.drop 31).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 31 2 2 33 4 rfl rfl entriesNode31_2 entriesNode33_2

theorem entriesNode35_2 : (data.drop 35).take 2 = (originalEntries.drop 35).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 35 1 1 36 2 rfl rfl row35_binding row36_binding

theorem entriesNode37_2 : (data.drop 37).take 2 = (originalEntries.drop 37).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 37 1 1 38 2 rfl rfl row37_binding row38_binding

theorem entriesNode35_4 : (data.drop 35).take 4 = (originalEntries.drop 35).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 35 2 2 37 4 rfl rfl entriesNode35_2 entriesNode37_2

theorem entriesNode31_8 : (data.drop 31).take 8 = (originalEntries.drop 31).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 31 4 4 35 8 rfl rfl entriesNode31_4 entriesNode35_4

theorem entriesNode39_2 : (data.drop 39).take 2 = (originalEntries.drop 39).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 39 1 1 40 2 rfl rfl row39_binding row40_binding

theorem entriesNode41_2 : (data.drop 41).take 2 = (originalEntries.drop 41).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 41 1 1 42 2 rfl rfl row41_binding row42_binding

theorem entriesNode39_4 : (data.drop 39).take 4 = (originalEntries.drop 39).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 39 2 2 41 4 rfl rfl entriesNode39_2 entriesNode41_2

theorem entriesNode43_2 : (data.drop 43).take 2 = (originalEntries.drop 43).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 43 1 1 44 2 rfl rfl row43_binding row44_binding

theorem entriesNode45_2 : (data.drop 45).take 2 = (originalEntries.drop 45).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 45 1 1 46 2 rfl rfl row45_binding row46_binding

theorem entriesNode43_4 : (data.drop 43).take 4 = (originalEntries.drop 43).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 43 2 2 45 4 rfl rfl entriesNode43_2 entriesNode45_2

theorem entriesNode39_8 : (data.drop 39).take 8 = (originalEntries.drop 39).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 39 4 4 43 8 rfl rfl entriesNode39_4 entriesNode43_4

theorem entriesNode31_16 : (data.drop 31).take 16 = (originalEntries.drop 31).take 16 :=
  NumericWorkerPortChecks.merge_at data originalEntries 31 8 8 39 16 rfl rfl entriesNode31_8 entriesNode39_8

theorem entriesNode47_2 : (data.drop 47).take 2 = (originalEntries.drop 47).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 47 1 1 48 2 rfl rfl row47_binding row48_binding

theorem entriesNode49_2 : (data.drop 49).take 2 = (originalEntries.drop 49).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 49 1 1 50 2 rfl rfl row49_binding row50_binding

theorem entriesNode47_4 : (data.drop 47).take 4 = (originalEntries.drop 47).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 47 2 2 49 4 rfl rfl entriesNode47_2 entriesNode49_2

theorem entriesNode51_2 : (data.drop 51).take 2 = (originalEntries.drop 51).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 51 1 1 52 2 rfl rfl row51_binding row52_binding

theorem entriesNode53_2 : (data.drop 53).take 2 = (originalEntries.drop 53).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 53 1 1 54 2 rfl rfl row53_binding row54_binding

theorem entriesNode51_4 : (data.drop 51).take 4 = (originalEntries.drop 51).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 51 2 2 53 4 rfl rfl entriesNode51_2 entriesNode53_2

theorem entriesNode47_8 : (data.drop 47).take 8 = (originalEntries.drop 47).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 47 4 4 51 8 rfl rfl entriesNode47_4 entriesNode51_4

theorem entriesNode55_2 : (data.drop 55).take 2 = (originalEntries.drop 55).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 55 1 1 56 2 rfl rfl row55_binding row56_binding

theorem entriesNode57_2 : (data.drop 57).take 2 = (originalEntries.drop 57).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 57 1 1 58 2 rfl rfl row57_binding row58_binding

theorem entriesNode55_4 : (data.drop 55).take 4 = (originalEntries.drop 55).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 55 2 2 57 4 rfl rfl entriesNode55_2 entriesNode57_2

theorem entriesNode59_2 : (data.drop 59).take 2 = (originalEntries.drop 59).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 59 1 1 60 2 rfl rfl row59_binding row60_binding

theorem entriesNode61_2 : (data.drop 61).take 2 = (originalEntries.drop 61).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 61 1 1 62 2 rfl rfl row61_binding row62_binding

theorem entriesNode59_4 : (data.drop 59).take 4 = (originalEntries.drop 59).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 59 2 2 61 4 rfl rfl entriesNode59_2 entriesNode61_2

theorem entriesNode55_8 : (data.drop 55).take 8 = (originalEntries.drop 55).take 8 :=
  NumericWorkerPortChecks.merge_at data originalEntries 55 4 4 59 8 rfl rfl entriesNode55_4 entriesNode59_4

theorem entriesNode47_16 : (data.drop 47).take 16 = (originalEntries.drop 47).take 16 :=
  NumericWorkerPortChecks.merge_at data originalEntries 47 8 8 55 16 rfl rfl entriesNode47_8 entriesNode55_8

theorem entriesNode31_32 : (data.drop 31).take 32 = (originalEntries.drop 31).take 32 :=
  NumericWorkerPortChecks.merge_at data originalEntries 31 16 16 47 32 rfl rfl entriesNode31_16 entriesNode47_16

theorem entriesNode0_63 : (data.drop 0).take 63 = (originalEntries.drop 0).take 63 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 31 32 31 63 rfl rfl entriesNode0_31 entriesNode31_32

theorem source_binding : data = originalEntries :=
  NumericQueryFrameChecks.complete_binding data originalEntries 63
    (by decide +kernel) (by decide +kernel) entriesNode0_63

end Airbender.Compiler.MemoryPayloadChecks.BlakeGUncached
