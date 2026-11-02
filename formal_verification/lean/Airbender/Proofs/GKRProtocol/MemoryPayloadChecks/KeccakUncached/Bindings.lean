import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.KeccakUncached.Data
import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.KeccakUncached.ProjectionBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.MemoryPayloadChecks.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

attribute [local irreducible] originalEntries data

numeric_data_binding row0_view : (data.drop 0).take 1 = [projectionData]

theorem row0_source : [projectionData] = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs)] :=
  congrArg List.singleton projection_source_binding

numeric_data_binding row0_entry : (originalEntries.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing Airbender.Compiler.MemoryNative.KeccakUncached.native.projectionInputs)]

theorem row0_binding : (data.drop 0).take 1 = (originalEntries.drop 0).take 1 :=
  row0_view.trans (row0_source.trans row0_entry.symm)

numeric_data_binding row1_view : (data.drop 1).take 1 = (data1.drop 0).take 1

numeric_data_binding row1_source : (data1.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf0).isSome))]

numeric_data_binding row1_entry : (originalEntries.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf0).isSome))]

theorem row1_binding : (data.drop 1).take 1 = (originalEntries.drop 1).take 1 :=
  row1_view.trans (row1_source.trans row1_entry.symm)

numeric_data_binding row2_view : (data.drop 2).take 1 = (data1.drop 1).take 1

numeric_data_binding row2_source : (data1.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw0).inputs)]

numeric_data_binding row2_entry : (originalEntries.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw0).inputs)]

theorem row2_binding : (data.drop 2).take 1 = (originalEntries.drop 2).take 1 :=
  row2_view.trans (row2_source.trans row2_entry.symm)

numeric_data_binding row3_view : (data.drop 3).take 1 = (data1.drop 2).take 1

numeric_data_binding row3_source : (data1.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf1).isSome))]

numeric_data_binding row3_entry : (originalEntries.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf1).isSome))]

theorem row3_binding : (data.drop 3).take 1 = (originalEntries.drop 3).take 1 :=
  row3_view.trans (row3_source.trans row3_entry.symm)

numeric_data_binding row4_view : (data.drop 4).take 1 = (data1.drop 3).take 1

numeric_data_binding row4_source : (data1.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw1).inputs)]

numeric_data_binding row4_entry : (originalEntries.drop 4).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw1).inputs)]

theorem row4_binding : (data.drop 4).take 1 = (originalEntries.drop 4).take 1 :=
  row4_view.trans (row4_source.trans row4_entry.symm)

numeric_data_binding row5_view : (data.drop 5).take 1 = (data5.drop 0).take 1

numeric_data_binding row5_source : (data5.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf2).isSome))]

numeric_data_binding row5_entry : (originalEntries.drop 5).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf2).isSome))]

theorem row5_binding : (data.drop 5).take 1 = (originalEntries.drop 5).take 1 :=
  row5_view.trans (row5_source.trans row5_entry.symm)

numeric_data_binding row6_view : (data.drop 6).take 1 = (data5.drop 1).take 1

numeric_data_binding row6_source : (data5.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw2).inputs)]

numeric_data_binding row6_entry : (originalEntries.drop 6).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw2).inputs)]

theorem row6_binding : (data.drop 6).take 1 = (originalEntries.drop 6).take 1 :=
  row6_view.trans (row6_source.trans row6_entry.symm)

numeric_data_binding row7_view : (data.drop 7).take 1 = (data5.drop 2).take 1

numeric_data_binding row7_source : (data5.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf3).isSome))]

numeric_data_binding row7_entry : (originalEntries.drop 7).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf3).isSome))]

theorem row7_binding : (data.drop 7).take 1 = (originalEntries.drop 7).take 1 :=
  row7_view.trans (row7_source.trans row7_entry.symm)

numeric_data_binding row8_view : (data.drop 8).take 1 = (data5.drop 3).take 1

numeric_data_binding row8_source : (data5.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw3).inputs)]

numeric_data_binding row8_entry : (originalEntries.drop 8).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw3).inputs)]

theorem row8_binding : (data.drop 8).take 1 = (originalEntries.drop 8).take 1 :=
  row8_view.trans (row8_source.trans row8_entry.symm)

numeric_data_binding row9_view : (data.drop 9).take 1 = (data9.drop 0).take 1

numeric_data_binding row9_source : (data9.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf4).isSome))]

numeric_data_binding row9_entry : (originalEntries.drop 9).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf4).isSome))]

theorem row9_binding : (data.drop 9).take 1 = (originalEntries.drop 9).take 1 :=
  row9_view.trans (row9_source.trans row9_entry.symm)

numeric_data_binding row10_view : (data.drop 10).take 1 = (data9.drop 1).take 1

numeric_data_binding row10_source : (data9.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw4).inputs)]

numeric_data_binding row10_entry : (originalEntries.drop 10).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw4).inputs)]

theorem row10_binding : (data.drop 10).take 1 = (originalEntries.drop 10).take 1 :=
  row10_view.trans (row10_source.trans row10_entry.symm)

numeric_data_binding row11_view : (data.drop 11).take 1 = (data9.drop 2).take 1

numeric_data_binding row11_source : (data9.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf5).isSome))]

numeric_data_binding row11_entry : (originalEntries.drop 11).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf5).isSome))]

theorem row11_binding : (data.drop 11).take 1 = (originalEntries.drop 11).take 1 :=
  row11_view.trans (row11_source.trans row11_entry.symm)

numeric_data_binding row12_view : (data.drop 12).take 1 = (data9.drop 3).take 1

numeric_data_binding row12_source : (data9.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw5).inputs)]

numeric_data_binding row12_entry : (originalEntries.drop 12).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw5).inputs)]

theorem row12_binding : (data.drop 12).take 1 = (originalEntries.drop 12).take 1 :=
  row12_view.trans (row12_source.trans row12_entry.symm)

numeric_data_binding row13_view : (data.drop 13).take 1 = (data13.drop 0).take 1

numeric_data_binding row13_source : (data13.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf6).isSome))]

numeric_data_binding row13_entry : (originalEntries.drop 13).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf6).isSome))]

theorem row13_binding : (data.drop 13).take 1 = (originalEntries.drop 13).take 1 :=
  row13_view.trans (row13_source.trans row13_entry.symm)

numeric_data_binding row14_view : (data.drop 14).take 1 = (data13.drop 1).take 1

numeric_data_binding row14_source : (data13.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw6).inputs)]

numeric_data_binding row14_entry : (originalEntries.drop 14).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw6).inputs)]

theorem row14_binding : (data.drop 14).take 1 = (originalEntries.drop 14).take 1 :=
  row14_view.trans (row14_source.trans row14_entry.symm)

numeric_data_binding row15_view : (data.drop 15).take 1 = (data13.drop 2).take 1

numeric_data_binding row15_source : (data13.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf7).isSome))]

numeric_data_binding row15_entry : (originalEntries.drop 15).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf7).isSome))]

theorem row15_binding : (data.drop 15).take 1 = (originalEntries.drop 15).take 1 :=
  row15_view.trans (row15_source.trans row15_entry.symm)

numeric_data_binding row16_view : (data.drop 16).take 1 = (data13.drop 3).take 1

numeric_data_binding row16_source : (data13.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw7).inputs)]

numeric_data_binding row16_entry : (originalEntries.drop 16).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw7).inputs)]

theorem row16_binding : (data.drop 16).take 1 = (originalEntries.drop 16).take 1 :=
  row16_view.trans (row16_source.trans row16_entry.symm)

numeric_data_binding row17_view : (data.drop 17).take 1 = (data17.drop 0).take 1

numeric_data_binding row17_source : (data17.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf8).isSome))]

numeric_data_binding row17_entry : (originalEntries.drop 17).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf8).isSome))]

theorem row17_binding : (data.drop 17).take 1 = (originalEntries.drop 17).take 1 :=
  row17_view.trans (row17_source.trans row17_entry.symm)

numeric_data_binding row18_view : (data.drop 18).take 1 = (data17.drop 1).take 1

numeric_data_binding row18_source : (data17.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw8).inputs)]

numeric_data_binding row18_entry : (originalEntries.drop 18).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw8).inputs)]

theorem row18_binding : (data.drop 18).take 1 = (originalEntries.drop 18).take 1 :=
  row18_view.trans (row18_source.trans row18_entry.symm)

numeric_data_binding row19_view : (data.drop 19).take 1 = (data17.drop 2).take 1

numeric_data_binding row19_source : (data17.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf9).isSome))]

numeric_data_binding row19_entry : (originalEntries.drop 19).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf9).isSome))]

theorem row19_binding : (data.drop 19).take 1 = (originalEntries.drop 19).take 1 :=
  row19_view.trans (row19_source.trans row19_entry.symm)

numeric_data_binding row20_view : (data.drop 20).take 1 = (data17.drop 3).take 1

numeric_data_binding row20_source : (data17.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw9).inputs)]

numeric_data_binding row20_entry : (originalEntries.drop 20).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw9).inputs)]

theorem row20_binding : (data.drop 20).take 1 = (originalEntries.drop 20).take 1 :=
  row20_view.trans (row20_source.trans row20_entry.symm)

numeric_data_binding row21_view : (data.drop 21).take 1 = (data21.drop 0).take 1

numeric_data_binding row21_source : (data21.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf10).isSome))]

numeric_data_binding row21_entry : (originalEntries.drop 21).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf10).isSome))]

theorem row21_binding : (data.drop 21).take 1 = (originalEntries.drop 21).take 1 :=
  row21_view.trans (row21_source.trans row21_entry.symm)

numeric_data_binding row22_view : (data.drop 22).take 1 = (data21.drop 1).take 1

numeric_data_binding row22_source : (data21.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw10).inputs)]

numeric_data_binding row22_entry : (originalEntries.drop 22).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw10).inputs)]

theorem row22_binding : (data.drop 22).take 1 = (originalEntries.drop 22).take 1 :=
  row22_view.trans (row22_source.trans row22_entry.symm)

numeric_data_binding row23_view : (data.drop 23).take 1 = (data21.drop 2).take 1

numeric_data_binding row23_source : (data21.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf11).isSome))]

numeric_data_binding row23_entry : (originalEntries.drop 23).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf11).isSome))]

theorem row23_binding : (data.drop 23).take 1 = (originalEntries.drop 23).take 1 :=
  row23_view.trans (row23_source.trans row23_entry.symm)

numeric_data_binding row24_view : (data.drop 24).take 1 = (data21.drop 3).take 1

numeric_data_binding row24_source : (data21.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw11).inputs)]

numeric_data_binding row24_entry : (originalEntries.drop 24).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw11).inputs)]

theorem row24_binding : (data.drop 24).take 1 = (originalEntries.drop 24).take 1 :=
  row24_view.trans (row24_source.trans row24_entry.symm)

numeric_data_binding row25_view : (data.drop 25).take 1 = (data25.drop 0).take 1

numeric_data_binding row25_source : (data25.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf12).isSome))]

numeric_data_binding row25_entry : (originalEntries.drop 25).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf12).isSome))]

theorem row25_binding : (data.drop 25).take 1 = (originalEntries.drop 25).take 1 :=
  row25_view.trans (row25_source.trans row25_entry.symm)

numeric_data_binding row26_view : (data.drop 26).take 1 = (data25.drop 1).take 1

numeric_data_binding row26_source : (data25.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw12).inputs)]

numeric_data_binding row26_entry : (originalEntries.drop 26).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw12).inputs)]

theorem row26_binding : (data.drop 26).take 1 = (originalEntries.drop 26).take 1 :=
  row26_view.trans (row26_source.trans row26_entry.symm)

numeric_data_binding row27_view : (data.drop 27).take 1 = (data25.drop 2).take 1

numeric_data_binding row27_source : (data25.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf13).isSome))]

numeric_data_binding row27_entry : (originalEntries.drop 27).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf13).isSome))]

theorem row27_binding : (data.drop 27).take 1 = (originalEntries.drop 27).take 1 :=
  row27_view.trans (row27_source.trans row27_entry.symm)

numeric_data_binding row28_view : (data.drop 28).take 1 = (data25.drop 3).take 1

numeric_data_binding row28_source : (data25.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw13).inputs)]

numeric_data_binding row28_entry : (originalEntries.drop 28).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw13).inputs)]

theorem row28_binding : (data.drop 28).take 1 = (originalEntries.drop 28).take 1 :=
  row28_view.trans (row28_source.trans row28_entry.symm)

numeric_data_binding row29_view : (data.drop 29).take 1 = (data29.drop 0).take 1

numeric_data_binding row29_source : (data29.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf14).isSome))]

numeric_data_binding row29_entry : (originalEntries.drop 29).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf14).isSome))]

theorem row29_binding : (data.drop 29).take 1 = (originalEntries.drop 29).take 1 :=
  row29_view.trans (row29_source.trans row29_entry.symm)

numeric_data_binding row30_view : (data.drop 30).take 1 = (data29.drop 1).take 1

numeric_data_binding row30_source : (data29.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw14).inputs)]

numeric_data_binding row30_entry : (originalEntries.drop 30).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw14).inputs)]

theorem row30_binding : (data.drop 30).take 1 = (originalEntries.drop 30).take 1 :=
  row30_view.trans (row30_source.trans row30_entry.symm)

numeric_data_binding row31_view : (data.drop 31).take 1 = (data29.drop 2).take 1

numeric_data_binding row31_source : (data29.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf15).isSome))]

numeric_data_binding row31_entry : (originalEntries.drop 31).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf15).isSome))]

theorem row31_binding : (data.drop 31).take 1 = (originalEntries.drop 31).take 1 :=
  row31_view.trans (row31_source.trans row31_entry.symm)

numeric_data_binding row32_view : (data.drop 32).take 1 = (data29.drop 3).take 1

numeric_data_binding row32_source : (data29.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw15).inputs)]

numeric_data_binding row32_entry : (originalEntries.drop 32).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw15).inputs)]

theorem row32_binding : (data.drop 32).take 1 = (originalEntries.drop 32).take 1 :=
  row32_view.trans (row32_source.trans row32_entry.symm)

numeric_data_binding row33_view : (data.drop 33).take 1 = (data33.drop 0).take 1

numeric_data_binding row33_source : (data33.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf16).isSome))]

numeric_data_binding row33_entry : (originalEntries.drop 33).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf16).isSome))]

theorem row33_binding : (data.drop 33).take 1 = (originalEntries.drop 33).take 1 :=
  row33_view.trans (row33_source.trans row33_entry.symm)

numeric_data_binding row34_view : (data.drop 34).take 1 = (data33.drop 1).take 1

numeric_data_binding row34_source : (data33.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw16).inputs)]

numeric_data_binding row34_entry : (originalEntries.drop 34).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw16).inputs)]

theorem row34_binding : (data.drop 34).take 1 = (originalEntries.drop 34).take 1 :=
  row34_view.trans (row34_source.trans row34_entry.symm)

numeric_data_binding row35_view : (data.drop 35).take 1 = (data33.drop 2).take 1

numeric_data_binding row35_source : (data33.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf17).isSome))]

numeric_data_binding row35_entry : (originalEntries.drop 35).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf17).isSome))]

theorem row35_binding : (data.drop 35).take 1 = (originalEntries.drop 35).take 1 :=
  row35_view.trans (row35_source.trans row35_entry.symm)

numeric_data_binding row36_view : (data.drop 36).take 1 = (data33.drop 3).take 1

numeric_data_binding row36_source : (data33.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw17).inputs)]

numeric_data_binding row36_entry : (originalEntries.drop 36).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw17).inputs)]

theorem row36_binding : (data.drop 36).take 1 = (originalEntries.drop 36).take 1 :=
  row36_view.trans (row36_source.trans row36_entry.symm)

numeric_data_binding row37_view : (data.drop 37).take 1 = (data37.drop 0).take 1

numeric_data_binding row37_source : (data37.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf18).isSome))]

numeric_data_binding row37_entry : (originalEntries.drop 37).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf18).isSome))]

theorem row37_binding : (data.drop 37).take 1 = (originalEntries.drop 37).take 1 :=
  row37_view.trans (row37_source.trans row37_entry.symm)

numeric_data_binding row38_view : (data.drop 38).take 1 = (data37.drop 1).take 1

numeric_data_binding row38_source : (data37.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw18).inputs)]

numeric_data_binding row38_entry : (originalEntries.drop 38).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw18).inputs)]

theorem row38_binding : (data.drop 38).take 1 = (originalEntries.drop 38).take 1 :=
  row38_view.trans (row38_source.trans row38_entry.symm)

numeric_data_binding row39_view : (data.drop 39).take 1 = (data37.drop 2).take 1

numeric_data_binding row39_source : (data37.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf19).isSome))]

numeric_data_binding row39_entry : (originalEntries.drop 39).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf19).isSome))]

theorem row39_binding : (data.drop 39).take 1 = (originalEntries.drop 39).take 1 :=
  row39_view.trans (row39_source.trans row39_entry.symm)

numeric_data_binding row40_view : (data.drop 40).take 1 = (data37.drop 3).take 1

numeric_data_binding row40_source : (data37.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw19).inputs)]

numeric_data_binding row40_entry : (originalEntries.drop 40).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw19).inputs)]

theorem row40_binding : (data.drop 40).take 1 = (originalEntries.drop 40).take 1 :=
  row40_view.trans (row40_source.trans row40_entry.symm)

numeric_data_binding row41_view : (data.drop 41).take 1 = (data41.drop 0).take 1

numeric_data_binding row41_source : (data41.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf20).isSome))]

numeric_data_binding row41_entry : (originalEntries.drop 41).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf20).isSome))]

theorem row41_binding : (data.drop 41).take 1 = (originalEntries.drop 41).take 1 :=
  row41_view.trans (row41_source.trans row41_entry.symm)

numeric_data_binding row42_view : (data.drop 42).take 1 = (data41.drop 1).take 1

numeric_data_binding row42_source : (data41.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw20).inputs)]

numeric_data_binding row42_entry : (originalEntries.drop 42).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw20).inputs)]

theorem row42_binding : (data.drop 42).take 1 = (originalEntries.drop 42).take 1 :=
  row42_view.trans (row42_source.trans row42_entry.symm)

numeric_data_binding row43_view : (data.drop 43).take 1 = (data41.drop 2).take 1

numeric_data_binding row43_source : (data41.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf21).isSome))]

numeric_data_binding row43_entry : (originalEntries.drop 43).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf21).isSome))]

theorem row43_binding : (data.drop 43).take 1 = (originalEntries.drop 43).take 1 :=
  row43_view.trans (row43_source.trans row43_entry.symm)

numeric_data_binding row44_view : (data.drop 44).take 1 = (data41.drop 3).take 1

numeric_data_binding row44_source : (data41.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw21).inputs)]

numeric_data_binding row44_entry : (originalEntries.drop 44).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw21).inputs)]

theorem row44_binding : (data.drop 44).take 1 = (originalEntries.drop 44).take 1 :=
  row44_view.trans (row44_source.trans row44_entry.symm)

numeric_data_binding row45_view : (data.drop 45).take 1 = (data45.drop 0).take 1

numeric_data_binding row45_source : (data45.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf22).isSome))]

numeric_data_binding row45_entry : (originalEntries.drop 45).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf22).isSome))]

theorem row45_binding : (data.drop 45).take 1 = (originalEntries.drop 45).take 1 :=
  row45_view.trans (row45_source.trans row45_entry.symm)

numeric_data_binding row46_view : (data.drop 46).take 1 = (data45.drop 1).take 1

numeric_data_binding row46_source : (data45.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw22).inputs)]

numeric_data_binding row46_entry : (originalEntries.drop 46).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw22).inputs)]

theorem row46_binding : (data.drop 46).take 1 = (originalEntries.drop 46).take 1 :=
  row46_view.trans (row46_source.trans row46_entry.symm)

numeric_data_binding row47_view : (data.drop 47).take 1 = (data45.drop 2).take 1

numeric_data_binding row47_source : (data45.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf23).isSome))]

numeric_data_binding row47_entry : (originalEntries.drop 47).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf23).isSome))]

theorem row47_binding : (data.drop 47).take 1 = (originalEntries.drop 47).take 1 :=
  row47_view.trans (row47_source.trans row47_entry.symm)

numeric_data_binding row48_view : (data.drop 48).take 1 = (data45.drop 3).take 1

numeric_data_binding row48_source : (data45.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw23).inputs)]

numeric_data_binding row48_entry : (originalEntries.drop 48).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw23).inputs)]

theorem row48_binding : (data.drop 48).take 1 = (originalEntries.drop 48).take 1 :=
  row48_view.trans (row48_source.trans row48_entry.symm)

numeric_data_binding row49_view : (data.drop 49).take 1 = (data49.drop 0).take 1

numeric_data_binding row49_source : (data49.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf24).isSome))]

numeric_data_binding row49_entry : (originalEntries.drop 49).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf24).isSome))]

theorem row49_binding : (data.drop 49).take 1 = (originalEntries.drop 49).take 1 :=
  row49_view.trans (row49_source.trans row49_entry.symm)

numeric_data_binding row50_view : (data.drop 50).take 1 = (data49.drop 1).take 1

numeric_data_binding row50_source : (data49.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw24).inputs)]

numeric_data_binding row50_entry : (originalEntries.drop 50).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw24).inputs)]

theorem row50_binding : (data.drop 50).take 1 = (originalEntries.drop 50).take 1 :=
  row50_view.trans (row50_source.trans row50_entry.symm)

numeric_data_binding row51_view : (data.drop 51).take 1 = (data49.drop 2).take 1

numeric_data_binding row51_source : (data49.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf25).isSome))]

numeric_data_binding row51_entry : (originalEntries.drop 51).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf25).isSome))]

theorem row51_binding : (data.drop 51).take 1 = (originalEntries.drop 51).take 1 :=
  row51_view.trans (row51_source.trans row51_entry.symm)

numeric_data_binding row52_view : (data.drop 52).take 1 = (data49.drop 3).take 1

numeric_data_binding row52_source : (data49.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw25).inputs)]

numeric_data_binding row52_entry : (originalEntries.drop 52).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw25).inputs)]

theorem row52_binding : (data.drop 52).take 1 = (originalEntries.drop 52).take 1 :=
  row52_view.trans (row52_source.trans row52_entry.symm)

numeric_data_binding row53_view : (data.drop 53).take 1 = (data53.drop 0).take 1

numeric_data_binding row53_source : (data53.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf26).isSome))]

numeric_data_binding row53_entry : (originalEntries.drop 53).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf26).isSome))]

theorem row53_binding : (data.drop 53).take 1 = (originalEntries.drop 53).take 1 :=
  row53_view.trans (row53_source.trans row53_entry.symm)

numeric_data_binding row54_view : (data.drop 54).take 1 = (data53.drop 1).take 1

numeric_data_binding row54_source : (data53.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw26).inputs)]

numeric_data_binding row54_entry : (originalEntries.drop 54).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw26).inputs)]

theorem row54_binding : (data.drop 54).take 1 = (originalEntries.drop 54).take 1 :=
  row54_view.trans (row54_source.trans row54_entry.symm)

numeric_data_binding row55_view : (data.drop 55).take 1 = (data53.drop 2).take 1

numeric_data_binding row55_source : (data53.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf27).isSome))]

numeric_data_binding row55_entry : (originalEntries.drop 55).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf27).isSome))]

theorem row55_binding : (data.drop 55).take 1 = (originalEntries.drop 55).take 1 :=
  row55_view.trans (row55_source.trans row55_entry.symm)

numeric_data_binding row56_view : (data.drop 56).take 1 = (data53.drop 3).take 1

numeric_data_binding row56_source : (data53.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw27).inputs)]

numeric_data_binding row56_entry : (originalEntries.drop 56).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw27).inputs)]

theorem row56_binding : (data.drop 56).take 1 = (originalEntries.drop 56).take 1 :=
  row56_view.trans (row56_source.trans row56_entry.symm)

numeric_data_binding row57_view : (data.drop 57).take 1 = (data57.drop 0).take 1

numeric_data_binding row57_source : (data57.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf28).isSome))]

numeric_data_binding row57_entry : (originalEntries.drop 57).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf28).isSome))]

theorem row57_binding : (data.drop 57).take 1 = (originalEntries.drop 57).take 1 :=
  row57_view.trans (row57_source.trans row57_entry.symm)

numeric_data_binding row58_view : (data.drop 58).take 1 = (data57.drop 1).take 1

numeric_data_binding row58_source : (data57.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw28).inputs)]

numeric_data_binding row58_entry : (originalEntries.drop 58).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw28).inputs)]

theorem row58_binding : (data.drop 58).take 1 = (originalEntries.drop 58).take 1 :=
  row58_view.trans (row58_source.trans row58_entry.symm)

numeric_data_binding row59_view : (data.drop 59).take 1 = (data57.drop 2).take 1

numeric_data_binding row59_source : (data57.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf29).isSome))]

numeric_data_binding row59_entry : (originalEntries.drop 59).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.KeccakUncached.native.definitions [] Airbender.Compiler.MemoryNative.KeccakUncached.native.leaf29).isSome))]

theorem row59_binding : (data.drop 59).take 1 = (originalEntries.drop 59).take 1 :=
  row59_view.trans (row59_source.trans row59_entry.symm)

numeric_data_binding row60_view : (data.drop 60).take 1 = (data57.drop 3).take 1

numeric_data_binding row60_source : (data57.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw29).inputs)]

numeric_data_binding row60_entry : (originalEntries.drop 60).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing (Airbender.Compiler.MemoryNative.KeccakUncached.native.raw29).inputs)]

theorem row60_binding : (data.drop 60).take 1 = (originalEntries.drop 60).take 1 :=
  row60_view.trans (row60_source.trans row60_entry.symm)

numeric_data_binding row61_view : (data.drop 61).take 1 = (data61.drop 0).take 1

numeric_data_binding row61_source : (data61.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw0 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row61_entry : (originalEntries.drop 61).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw0 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row61_binding : (data.drop 61).take 1 = (originalEntries.drop 61).take 1 :=
  row61_view.trans (row61_source.trans row61_entry.symm)

numeric_data_binding row62_view : (data.drop 62).take 1 = (data61.drop 1).take 1

numeric_data_binding row62_source : (data61.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw1 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row62_entry : (originalEntries.drop 62).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw1 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row62_binding : (data.drop 62).take 1 = (originalEntries.drop 62).take 1 :=
  row62_view.trans (row62_source.trans row62_entry.symm)

numeric_data_binding row63_view : (data.drop 63).take 1 = (data61.drop 2).take 1

numeric_data_binding row63_source : (data61.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw4 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row63_entry : (originalEntries.drop 63).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw4 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row63_binding : (data.drop 63).take 1 = (originalEntries.drop 63).take 1 :=
  row63_view.trans (row63_source.trans row63_entry.symm)

numeric_data_binding row64_view : (data.drop 64).take 1 = (data61.drop 3).take 1

numeric_data_binding row64_source : (data61.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw5 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row64_entry : (originalEntries.drop 64).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw5 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row64_binding : (data.drop 64).take 1 = (originalEntries.drop 64).take 1 :=
  row64_view.trans (row64_source.trans row64_entry.symm)

numeric_data_binding row65_view : (data.drop 65).take 1 = (data65.drop 0).take 1

numeric_data_binding row65_source : (data65.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate4 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw8 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row65_entry : (originalEntries.drop 65).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate4 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw8 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row65_binding : (data.drop 65).take 1 = (originalEntries.drop 65).take 1 :=
  row65_view.trans (row65_source.trans row65_entry.symm)

numeric_data_binding row66_view : (data.drop 66).take 1 = (data65.drop 1).take 1

numeric_data_binding row66_source : (data65.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate5 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw9 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row66_entry : (originalEntries.drop 66).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate5 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw9 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row66_binding : (data.drop 66).take 1 = (originalEntries.drop 66).take 1 :=
  row66_view.trans (row66_source.trans row66_entry.symm)

numeric_data_binding row67_view : (data.drop 67).take 1 = (data65.drop 2).take 1

numeric_data_binding row67_source : (data65.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate6 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw12 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row67_entry : (originalEntries.drop 67).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate6 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw12 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row67_binding : (data.drop 67).take 1 = (originalEntries.drop 67).take 1 :=
  row67_view.trans (row67_source.trans row67_entry.symm)

numeric_data_binding row68_view : (data.drop 68).take 1 = (data65.drop 3).take 1

numeric_data_binding row68_source : (data65.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate7 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw13 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row68_entry : (originalEntries.drop 68).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate7 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw13 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row68_binding : (data.drop 68).take 1 = (originalEntries.drop 68).take 1 :=
  row68_view.trans (row68_source.trans row68_entry.symm)

numeric_data_binding row69_view : (data.drop 69).take 1 = (data69.drop 0).take 1

numeric_data_binding row69_source : (data69.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate8 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw16 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row69_entry : (originalEntries.drop 69).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate8 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw16 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row69_binding : (data.drop 69).take 1 = (originalEntries.drop 69).take 1 :=
  row69_view.trans (row69_source.trans row69_entry.symm)

numeric_data_binding row70_view : (data.drop 70).take 1 = (data69.drop 1).take 1

numeric_data_binding row70_source : (data69.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate9 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw17 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row70_entry : (originalEntries.drop 70).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate9 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw17 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row70_binding : (data.drop 70).take 1 = (originalEntries.drop 70).take 1 :=
  row70_view.trans (row70_source.trans row70_entry.symm)

numeric_data_binding row71_view : (data.drop 71).take 1 = (data69.drop 2).take 1

numeric_data_binding row71_source : (data69.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate10 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw20 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row71_entry : (originalEntries.drop 71).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate10 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw20 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row71_binding : (data.drop 71).take 1 = (originalEntries.drop 71).take 1 :=
  row71_view.trans (row71_source.trans row71_entry.symm)

numeric_data_binding row72_view : (data.drop 72).take 1 = (data69.drop 3).take 1

numeric_data_binding row72_source : (data69.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate11 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw21 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row72_entry : (originalEntries.drop 72).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate11 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw21 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row72_binding : (data.drop 72).take 1 = (originalEntries.drop 72).take 1 :=
  row72_view.trans (row72_source.trans row72_entry.symm)

numeric_data_binding row73_view : (data.drop 73).take 1 = (data73.drop 0).take 1

numeric_data_binding row73_source : (data73.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate12 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw24 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row73_entry : (originalEntries.drop 73).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate12 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw24 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row73_binding : (data.drop 73).take 1 = (originalEntries.drop 73).take 1 :=
  row73_view.trans (row73_source.trans row73_entry.symm)

numeric_data_binding row74_view : (data.drop 74).take 1 = (data73.drop 1).take 1

numeric_data_binding row74_source : (data73.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate13 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw25 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row74_entry : (originalEntries.drop 74).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate13 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw25 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row74_binding : (data.drop 74).take 1 = (originalEntries.drop 74).take 1 :=
  row74_view.trans (row74_source.trans row74_entry.symm)

numeric_data_binding row75_view : (data.drop 75).take 1 = (data73.drop 2).take 1

numeric_data_binding row75_source : (data73.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate14 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw28 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row75_entry : (originalEntries.drop 75).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadCertificate14 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw28 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row75_binding : (data.drop 75).take 1 = (originalEntries.drop 75).take 1 :=
  row75_view.trans (row75_source.trans row75_entry.symm)

numeric_data_binding row76_view : (data.drop 76).take 1 = (data73.drop 3).take 1

numeric_data_binding row76_source : (data73.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing [(GKRAddress.InnerLayer 4 0)])]

numeric_data_binding row76_entry : (originalEntries.drop 76).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing [(GKRAddress.InnerLayer 4 0)])]

theorem row76_binding : (data.drop 76).take 1 = (originalEntries.drop 76).take 1 :=
  row76_view.trans (row76_source.trans row76_entry.symm)

numeric_data_binding row77_view : (data.drop 77).take 1 = (data77.drop 0).take 1

numeric_data_binding row77_source : (data77.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw2 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row77_entry : (originalEntries.drop 77).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw2 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row77_binding : (data.drop 77).take 1 = (originalEntries.drop 77).take 1 :=
  row77_view.trans (row77_source.trans row77_entry.symm)

numeric_data_binding row78_view : (data.drop 78).take 1 = (data77.drop 1).take 1

numeric_data_binding row78_source : (data77.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw3 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row78_entry : (originalEntries.drop 78).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw3 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row78_binding : (data.drop 78).take 1 = (originalEntries.drop 78).take 1 :=
  row78_view.trans (row78_source.trans row78_entry.symm)

numeric_data_binding row79_view : (data.drop 79).take 1 = (data77.drop 2).take 1

numeric_data_binding row79_source : (data77.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw6 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row79_entry : (originalEntries.drop 79).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw6 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row79_binding : (data.drop 79).take 1 = (originalEntries.drop 79).take 1 :=
  row79_view.trans (row79_source.trans row79_entry.symm)

numeric_data_binding row80_view : (data.drop 80).take 1 = (data77.drop 3).take 1

numeric_data_binding row80_source : (data77.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw7 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row80_entry : (originalEntries.drop 80).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw7 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row80_binding : (data.drop 80).take 1 = (originalEntries.drop 80).take 1 :=
  row80_view.trans (row80_source.trans row80_entry.symm)

numeric_data_binding row81_view : (data.drop 81).take 1 = (data81.drop 0).take 1

numeric_data_binding row81_source : (data81.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate4 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw10 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row81_entry : (originalEntries.drop 81).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate4 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw10 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row81_binding : (data.drop 81).take 1 = (originalEntries.drop 81).take 1 :=
  row81_view.trans (row81_source.trans row81_entry.symm)

numeric_data_binding row82_view : (data.drop 82).take 1 = (data81.drop 1).take 1

numeric_data_binding row82_source : (data81.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate5 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw11 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row82_entry : (originalEntries.drop 82).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate5 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw11 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row82_binding : (data.drop 82).take 1 = (originalEntries.drop 82).take 1 :=
  row82_view.trans (row82_source.trans row82_entry.symm)

numeric_data_binding row83_view : (data.drop 83).take 1 = (data81.drop 2).take 1

numeric_data_binding row83_source : (data81.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate6 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw14 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row83_entry : (originalEntries.drop 83).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate6 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw14 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row83_binding : (data.drop 83).take 1 = (originalEntries.drop 83).take 1 :=
  row83_view.trans (row83_source.trans row83_entry.symm)

numeric_data_binding row84_view : (data.drop 84).take 1 = (data81.drop 3).take 1

numeric_data_binding row84_source : (data81.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate7 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw15 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row84_entry : (originalEntries.drop 84).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate7 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw15 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row84_binding : (data.drop 84).take 1 = (originalEntries.drop 84).take 1 :=
  row84_view.trans (row84_source.trans row84_entry.symm)

numeric_data_binding row85_view : (data.drop 85).take 1 = (data85.drop 0).take 1

numeric_data_binding row85_source : (data85.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate8 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw18 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row85_entry : (originalEntries.drop 85).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate8 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw18 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row85_binding : (data.drop 85).take 1 = (originalEntries.drop 85).take 1 :=
  row85_view.trans (row85_source.trans row85_entry.symm)

numeric_data_binding row86_view : (data.drop 86).take 1 = (data85.drop 1).take 1

numeric_data_binding row86_source : (data85.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate9 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw19 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row86_entry : (originalEntries.drop 86).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate9 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw19 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row86_binding : (data.drop 86).take 1 = (originalEntries.drop 86).take 1 :=
  row86_view.trans (row86_source.trans row86_entry.symm)

numeric_data_binding row87_view : (data.drop 87).take 1 = (data85.drop 2).take 1

numeric_data_binding row87_source : (data85.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate10 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw22 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row87_entry : (originalEntries.drop 87).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate10 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw22 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row87_binding : (data.drop 87).take 1 = (originalEntries.drop 87).take 1 :=
  row87_view.trans (row87_source.trans row87_entry.symm)

numeric_data_binding row88_view : (data.drop 88).take 1 = (data85.drop 3).take 1

numeric_data_binding row88_source : (data85.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate11 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw23 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row88_entry : (originalEntries.drop 88).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate11 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw23 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row88_binding : (data.drop 88).take 1 = (originalEntries.drop 88).take 1 :=
  row88_view.trans (row88_source.trans row88_entry.symm)

numeric_data_binding row89_view : (data.drop 89).take 1 = (data89.drop 0).take 1

numeric_data_binding row89_source : (data89.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate12 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw26 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row89_entry : (originalEntries.drop 89).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate12 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw26 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row89_binding : (data.drop 89).take 1 = (originalEntries.drop 89).take 1 :=
  row89_view.trans (row89_source.trans row89_entry.symm)

numeric_data_binding row90_view : (data.drop 90).take 1 = (data89.drop 1).take 1

numeric_data_binding row90_source : (data89.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate13 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw27 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row90_entry : (originalEntries.drop 90).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate13 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw27 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row90_binding : (data.drop 90).take 1 = (originalEntries.drop 90).take 1 :=
  row90_view.trans (row90_source.trans row90_entry.symm)

numeric_data_binding row91_view : (data.drop 91).take 1 = (data89.drop 2).take 1

numeric_data_binding row91_source : (data89.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate14 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw29 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

numeric_data_binding row91_entry : (originalEntries.drop 91).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteCertificate14 (((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.MemoryNative.KeccakUncached.native.raw29 Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing)]

theorem row91_binding : (data.drop 91).take 1 = (originalEntries.drop 91).take 1 :=
  row91_view.trans (row91_source.trans row91_entry.symm)

numeric_data_binding row92_view : (data.drop 92).take 1 = (data89.drop 3).take 1

numeric_data_binding row92_source : (data89.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing [(GKRAddress.InnerLayer 4 0)])]

numeric_data_binding row92_entry : (originalEntries.drop 92).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.KeccakUncached.native.bank Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing [(GKRAddress.InnerLayer 4 0)])]

theorem row92_binding : (data.drop 92).take 1 = (originalEntries.drop 92).take 1 :=
  row92_view.trans (row92_source.trans row92_entry.symm)

theorem entriesNode0_2 : (data.drop 0).take 2 = (originalEntries.drop 0).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 1 1 1 2 rfl rfl row0_binding row1_binding

theorem entriesNode3_2 : (data.drop 3).take 2 = (originalEntries.drop 3).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 3 1 1 4 2 rfl rfl row3_binding row4_binding

theorem entriesNode2_3 : (data.drop 2).take 3 = (originalEntries.drop 2).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 2 1 2 3 3 rfl rfl row2_binding entriesNode3_2

theorem entriesNode0_5 : (data.drop 0).take 5 = (originalEntries.drop 0).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 2 3 2 5 rfl rfl entriesNode0_2 entriesNode2_3

theorem entriesNode6_2 : (data.drop 6).take 2 = (originalEntries.drop 6).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 6 1 1 7 2 rfl rfl row6_binding row7_binding

theorem entriesNode5_3 : (data.drop 5).take 3 = (originalEntries.drop 5).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 5 1 2 6 3 rfl rfl row5_binding entriesNode6_2

theorem entriesNode9_2 : (data.drop 9).take 2 = (originalEntries.drop 9).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 9 1 1 10 2 rfl rfl row9_binding row10_binding

theorem entriesNode8_3 : (data.drop 8).take 3 = (originalEntries.drop 8).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 8 1 2 9 3 rfl rfl row8_binding entriesNode9_2

theorem entriesNode5_6 : (data.drop 5).take 6 = (originalEntries.drop 5).take 6 :=
  NumericWorkerPortChecks.merge_at data originalEntries 5 3 3 8 6 rfl rfl entriesNode5_3 entriesNode8_3

theorem entriesNode0_11 : (data.drop 0).take 11 = (originalEntries.drop 0).take 11 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 5 6 5 11 rfl rfl entriesNode0_5 entriesNode5_6

theorem entriesNode12_2 : (data.drop 12).take 2 = (originalEntries.drop 12).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 12 1 1 13 2 rfl rfl row12_binding row13_binding

theorem entriesNode11_3 : (data.drop 11).take 3 = (originalEntries.drop 11).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 11 1 2 12 3 rfl rfl row11_binding entriesNode12_2

theorem entriesNode15_2 : (data.drop 15).take 2 = (originalEntries.drop 15).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 15 1 1 16 2 rfl rfl row15_binding row16_binding

theorem entriesNode14_3 : (data.drop 14).take 3 = (originalEntries.drop 14).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 14 1 2 15 3 rfl rfl row14_binding entriesNode15_2

theorem entriesNode11_6 : (data.drop 11).take 6 = (originalEntries.drop 11).take 6 :=
  NumericWorkerPortChecks.merge_at data originalEntries 11 3 3 14 6 rfl rfl entriesNode11_3 entriesNode14_3

theorem entriesNode18_2 : (data.drop 18).take 2 = (originalEntries.drop 18).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 18 1 1 19 2 rfl rfl row18_binding row19_binding

theorem entriesNode17_3 : (data.drop 17).take 3 = (originalEntries.drop 17).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 17 1 2 18 3 rfl rfl row17_binding entriesNode18_2

theorem entriesNode21_2 : (data.drop 21).take 2 = (originalEntries.drop 21).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 21 1 1 22 2 rfl rfl row21_binding row22_binding

theorem entriesNode20_3 : (data.drop 20).take 3 = (originalEntries.drop 20).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 20 1 2 21 3 rfl rfl row20_binding entriesNode21_2

theorem entriesNode17_6 : (data.drop 17).take 6 = (originalEntries.drop 17).take 6 :=
  NumericWorkerPortChecks.merge_at data originalEntries 17 3 3 20 6 rfl rfl entriesNode17_3 entriesNode20_3

theorem entriesNode11_12 : (data.drop 11).take 12 = (originalEntries.drop 11).take 12 :=
  NumericWorkerPortChecks.merge_at data originalEntries 11 6 6 17 12 rfl rfl entriesNode11_6 entriesNode17_6

theorem entriesNode0_23 : (data.drop 0).take 23 = (originalEntries.drop 0).take 23 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 11 12 11 23 rfl rfl entriesNode0_11 entriesNode11_12

theorem entriesNode23_2 : (data.drop 23).take 2 = (originalEntries.drop 23).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 23 1 1 24 2 rfl rfl row23_binding row24_binding

theorem entriesNode26_2 : (data.drop 26).take 2 = (originalEntries.drop 26).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 26 1 1 27 2 rfl rfl row26_binding row27_binding

theorem entriesNode25_3 : (data.drop 25).take 3 = (originalEntries.drop 25).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 25 1 2 26 3 rfl rfl row25_binding entriesNode26_2

theorem entriesNode23_5 : (data.drop 23).take 5 = (originalEntries.drop 23).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 23 2 3 25 5 rfl rfl entriesNode23_2 entriesNode25_3

theorem entriesNode29_2 : (data.drop 29).take 2 = (originalEntries.drop 29).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 29 1 1 30 2 rfl rfl row29_binding row30_binding

theorem entriesNode28_3 : (data.drop 28).take 3 = (originalEntries.drop 28).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 28 1 2 29 3 rfl rfl row28_binding entriesNode29_2

theorem entriesNode32_2 : (data.drop 32).take 2 = (originalEntries.drop 32).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 32 1 1 33 2 rfl rfl row32_binding row33_binding

theorem entriesNode31_3 : (data.drop 31).take 3 = (originalEntries.drop 31).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 31 1 2 32 3 rfl rfl row31_binding entriesNode32_2

theorem entriesNode28_6 : (data.drop 28).take 6 = (originalEntries.drop 28).take 6 :=
  NumericWorkerPortChecks.merge_at data originalEntries 28 3 3 31 6 rfl rfl entriesNode28_3 entriesNode31_3

theorem entriesNode23_11 : (data.drop 23).take 11 = (originalEntries.drop 23).take 11 :=
  NumericWorkerPortChecks.merge_at data originalEntries 23 5 6 28 11 rfl rfl entriesNode23_5 entriesNode28_6

theorem entriesNode35_2 : (data.drop 35).take 2 = (originalEntries.drop 35).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 35 1 1 36 2 rfl rfl row35_binding row36_binding

theorem entriesNode34_3 : (data.drop 34).take 3 = (originalEntries.drop 34).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 34 1 2 35 3 rfl rfl row34_binding entriesNode35_2

theorem entriesNode38_2 : (data.drop 38).take 2 = (originalEntries.drop 38).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 38 1 1 39 2 rfl rfl row38_binding row39_binding

theorem entriesNode37_3 : (data.drop 37).take 3 = (originalEntries.drop 37).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 37 1 2 38 3 rfl rfl row37_binding entriesNode38_2

theorem entriesNode34_6 : (data.drop 34).take 6 = (originalEntries.drop 34).take 6 :=
  NumericWorkerPortChecks.merge_at data originalEntries 34 3 3 37 6 rfl rfl entriesNode34_3 entriesNode37_3

theorem entriesNode41_2 : (data.drop 41).take 2 = (originalEntries.drop 41).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 41 1 1 42 2 rfl rfl row41_binding row42_binding

theorem entriesNode40_3 : (data.drop 40).take 3 = (originalEntries.drop 40).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 40 1 2 41 3 rfl rfl row40_binding entriesNode41_2

theorem entriesNode44_2 : (data.drop 44).take 2 = (originalEntries.drop 44).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 44 1 1 45 2 rfl rfl row44_binding row45_binding

theorem entriesNode43_3 : (data.drop 43).take 3 = (originalEntries.drop 43).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 43 1 2 44 3 rfl rfl row43_binding entriesNode44_2

theorem entriesNode40_6 : (data.drop 40).take 6 = (originalEntries.drop 40).take 6 :=
  NumericWorkerPortChecks.merge_at data originalEntries 40 3 3 43 6 rfl rfl entriesNode40_3 entriesNode43_3

theorem entriesNode34_12 : (data.drop 34).take 12 = (originalEntries.drop 34).take 12 :=
  NumericWorkerPortChecks.merge_at data originalEntries 34 6 6 40 12 rfl rfl entriesNode34_6 entriesNode40_6

theorem entriesNode23_23 : (data.drop 23).take 23 = (originalEntries.drop 23).take 23 :=
  NumericWorkerPortChecks.merge_at data originalEntries 23 11 12 34 23 rfl rfl entriesNode23_11 entriesNode34_12

theorem entriesNode0_46 : (data.drop 0).take 46 = (originalEntries.drop 0).take 46 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 23 23 23 46 rfl rfl entriesNode0_23 entriesNode23_23

theorem entriesNode46_2 : (data.drop 46).take 2 = (originalEntries.drop 46).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 46 1 1 47 2 rfl rfl row46_binding row47_binding

theorem entriesNode49_2 : (data.drop 49).take 2 = (originalEntries.drop 49).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 49 1 1 50 2 rfl rfl row49_binding row50_binding

theorem entriesNode48_3 : (data.drop 48).take 3 = (originalEntries.drop 48).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 48 1 2 49 3 rfl rfl row48_binding entriesNode49_2

theorem entriesNode46_5 : (data.drop 46).take 5 = (originalEntries.drop 46).take 5 :=
  NumericWorkerPortChecks.merge_at data originalEntries 46 2 3 48 5 rfl rfl entriesNode46_2 entriesNode48_3

theorem entriesNode52_2 : (data.drop 52).take 2 = (originalEntries.drop 52).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 52 1 1 53 2 rfl rfl row52_binding row53_binding

theorem entriesNode51_3 : (data.drop 51).take 3 = (originalEntries.drop 51).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 51 1 2 52 3 rfl rfl row51_binding entriesNode52_2

theorem entriesNode55_2 : (data.drop 55).take 2 = (originalEntries.drop 55).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 55 1 1 56 2 rfl rfl row55_binding row56_binding

theorem entriesNode54_3 : (data.drop 54).take 3 = (originalEntries.drop 54).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 54 1 2 55 3 rfl rfl row54_binding entriesNode55_2

theorem entriesNode51_6 : (data.drop 51).take 6 = (originalEntries.drop 51).take 6 :=
  NumericWorkerPortChecks.merge_at data originalEntries 51 3 3 54 6 rfl rfl entriesNode51_3 entriesNode54_3

theorem entriesNode46_11 : (data.drop 46).take 11 = (originalEntries.drop 46).take 11 :=
  NumericWorkerPortChecks.merge_at data originalEntries 46 5 6 51 11 rfl rfl entriesNode46_5 entriesNode51_6

theorem entriesNode58_2 : (data.drop 58).take 2 = (originalEntries.drop 58).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 58 1 1 59 2 rfl rfl row58_binding row59_binding

theorem entriesNode57_3 : (data.drop 57).take 3 = (originalEntries.drop 57).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 57 1 2 58 3 rfl rfl row57_binding entriesNode58_2

theorem entriesNode61_2 : (data.drop 61).take 2 = (originalEntries.drop 61).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 61 1 1 62 2 rfl rfl row61_binding row62_binding

theorem entriesNode60_3 : (data.drop 60).take 3 = (originalEntries.drop 60).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 60 1 2 61 3 rfl rfl row60_binding entriesNode61_2

theorem entriesNode57_6 : (data.drop 57).take 6 = (originalEntries.drop 57).take 6 :=
  NumericWorkerPortChecks.merge_at data originalEntries 57 3 3 60 6 rfl rfl entriesNode57_3 entriesNode60_3

theorem entriesNode64_2 : (data.drop 64).take 2 = (originalEntries.drop 64).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 64 1 1 65 2 rfl rfl row64_binding row65_binding

theorem entriesNode63_3 : (data.drop 63).take 3 = (originalEntries.drop 63).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 63 1 2 64 3 rfl rfl row63_binding entriesNode64_2

theorem entriesNode67_2 : (data.drop 67).take 2 = (originalEntries.drop 67).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 67 1 1 68 2 rfl rfl row67_binding row68_binding

theorem entriesNode66_3 : (data.drop 66).take 3 = (originalEntries.drop 66).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 66 1 2 67 3 rfl rfl row66_binding entriesNode67_2

theorem entriesNode63_6 : (data.drop 63).take 6 = (originalEntries.drop 63).take 6 :=
  NumericWorkerPortChecks.merge_at data originalEntries 63 3 3 66 6 rfl rfl entriesNode63_3 entriesNode66_3

theorem entriesNode57_12 : (data.drop 57).take 12 = (originalEntries.drop 57).take 12 :=
  NumericWorkerPortChecks.merge_at data originalEntries 57 6 6 63 12 rfl rfl entriesNode57_6 entriesNode63_6

theorem entriesNode46_23 : (data.drop 46).take 23 = (originalEntries.drop 46).take 23 :=
  NumericWorkerPortChecks.merge_at data originalEntries 46 11 12 57 23 rfl rfl entriesNode46_11 entriesNode57_12

theorem entriesNode70_2 : (data.drop 70).take 2 = (originalEntries.drop 70).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 70 1 1 71 2 rfl rfl row70_binding row71_binding

theorem entriesNode69_3 : (data.drop 69).take 3 = (originalEntries.drop 69).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 69 1 2 70 3 rfl rfl row69_binding entriesNode70_2

theorem entriesNode73_2 : (data.drop 73).take 2 = (originalEntries.drop 73).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 73 1 1 74 2 rfl rfl row73_binding row74_binding

theorem entriesNode72_3 : (data.drop 72).take 3 = (originalEntries.drop 72).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 72 1 2 73 3 rfl rfl row72_binding entriesNode73_2

theorem entriesNode69_6 : (data.drop 69).take 6 = (originalEntries.drop 69).take 6 :=
  NumericWorkerPortChecks.merge_at data originalEntries 69 3 3 72 6 rfl rfl entriesNode69_3 entriesNode72_3

theorem entriesNode76_2 : (data.drop 76).take 2 = (originalEntries.drop 76).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 76 1 1 77 2 rfl rfl row76_binding row77_binding

theorem entriesNode75_3 : (data.drop 75).take 3 = (originalEntries.drop 75).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 75 1 2 76 3 rfl rfl row75_binding entriesNode76_2

theorem entriesNode79_2 : (data.drop 79).take 2 = (originalEntries.drop 79).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 79 1 1 80 2 rfl rfl row79_binding row80_binding

theorem entriesNode78_3 : (data.drop 78).take 3 = (originalEntries.drop 78).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 78 1 2 79 3 rfl rfl row78_binding entriesNode79_2

theorem entriesNode75_6 : (data.drop 75).take 6 = (originalEntries.drop 75).take 6 :=
  NumericWorkerPortChecks.merge_at data originalEntries 75 3 3 78 6 rfl rfl entriesNode75_3 entriesNode78_3

theorem entriesNode69_12 : (data.drop 69).take 12 = (originalEntries.drop 69).take 12 :=
  NumericWorkerPortChecks.merge_at data originalEntries 69 6 6 75 12 rfl rfl entriesNode69_6 entriesNode75_6

theorem entriesNode82_2 : (data.drop 82).take 2 = (originalEntries.drop 82).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 82 1 1 83 2 rfl rfl row82_binding row83_binding

theorem entriesNode81_3 : (data.drop 81).take 3 = (originalEntries.drop 81).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 81 1 2 82 3 rfl rfl row81_binding entriesNode82_2

theorem entriesNode85_2 : (data.drop 85).take 2 = (originalEntries.drop 85).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 85 1 1 86 2 rfl rfl row85_binding row86_binding

theorem entriesNode84_3 : (data.drop 84).take 3 = (originalEntries.drop 84).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 84 1 2 85 3 rfl rfl row84_binding entriesNode85_2

theorem entriesNode81_6 : (data.drop 81).take 6 = (originalEntries.drop 81).take 6 :=
  NumericWorkerPortChecks.merge_at data originalEntries 81 3 3 84 6 rfl rfl entriesNode81_3 entriesNode84_3

theorem entriesNode88_2 : (data.drop 88).take 2 = (originalEntries.drop 88).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 88 1 1 89 2 rfl rfl row88_binding row89_binding

theorem entriesNode87_3 : (data.drop 87).take 3 = (originalEntries.drop 87).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 87 1 2 88 3 rfl rfl row87_binding entriesNode88_2

theorem entriesNode91_2 : (data.drop 91).take 2 = (originalEntries.drop 91).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 91 1 1 92 2 rfl rfl row91_binding row92_binding

theorem entriesNode90_3 : (data.drop 90).take 3 = (originalEntries.drop 90).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 90 1 2 91 3 rfl rfl row90_binding entriesNode91_2

theorem entriesNode87_6 : (data.drop 87).take 6 = (originalEntries.drop 87).take 6 :=
  NumericWorkerPortChecks.merge_at data originalEntries 87 3 3 90 6 rfl rfl entriesNode87_3 entriesNode90_3

theorem entriesNode81_12 : (data.drop 81).take 12 = (originalEntries.drop 81).take 12 :=
  NumericWorkerPortChecks.merge_at data originalEntries 81 6 6 87 12 rfl rfl entriesNode81_6 entriesNode87_6

theorem entriesNode69_24 : (data.drop 69).take 24 = (originalEntries.drop 69).take 24 :=
  NumericWorkerPortChecks.merge_at data originalEntries 69 12 12 81 24 rfl rfl entriesNode69_12 entriesNode81_12

theorem entriesNode46_47 : (data.drop 46).take 47 = (originalEntries.drop 46).take 47 :=
  NumericWorkerPortChecks.merge_at data originalEntries 46 23 24 69 47 rfl rfl entriesNode46_23 entriesNode69_24

theorem entriesNode0_93 : (data.drop 0).take 93 = (originalEntries.drop 0).take 93 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 46 47 46 93 rfl rfl entriesNode0_46 entriesNode46_47

theorem source_binding : data = originalEntries :=
  NumericQueryFrameChecks.complete_binding data originalEntries 93
    (by decide +kernel) (by decide +kernel) entriesNode0_93

end Airbender.Compiler.MemoryPayloadChecks.KeccakUncached
