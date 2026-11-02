import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.WordMemoryUncached.Data
import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.WordMemoryUncached.ProjectionBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.MemoryPayloadChecks.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

attribute [local irreducible] originalEntries data

numeric_data_binding row0_view : (data.drop 0).take 1 = [projectionData]

theorem row0_source : [projectionData] = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing Airbender.Compiler.MemoryNative.WordMemoryUncached.native.projectionInputs)] :=
  congrArg List.singleton projection_source_binding

numeric_data_binding row0_entry : (originalEntries.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing Airbender.Compiler.MemoryNative.WordMemoryUncached.native.projectionInputs)]

theorem row0_binding : (data.drop 0).take 1 = (originalEntries.drop 0).take 1 :=
  row0_view.trans (row0_source.trans row0_entry.symm)

numeric_data_binding row1_view : (data.drop 1).take 1 = (data1.drop 0).take 1

numeric_data_binding row1_source : (data1.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf0).isSome))]

numeric_data_binding row1_entry : (originalEntries.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf0).isSome))]

theorem row1_binding : (data.drop 1).take 1 = (originalEntries.drop 1).take 1 :=
  row1_view.trans (row1_source.trans row1_entry.symm)

numeric_data_binding row2_view : (data.drop 2).take 1 = (data1.drop 1).take 1

numeric_data_binding row2_source : (data1.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw0).inputs)]

numeric_data_binding row2_entry : (originalEntries.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw0).inputs)]

theorem row2_binding : (data.drop 2).take 1 = (originalEntries.drop 2).take 1 :=
  row2_view.trans (row2_source.trans row2_entry.symm)

numeric_data_binding row3_view : (data.drop 3).take 1 = (data1.drop 2).take 1

numeric_data_binding row3_source : (data1.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf1).isSome))]

numeric_data_binding row3_entry : (originalEntries.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf1).isSome))]

theorem row3_binding : (data.drop 3).take 1 = (originalEntries.drop 3).take 1 :=
  row3_view.trans (row3_source.trans row3_entry.symm)

numeric_data_binding row4_view : (data.drop 4).take 1 = (data1.drop 3).take 1

numeric_data_binding row4_source : (data1.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw1).inputs)]

numeric_data_binding row4_entry : (originalEntries.drop 4).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw1).inputs)]

theorem row4_binding : (data.drop 4).take 1 = (originalEntries.drop 4).take 1 :=
  row4_view.trans (row4_source.trans row4_entry.symm)

numeric_data_binding row5_view : (data.drop 5).take 1 = (data5.drop 0).take 1

numeric_data_binding row5_source : (data5.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf2).isSome))]

numeric_data_binding row5_entry : (originalEntries.drop 5).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf2).isSome))]

theorem row5_binding : (data.drop 5).take 1 = (originalEntries.drop 5).take 1 :=
  row5_view.trans (row5_source.trans row5_entry.symm)

numeric_data_binding row6_view : (data.drop 6).take 1 = (data5.drop 1).take 1

numeric_data_binding row6_source : (data5.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw2).inputs)]

numeric_data_binding row6_entry : (originalEntries.drop 6).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw2).inputs)]

theorem row6_binding : (data.drop 6).take 1 = (originalEntries.drop 6).take 1 :=
  row6_view.trans (row6_source.trans row6_entry.symm)

numeric_data_binding row7_view : (data.drop 7).take 1 = (data5.drop 2).take 1

numeric_data_binding row7_source : (data5.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf3).isSome))]

numeric_data_binding row7_entry : (originalEntries.drop 7).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf3).isSome))]

theorem row7_binding : (data.drop 7).take 1 = (originalEntries.drop 7).take 1 :=
  row7_view.trans (row7_source.trans row7_entry.symm)

numeric_data_binding row8_view : (data.drop 8).take 1 = (data5.drop 3).take 1

numeric_data_binding row8_source : (data5.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw3).inputs)]

numeric_data_binding row8_entry : (originalEntries.drop 8).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw3).inputs)]

theorem row8_binding : (data.drop 8).take 1 = (originalEntries.drop 8).take 1 :=
  row8_view.trans (row8_source.trans row8_entry.symm)

numeric_data_binding row9_view : (data.drop 9).take 1 = (data9.drop 0).take 1

numeric_data_binding row9_source : (data9.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf4).isSome))]

numeric_data_binding row9_entry : (originalEntries.drop 9).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf4).isSome))]

theorem row9_binding : (data.drop 9).take 1 = (originalEntries.drop 9).take 1 :=
  row9_view.trans (row9_source.trans row9_entry.symm)

numeric_data_binding row10_view : (data.drop 10).take 1 = (data9.drop 1).take 1

numeric_data_binding row10_source : (data9.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw4).inputs)]

numeric_data_binding row10_entry : (originalEntries.drop 10).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw4).inputs)]

theorem row10_binding : (data.drop 10).take 1 = (originalEntries.drop 10).take 1 :=
  row10_view.trans (row10_source.trans row10_entry.symm)

numeric_data_binding row11_view : (data.drop 11).take 1 = (data9.drop 2).take 1

numeric_data_binding row11_source : (data9.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf5).isSome))]

numeric_data_binding row11_entry : (originalEntries.drop 11).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf5).isSome))]

theorem row11_binding : (data.drop 11).take 1 = (originalEntries.drop 11).take 1 :=
  row11_view.trans (row11_source.trans row11_entry.symm)

numeric_data_binding row12_view : (data.drop 12).take 1 = (data9.drop 3).take 1

numeric_data_binding row12_source : (data9.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw5).inputs)]

numeric_data_binding row12_entry : (originalEntries.drop 12).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw5).inputs)]

theorem row12_binding : (data.drop 12).take 1 = (originalEntries.drop 12).take 1 :=
  row12_view.trans (row12_source.trans row12_entry.symm)

numeric_data_binding row13_view : (data.drop 13).take 1 = (data13.drop 0).take 1

numeric_data_binding row13_source : (data13.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf6).isSome))]

numeric_data_binding row13_entry : (originalEntries.drop 13).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf6).isSome))]

theorem row13_binding : (data.drop 13).take 1 = (originalEntries.drop 13).take 1 :=
  row13_view.trans (row13_source.trans row13_entry.symm)

numeric_data_binding row14_view : (data.drop 14).take 1 = (data13.drop 1).take 1

numeric_data_binding row14_source : (data13.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw6).inputs)]

numeric_data_binding row14_entry : (originalEntries.drop 14).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw6).inputs)]

theorem row14_binding : (data.drop 14).take 1 = (originalEntries.drop 14).take 1 :=
  row14_view.trans (row14_source.trans row14_entry.symm)

numeric_data_binding row15_view : (data.drop 15).take 1 = (data13.drop 2).take 1

numeric_data_binding row15_source : (data13.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf7).isSome))]

numeric_data_binding row15_entry : (originalEntries.drop 15).take 1 = [NumericFunctionalBaseChecks.encode (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.WordMemoryUncached.native.definitions [] Airbender.Compiler.MemoryNative.WordMemoryUncached.native.leaf7).isSome))]

theorem row15_binding : (data.drop 15).take 1 = (originalEntries.drop 15).take 1 :=
  row15_view.trans (row15_source.trans row15_entry.symm)

numeric_data_binding row16_view : (data.drop 16).take 1 = (data13.drop 3).take 1

numeric_data_binding row16_source : (data13.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw7).inputs)]

numeric_data_binding row16_entry : (originalEntries.drop 16).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing (Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw7).inputs)]

theorem row16_binding : (data.drop 16).take 1 = (originalEntries.drop 16).take 1 :=
  row16_view.trans (row16_source.trans row16_entry.symm)

numeric_data_binding row17_view : (data.drop 17).take 1 = (data17.drop 0).take 1

numeric_data_binding row17_source : (data17.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw0 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

numeric_data_binding row17_entry : (originalEntries.drop 17).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw0 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

theorem row17_binding : (data.drop 17).take 1 = (originalEntries.drop 17).take 1 :=
  row17_view.trans (row17_source.trans row17_entry.symm)

numeric_data_binding row18_view : (data.drop 18).take 1 = (data17.drop 1).take 1

numeric_data_binding row18_source : (data17.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw1 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

numeric_data_binding row18_entry : (originalEntries.drop 18).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw1 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

theorem row18_binding : (data.drop 18).take 1 = (originalEntries.drop 18).take 1 :=
  row18_view.trans (row18_source.trans row18_entry.symm)

numeric_data_binding row19_view : (data.drop 19).take 1 = (data17.drop 2).take 1

numeric_data_binding row19_source : (data17.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw4 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

numeric_data_binding row19_entry : (originalEntries.drop 19).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw4 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

theorem row19_binding : (data.drop 19).take 1 = (originalEntries.drop 19).take 1 :=
  row19_view.trans (row19_source.trans row19_entry.symm)

numeric_data_binding row20_view : (data.drop 20).take 1 = (data17.drop 3).take 1

numeric_data_binding row20_source : (data17.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw5 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

numeric_data_binding row20_entry : (originalEntries.drop 20).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw5 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

theorem row20_binding : (data.drop 20).take 1 = (originalEntries.drop 20).take 1 :=
  row20_view.trans (row20_source.trans row20_entry.symm)

numeric_data_binding row21_view : (data.drop 21).take 1 = (data21.drop 0).take 1

numeric_data_binding row21_source : (data21.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing [(GKRAddress.InnerLayer 2 4)])]

numeric_data_binding row21_entry : (originalEntries.drop 21).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing [(GKRAddress.InnerLayer 2 4)])]

theorem row21_binding : (data.drop 21).take 1 = (originalEntries.drop 21).take 1 :=
  row21_view.trans (row21_source.trans row21_entry.symm)

numeric_data_binding row22_view : (data.drop 22).take 1 = (data21.drop 1).take 1

numeric_data_binding row22_source : (data21.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw2 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

numeric_data_binding row22_entry : (originalEntries.drop 22).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw2 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

theorem row22_binding : (data.drop 22).take 1 = (originalEntries.drop 22).take 1 :=
  row22_view.trans (row22_source.trans row22_entry.symm)

numeric_data_binding row23_view : (data.drop 23).take 1 = (data21.drop 2).take 1

numeric_data_binding row23_source : (data21.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw3 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

numeric_data_binding row23_entry : (originalEntries.drop 23).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw3 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

theorem row23_binding : (data.drop 23).take 1 = (originalEntries.drop 23).take 1 :=
  row23_view.trans (row23_source.trans row23_entry.symm)

numeric_data_binding row24_view : (data.drop 24).take 1 = (data21.drop 3).take 1

numeric_data_binding row24_source : (data21.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw6 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

numeric_data_binding row24_entry : (originalEntries.drop 24).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw6 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

theorem row24_binding : (data.drop 24).take 1 = (originalEntries.drop 24).take 1 :=
  row24_view.trans (row24_source.trans row24_entry.symm)

numeric_data_binding row25_view : (data.drop 25).take 1 = (data25.drop 0).take 1

numeric_data_binding row25_source : (data25.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw7 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

numeric_data_binding row25_entry : (originalEntries.drop 25).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.MemoryNative.WordMemoryUncached.native.raw7 Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing)]

theorem row25_binding : (data.drop 25).take 1 = (originalEntries.drop 25).take 1 :=
  row25_view.trans (row25_source.trans row25_entry.symm)

numeric_data_binding row26_view : (data.drop 26).take 1 = (data25.drop 1).take 1

numeric_data_binding row26_source : (data25.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing [(GKRAddress.InnerLayer 2 4)])]

numeric_data_binding row26_entry : (originalEntries.drop 26).take 1 = [NumericFunctionalBaseChecks.encode (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.WordMemoryUncached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.WordMemoryUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing [(GKRAddress.InnerLayer 2 4)])]

theorem row26_binding : (data.drop 26).take 1 = (originalEntries.drop 26).take 1 :=
  row26_view.trans (row26_source.trans row26_entry.symm)

theorem entriesNode1_2 : (data.drop 1).take 2 = (originalEntries.drop 1).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 1 1 1 2 2 rfl rfl row1_binding row2_binding

theorem entriesNode0_3 : (data.drop 0).take 3 = (originalEntries.drop 0).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 1 2 1 3 rfl rfl row0_binding entriesNode1_2

theorem entriesNode4_2 : (data.drop 4).take 2 = (originalEntries.drop 4).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 4 1 1 5 2 rfl rfl row4_binding row5_binding

theorem entriesNode3_3 : (data.drop 3).take 3 = (originalEntries.drop 3).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 3 1 2 4 3 rfl rfl row3_binding entriesNode4_2

theorem entriesNode0_6 : (data.drop 0).take 6 = (originalEntries.drop 0).take 6 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 3 3 3 6 rfl rfl entriesNode0_3 entriesNode3_3

theorem entriesNode7_2 : (data.drop 7).take 2 = (originalEntries.drop 7).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 7 1 1 8 2 rfl rfl row7_binding row8_binding

theorem entriesNode6_3 : (data.drop 6).take 3 = (originalEntries.drop 6).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 6 1 2 7 3 rfl rfl row6_binding entriesNode7_2

theorem entriesNode9_2 : (data.drop 9).take 2 = (originalEntries.drop 9).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 9 1 1 10 2 rfl rfl row9_binding row10_binding

theorem entriesNode11_2 : (data.drop 11).take 2 = (originalEntries.drop 11).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 11 1 1 12 2 rfl rfl row11_binding row12_binding

theorem entriesNode9_4 : (data.drop 9).take 4 = (originalEntries.drop 9).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 9 2 2 11 4 rfl rfl entriesNode9_2 entriesNode11_2

theorem entriesNode6_7 : (data.drop 6).take 7 = (originalEntries.drop 6).take 7 :=
  NumericWorkerPortChecks.merge_at data originalEntries 6 3 4 9 7 rfl rfl entriesNode6_3 entriesNode9_4

theorem entriesNode0_13 : (data.drop 0).take 13 = (originalEntries.drop 0).take 13 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 6 7 6 13 rfl rfl entriesNode0_6 entriesNode6_7

theorem entriesNode14_2 : (data.drop 14).take 2 = (originalEntries.drop 14).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 14 1 1 15 2 rfl rfl row14_binding row15_binding

theorem entriesNode13_3 : (data.drop 13).take 3 = (originalEntries.drop 13).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 13 1 2 14 3 rfl rfl row13_binding entriesNode14_2

theorem entriesNode16_2 : (data.drop 16).take 2 = (originalEntries.drop 16).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 16 1 1 17 2 rfl rfl row16_binding row17_binding

theorem entriesNode18_2 : (data.drop 18).take 2 = (originalEntries.drop 18).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 18 1 1 19 2 rfl rfl row18_binding row19_binding

theorem entriesNode16_4 : (data.drop 16).take 4 = (originalEntries.drop 16).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 16 2 2 18 4 rfl rfl entriesNode16_2 entriesNode18_2

theorem entriesNode13_7 : (data.drop 13).take 7 = (originalEntries.drop 13).take 7 :=
  NumericWorkerPortChecks.merge_at data originalEntries 13 3 4 16 7 rfl rfl entriesNode13_3 entriesNode16_4

theorem entriesNode21_2 : (data.drop 21).take 2 = (originalEntries.drop 21).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 21 1 1 22 2 rfl rfl row21_binding row22_binding

theorem entriesNode20_3 : (data.drop 20).take 3 = (originalEntries.drop 20).take 3 :=
  NumericWorkerPortChecks.merge_at data originalEntries 20 1 2 21 3 rfl rfl row20_binding entriesNode21_2

theorem entriesNode23_2 : (data.drop 23).take 2 = (originalEntries.drop 23).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 23 1 1 24 2 rfl rfl row23_binding row24_binding

theorem entriesNode25_2 : (data.drop 25).take 2 = (originalEntries.drop 25).take 2 :=
  NumericWorkerPortChecks.merge_at data originalEntries 25 1 1 26 2 rfl rfl row25_binding row26_binding

theorem entriesNode23_4 : (data.drop 23).take 4 = (originalEntries.drop 23).take 4 :=
  NumericWorkerPortChecks.merge_at data originalEntries 23 2 2 25 4 rfl rfl entriesNode23_2 entriesNode25_2

theorem entriesNode20_7 : (data.drop 20).take 7 = (originalEntries.drop 20).take 7 :=
  NumericWorkerPortChecks.merge_at data originalEntries 20 3 4 23 7 rfl rfl entriesNode20_3 entriesNode23_4

theorem entriesNode13_14 : (data.drop 13).take 14 = (originalEntries.drop 13).take 14 :=
  NumericWorkerPortChecks.merge_at data originalEntries 13 7 7 20 14 rfl rfl entriesNode13_7 entriesNode20_7

theorem entriesNode0_27 : (data.drop 0).take 27 = (originalEntries.drop 0).take 27 :=
  NumericWorkerPortChecks.merge_at data originalEntries 0 13 14 13 27 rfl rfl entriesNode0_13 entriesNode13_14

theorem source_binding : data = originalEntries :=
  NumericQueryFrameChecks.complete_binding data originalEntries 27
    (by decide +kernel) (by decide +kernel) entriesNode0_27

end Airbender.Compiler.MemoryPayloadChecks.WordMemoryUncached
