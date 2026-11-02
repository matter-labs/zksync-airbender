import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.BigintUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.HelperPayloadChecks.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

attribute [local irreducible] originalEntries data

numeric_data_binding row0_view : (data.drop 0).take 1 = (data0.drop 0).take 1

numeric_data_binding row0_source : (data0.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate16
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row0_entry : ((originalEntries.drop 0).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate16
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row0_binding : (data.drop 0).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 1 :=
  row0_view.trans (row0_source.trans (row0_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 0 1)))

numeric_data_binding row1_view : (data.drop 1).take 1 = (data0.drop 1).take 1

numeric_data_binding row1_source : (data0.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate18
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row1_entry : ((originalEntries.drop 1).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate18
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row1_binding : (data.drop 1).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 1).take 1 :=
  row1_view.trans (row1_source.trans (row1_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 1 1)))

numeric_data_binding row2_view : (data.drop 2).take 1 = (data0.drop 2).take 1

numeric_data_binding row2_source : (data0.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate19
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row2_entry : ((originalEntries.drop 2).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate19
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row2_binding : (data.drop 2).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 2).take 1 :=
  row2_view.trans (row2_source.trans (row2_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 2 1)))

numeric_data_binding row3_view : (data.drop 3).take 1 = (data0.drop 3).take 1

numeric_data_binding row3_source : (data0.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate20
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row3_entry : ((originalEntries.drop 3).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate20
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row3_binding : (data.drop 3).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 3).take 1 :=
  row3_view.trans (row3_source.trans (row3_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 3 1)))

numeric_data_binding row4_view : (data.drop 4).take 1 = (data4.drop 0).take 1

numeric_data_binding row4_source : (data4.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate21
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row4_entry : ((originalEntries.drop 4).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate21
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row4_binding : (data.drop 4).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 4).take 1 :=
  row4_view.trans (row4_source.trans (row4_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 4 1)))

numeric_data_binding row5_view : (data.drop 5).take 1 = (data4.drop 1).take 1

numeric_data_binding row5_source : (data4.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate22
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row5_entry : ((originalEntries.drop 5).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate22
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row5_binding : (data.drop 5).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 5).take 1 :=
  row5_view.trans (row5_source.trans (row5_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 5 1)))

numeric_data_binding row6_view : (data.drop 6).take 1 = (data4.drop 2).take 1

numeric_data_binding row6_source : (data4.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate23
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row6_entry : ((originalEntries.drop 6).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate23
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row6_binding : (data.drop 6).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 6).take 1 :=
  row6_view.trans (row6_source.trans (row6_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 6 1)))

numeric_data_binding row7_view : (data.drop 7).take 1 = (data4.drop 3).take 1

numeric_data_binding row7_source : (data4.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate24
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row7_entry : ((originalEntries.drop 7).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate24
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row7_binding : (data.drop 7).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 7).take 1 :=
  row7_view.trans (row7_source.trans (row7_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 7 1)))

numeric_data_binding row8_view : (data.drop 8).take 1 = (data8.drop 0).take 1

numeric_data_binding row8_source : (data8.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate25
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row8_entry : ((originalEntries.drop 8).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate25
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row8_binding : (data.drop 8).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 1 :=
  row8_view.trans (row8_source.trans (row8_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 8 1)))

numeric_data_binding row9_view : (data.drop 9).take 1 = (data8.drop 1).take 1

numeric_data_binding row9_source : (data8.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate26
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row9_entry : ((originalEntries.drop 9).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate26
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row9_binding : (data.drop 9).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 9).take 1 :=
  row9_view.trans (row9_source.trans (row9_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 9 1)))

numeric_data_binding row10_view : (data.drop 10).take 1 = (data8.drop 2).take 1

numeric_data_binding row10_source : (data8.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate27
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row10_entry : ((originalEntries.drop 10).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate27
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row10_binding : (data.drop 10).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 10).take 1 :=
  row10_view.trans (row10_source.trans (row10_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 10 1)))

numeric_data_binding row11_view : (data.drop 11).take 1 = (data8.drop 3).take 1

numeric_data_binding row11_source : (data8.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate28
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row11_entry : ((originalEntries.drop 11).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate28
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row11_binding : (data.drop 11).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 11).take 1 :=
  row11_view.trans (row11_source.trans (row11_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 11 1)))

numeric_data_binding row12_view : (data.drop 12).take 1 = (data12.drop 0).take 1

numeric_data_binding row12_source : (data12.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate29
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row12_entry : ((originalEntries.drop 12).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate29
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row12_binding : (data.drop 12).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 12).take 1 :=
  row12_view.trans (row12_source.trans (row12_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 12 1)))

numeric_data_binding row13_view : (data.drop 13).take 1 = (data12.drop 1).take 1

numeric_data_binding row13_source : (data12.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate30
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row13_entry : ((originalEntries.drop 13).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate30
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row13_binding : (data.drop 13).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 13).take 1 :=
  row13_view.trans (row13_source.trans (row13_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 13 1)))

numeric_data_binding row14_view : (data.drop 14).take 1 = (data12.drop 2).take 1

numeric_data_binding row14_source : (data12.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate31
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row14_entry : ((originalEntries.drop 14).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate31
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row14_binding : (data.drop 14).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 14).take 1 :=
  row14_view.trans (row14_source.trans (row14_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 14 1)))

numeric_data_binding row15_view : (data.drop 15).take 1 = (data12.drop 3).take 1

numeric_data_binding row15_source : (data12.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate32
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row15_entry : ((originalEntries.drop 15).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate32
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row15_binding : (data.drop 15).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 15).take 1 :=
  row15_view.trans (row15_source.trans (row15_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 15 1)))

numeric_data_binding row16_view : (data.drop 16).take 1 = (data16.drop 0).take 1

numeric_data_binding row16_source : (data16.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate33
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row16_entry : ((originalEntries.drop 16).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate33
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row16_binding : (data.drop 16).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 1 :=
  row16_view.trans (row16_source.trans (row16_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 16 1)))

numeric_data_binding row17_view : (data.drop 17).take 1 = (data16.drop 1).take 1

numeric_data_binding row17_source : (data16.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate34
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row17_entry : ((originalEntries.drop 17).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate34
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row17_binding : (data.drop 17).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 17).take 1 :=
  row17_view.trans (row17_source.trans (row17_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 17 1)))

numeric_data_binding row18_view : (data.drop 18).take 1 = (data16.drop 2).take 1

numeric_data_binding row18_source : (data16.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate35
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row18_entry : ((originalEntries.drop 18).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate35
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row18_binding : (data.drop 18).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 18).take 1 :=
  row18_view.trans (row18_source.trans (row18_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 18 1)))

numeric_data_binding row19_view : (data.drop 19).take 1 = (data16.drop 3).take 1

numeric_data_binding row19_source : (data16.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate36
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row19_entry : ((originalEntries.drop 19).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate36
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row19_binding : (data.drop 19).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 19).take 1 :=
  row19_view.trans (row19_source.trans (row19_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 19 1)))

numeric_data_binding row20_view : (data.drop 20).take 1 = (data20.drop 0).take 1

numeric_data_binding row20_source : (data20.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate37
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row20_entry : ((originalEntries.drop 20).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate37
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row20_binding : (data.drop 20).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 20).take 1 :=
  row20_view.trans (row20_source.trans (row20_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 20 1)))

numeric_data_binding row21_view : (data.drop 21).take 1 = (data20.drop 1).take 1

numeric_data_binding row21_source : (data20.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate38
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row21_entry : ((originalEntries.drop 21).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate38
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row21_binding : (data.drop 21).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 21).take 1 :=
  row21_view.trans (row21_source.trans (row21_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 21 1)))

numeric_data_binding row22_view : (data.drop 22).take 1 = (data20.drop 2).take 1

numeric_data_binding row22_source : (data20.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate39
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row22_entry : ((originalEntries.drop 22).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate39
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row22_binding : (data.drop 22).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 1 :=
  row22_view.trans (row22_source.trans (row22_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 22 1)))

numeric_data_binding row23_view : (data.drop 23).take 1 = (data20.drop 3).take 1

numeric_data_binding row23_source : (data20.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate40
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row23_entry : ((originalEntries.drop 23).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate40
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row23_binding : (data.drop 23).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 23).take 1 :=
  row23_view.trans (row23_source.trans (row23_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 23 1)))

numeric_data_binding row24_view : (data.drop 24).take 1 = (data24.drop 0).take 1

numeric_data_binding row24_source : (data24.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate41
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row24_entry : ((originalEntries.drop 24).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate41
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row24_binding : (data.drop 24).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 1 :=
  row24_view.trans (row24_source.trans (row24_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 24 1)))

numeric_data_binding row25_view : (data.drop 25).take 1 = (data24.drop 1).take 1

numeric_data_binding row25_source : (data24.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate42
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row25_entry : ((originalEntries.drop 25).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate42
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row25_binding : (data.drop 25).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 25).take 1 :=
  row25_view.trans (row25_source.trans (row25_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 25 1)))

numeric_data_binding row26_view : (data.drop 26).take 1 = (data24.drop 2).take 1

numeric_data_binding row26_source : (data24.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate43
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row26_entry : ((originalEntries.drop 26).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate43
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row26_binding : (data.drop 26).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 26).take 1 :=
  row26_view.trans (row26_source.trans (row26_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 26 1)))

numeric_data_binding row27_view : (data.drop 27).take 1 = (data24.drop 3).take 1

numeric_data_binding row27_source : (data24.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate44
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row27_entry : ((originalEntries.drop 27).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate44
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row27_binding : (data.drop 27).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 27).take 1 :=
  row27_view.trans (row27_source.trans (row27_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 27 1)))

numeric_data_binding row28_view : (data.drop 28).take 1 = (data28.drop 0).take 1

numeric_data_binding row28_source : (data28.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate45
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row28_entry : ((originalEntries.drop 28).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate45
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row28_binding : (data.drop 28).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 28).take 1 :=
  row28_view.trans (row28_source.trans (row28_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 28 1)))

numeric_data_binding row29_view : (data.drop 29).take 1 = (data28.drop 1).take 1

numeric_data_binding row29_source : (data28.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate46
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row29_entry : ((originalEntries.drop 29).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate46
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row29_binding : (data.drop 29).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 29).take 1 :=
  row29_view.trans (row29_source.trans (row29_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 29 1)))

numeric_data_binding row30_view : (data.drop 30).take 1 = (data28.drop 2).take 1

numeric_data_binding row30_source : (data28.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate47
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row30_entry : ((originalEntries.drop 30).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate47
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row30_binding : (data.drop 30).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 30).take 1 :=
  row30_view.trans (row30_source.trans (row30_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 30 1)))

numeric_data_binding row31_view : (data.drop 31).take 1 = (data28.drop 3).take 1

numeric_data_binding row31_source : (data28.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate48
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row31_entry : ((originalEntries.drop 31).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate48
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row31_binding : (data.drop 31).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 31).take 1 :=
  row31_view.trans (row31_source.trans (row31_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 31 1)))

numeric_data_binding row32_view : (data.drop 32).take 1 = (data32.drop 0).take 1

numeric_data_binding row32_source : (data32.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate49
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row32_entry : ((originalEntries.drop 32).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate49
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row32_binding : (data.drop 32).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 1 :=
  row32_view.trans (row32_source.trans (row32_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 32 1)))

numeric_data_binding row33_view : (data.drop 33).take 1 = (data32.drop 1).take 1

numeric_data_binding row33_source : (data32.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate50
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row33_entry : ((originalEntries.drop 33).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate50
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row33_binding : (data.drop 33).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 33).take 1 :=
  row33_view.trans (row33_source.trans (row33_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 33 1)))

numeric_data_binding row34_view : (data.drop 34).take 1 = (data32.drop 2).take 1

numeric_data_binding row34_source : (data32.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate51
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row34_entry : ((originalEntries.drop 34).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate51
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row34_binding : (data.drop 34).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 34).take 1 :=
  row34_view.trans (row34_source.trans (row34_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 34 1)))

numeric_data_binding row35_view : (data.drop 35).take 1 = (data32.drop 3).take 1

numeric_data_binding row35_source : (data32.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate52
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row35_entry : ((originalEntries.drop 35).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate52
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row35_binding : (data.drop 35).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 35).take 1 :=
  row35_view.trans (row35_source.trans (row35_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 35 1)))

numeric_data_binding row36_view : (data.drop 36).take 1 = (data36.drop 0).take 1

numeric_data_binding row36_source : (data36.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate53
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row36_entry : ((originalEntries.drop 36).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate53
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row36_binding : (data.drop 36).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 36).take 1 :=
  row36_view.trans (row36_source.trans (row36_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 36 1)))

numeric_data_binding row37_view : (data.drop 37).take 1 = (data36.drop 1).take 1

numeric_data_binding row37_source : (data36.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate54
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row37_entry : ((originalEntries.drop 37).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate54
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row37_binding : (data.drop 37).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 37).take 1 :=
  row37_view.trans (row37_source.trans (row37_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 37 1)))

numeric_data_binding row38_view : (data.drop 38).take 1 = (data36.drop 2).take 1

numeric_data_binding row38_source : (data36.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate55
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row38_entry : ((originalEntries.drop 38).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate55
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row38_binding : (data.drop 38).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 38).take 1 :=
  row38_view.trans (row38_source.trans (row38_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 38 1)))

numeric_data_binding row39_view : (data.drop 39).take 1 = (data36.drop 3).take 1

numeric_data_binding row39_source : (data36.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate56
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row39_entry : ((originalEntries.drop 39).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate56
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row39_binding : (data.drop 39).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 39).take 1 :=
  row39_view.trans (row39_source.trans (row39_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 39 1)))

numeric_data_binding row40_view : (data.drop 40).take 1 = (data40.drop 0).take 1

numeric_data_binding row40_source : (data40.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate57
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

numeric_data_binding row40_entry : ((originalEntries.drop 40).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate57
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing)]

theorem row40_binding : (data.drop 40).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 40).take 1 :=
  row40_view.trans (row40_source.trans (row40_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 40 1)))

theorem entriesNode0_2 : (data.drop 0).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 1 1 1 2 rfl rfl row0_binding row1_binding

theorem entriesNode3_2 : (data.drop 3).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 3).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 3 1 1 4 2 rfl rfl row3_binding row4_binding

theorem entriesNode2_3 : (data.drop 2).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 2).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 2 1 2 3 3 rfl rfl row2_binding entriesNode3_2

theorem entriesNode0_5 : (data.drop 0).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 5 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 2 3 2 5 rfl rfl entriesNode0_2 entriesNode2_3

theorem entriesNode5_2 : (data.drop 5).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 5).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 5 1 1 6 2 rfl rfl row5_binding row6_binding

theorem entriesNode8_2 : (data.drop 8).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 8 1 1 9 2 rfl rfl row8_binding row9_binding

theorem entriesNode7_3 : (data.drop 7).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 7).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 7 1 2 8 3 rfl rfl row7_binding entriesNode8_2

theorem entriesNode5_5 : (data.drop 5).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 5).take 5 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 5 2 3 7 5 rfl rfl entriesNode5_2 entriesNode7_3

theorem entriesNode0_10 : (data.drop 0).take 10 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 10 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 5 5 5 10 rfl rfl entriesNode0_5 entriesNode5_5

theorem entriesNode10_2 : (data.drop 10).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 10).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 10 1 1 11 2 rfl rfl row10_binding row11_binding

theorem entriesNode13_2 : (data.drop 13).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 13).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 13 1 1 14 2 rfl rfl row13_binding row14_binding

theorem entriesNode12_3 : (data.drop 12).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 12).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 12 1 2 13 3 rfl rfl row12_binding entriesNode13_2

theorem entriesNode10_5 : (data.drop 10).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 10).take 5 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 10 2 3 12 5 rfl rfl entriesNode10_2 entriesNode12_3

theorem entriesNode15_2 : (data.drop 15).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 15).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 15 1 1 16 2 rfl rfl row15_binding row16_binding

theorem entriesNode18_2 : (data.drop 18).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 18).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 18 1 1 19 2 rfl rfl row18_binding row19_binding

theorem entriesNode17_3 : (data.drop 17).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 17).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 17 1 2 18 3 rfl rfl row17_binding entriesNode18_2

theorem entriesNode15_5 : (data.drop 15).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 15).take 5 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 15 2 3 17 5 rfl rfl entriesNode15_2 entriesNode17_3

theorem entriesNode10_10 : (data.drop 10).take 10 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 10).take 10 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 10 5 5 15 10 rfl rfl entriesNode10_5 entriesNode15_5

theorem entriesNode0_20 : (data.drop 0).take 20 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 20 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 10 10 10 20 rfl rfl entriesNode0_10 entriesNode10_10

theorem entriesNode20_2 : (data.drop 20).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 20).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 20 1 1 21 2 rfl rfl row20_binding row21_binding

theorem entriesNode23_2 : (data.drop 23).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 23).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 23 1 1 24 2 rfl rfl row23_binding row24_binding

theorem entriesNode22_3 : (data.drop 22).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 22 1 2 23 3 rfl rfl row22_binding entriesNode23_2

theorem entriesNode20_5 : (data.drop 20).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 20).take 5 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 20 2 3 22 5 rfl rfl entriesNode20_2 entriesNode22_3

theorem entriesNode25_2 : (data.drop 25).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 25).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 25 1 1 26 2 rfl rfl row25_binding row26_binding

theorem entriesNode28_2 : (data.drop 28).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 28).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 28 1 1 29 2 rfl rfl row28_binding row29_binding

theorem entriesNode27_3 : (data.drop 27).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 27).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 27 1 2 28 3 rfl rfl row27_binding entriesNode28_2

theorem entriesNode25_5 : (data.drop 25).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 25).take 5 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 25 2 3 27 5 rfl rfl entriesNode25_2 entriesNode27_3

theorem entriesNode20_10 : (data.drop 20).take 10 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 20).take 10 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 20 5 5 25 10 rfl rfl entriesNode20_5 entriesNode25_5

theorem entriesNode30_2 : (data.drop 30).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 30).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 30 1 1 31 2 rfl rfl row30_binding row31_binding

theorem entriesNode33_2 : (data.drop 33).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 33).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 33 1 1 34 2 rfl rfl row33_binding row34_binding

theorem entriesNode32_3 : (data.drop 32).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 1 2 33 3 rfl rfl row32_binding entriesNode33_2

theorem entriesNode30_5 : (data.drop 30).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 30).take 5 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 30 2 3 32 5 rfl rfl entriesNode30_2 entriesNode32_3

theorem entriesNode36_2 : (data.drop 36).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 36).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 36 1 1 37 2 rfl rfl row36_binding row37_binding

theorem entriesNode35_3 : (data.drop 35).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 35).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 35 1 2 36 3 rfl rfl row35_binding entriesNode36_2

theorem entriesNode39_2 : (data.drop 39).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 39).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 39 1 1 40 2 rfl rfl row39_binding row40_binding

theorem entriesNode38_3 : (data.drop 38).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 38).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 38 1 2 39 3 rfl rfl row38_binding entriesNode39_2

theorem entriesNode35_6 : (data.drop 35).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 35).take 6 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 35 3 3 38 6 rfl rfl entriesNode35_3 entriesNode38_3

theorem entriesNode30_11 : (data.drop 30).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 30).take 11 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 30 5 6 35 11 rfl rfl entriesNode30_5 entriesNode35_6

theorem entriesNode20_21 : (data.drop 20).take 21 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 20).take 21 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 20 10 11 30 21 rfl rfl entriesNode20_10 entriesNode30_11

theorem entriesNode0_41 : (data.drop 0).take 41 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 41 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 20 21 20 41 rfl rfl entriesNode0_20 entriesNode20_21

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 41
    (by decide +kernel) (by decide +kernel) entriesNode0_41

end Airbender.Compiler.HelperPayloadChecks.BigintUncached
