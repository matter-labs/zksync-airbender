import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.BlakeGUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.HelperPayloadChecks.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

attribute [local irreducible] originalEntries data

numeric_data_binding row0_view : (data.drop 0).take 1 = (data0.drop 0).take 1

numeric_data_binding row0_source : (data0.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate0
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row0_entry : ((originalEntries.drop 0).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate0
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row0_binding : (data.drop 0).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 1 :=
  row0_view.trans (row0_source.trans (row0_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 0 1)))

numeric_data_binding row1_view : (data.drop 1).take 1 = (data0.drop 1).take 1

numeric_data_binding row1_source : (data0.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate2
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row1_entry : ((originalEntries.drop 1).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate2
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row1_binding : (data.drop 1).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 1).take 1 :=
  row1_view.trans (row1_source.trans (row1_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 1 1)))

numeric_data_binding row2_view : (data.drop 2).take 1 = (data0.drop 2).take 1

numeric_data_binding row2_source : (data0.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate3
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row2_entry : ((originalEntries.drop 2).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate3
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row2_binding : (data.drop 2).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 2).take 1 :=
  row2_view.trans (row2_source.trans (row2_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 2 1)))

numeric_data_binding row3_view : (data.drop 3).take 1 = (data0.drop 3).take 1

numeric_data_binding row3_source : (data0.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate4
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row3_entry : ((originalEntries.drop 3).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate4
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row3_binding : (data.drop 3).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 3).take 1 :=
  row3_view.trans (row3_source.trans (row3_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 3 1)))

numeric_data_binding row4_view : (data.drop 4).take 1 = (data4.drop 0).take 1

numeric_data_binding row4_source : (data4.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate5
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row4_entry : ((originalEntries.drop 4).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate5
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row4_binding : (data.drop 4).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 4).take 1 :=
  row4_view.trans (row4_source.trans (row4_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 4 1)))

numeric_data_binding row5_view : (data.drop 5).take 1 = (data4.drop 1).take 1

numeric_data_binding row5_source : (data4.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate6
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row5_entry : ((originalEntries.drop 5).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate6
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row5_binding : (data.drop 5).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 5).take 1 :=
  row5_view.trans (row5_source.trans (row5_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 5 1)))

numeric_data_binding row6_view : (data.drop 6).take 1 = (data4.drop 2).take 1

numeric_data_binding row6_source : (data4.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate7
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row6_entry : ((originalEntries.drop 6).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate7
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row6_binding : (data.drop 6).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 6).take 1 :=
  row6_view.trans (row6_source.trans (row6_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 6 1)))

numeric_data_binding row7_view : (data.drop 7).take 1 = (data4.drop 3).take 1

numeric_data_binding row7_source : (data4.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate8
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row7_entry : ((originalEntries.drop 7).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate8
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row7_binding : (data.drop 7).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 7).take 1 :=
  row7_view.trans (row7_source.trans (row7_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 7 1)))

numeric_data_binding row8_view : (data.drop 8).take 1 = (data8.drop 0).take 1

numeric_data_binding row8_source : (data8.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate9
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row8_entry : ((originalEntries.drop 8).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate9
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row8_binding : (data.drop 8).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 1 :=
  row8_view.trans (row8_source.trans (row8_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 8 1)))

numeric_data_binding row9_view : (data.drop 9).take 1 = (data8.drop 1).take 1

numeric_data_binding row9_source : (data8.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate10
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row9_entry : ((originalEntries.drop 9).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate10
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row9_binding : (data.drop 9).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 9).take 1 :=
  row9_view.trans (row9_source.trans (row9_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 9 1)))

numeric_data_binding row10_view : (data.drop 10).take 1 = (data8.drop 2).take 1

numeric_data_binding row10_source : (data8.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate11
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row10_entry : ((originalEntries.drop 10).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate11
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row10_binding : (data.drop 10).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 10).take 1 :=
  row10_view.trans (row10_source.trans (row10_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 10 1)))

numeric_data_binding row11_view : (data.drop 11).take 1 = (data8.drop 3).take 1

numeric_data_binding row11_source : (data8.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate12
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row11_entry : ((originalEntries.drop 11).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate12
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row11_binding : (data.drop 11).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 11).take 1 :=
  row11_view.trans (row11_source.trans (row11_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 11 1)))

numeric_data_binding row12_view : (data.drop 12).take 1 = (data12.drop 0).take 1

numeric_data_binding row12_source : (data12.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate13
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row12_entry : ((originalEntries.drop 12).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate13
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row12_binding : (data.drop 12).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 12).take 1 :=
  row12_view.trans (row12_source.trans (row12_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 12 1)))

numeric_data_binding row13_view : (data.drop 13).take 1 = (data12.drop 1).take 1

numeric_data_binding row13_source : (data12.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate14
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row13_entry : ((originalEntries.drop 13).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate14
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row13_binding : (data.drop 13).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 13).take 1 :=
  row13_view.trans (row13_source.trans (row13_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 13 1)))

numeric_data_binding row14_view : (data.drop 14).take 1 = (data12.drop 2).take 1

numeric_data_binding row14_source : (data12.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate15
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row14_entry : ((originalEntries.drop 14).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate15
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row14_binding : (data.drop 14).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 14).take 1 :=
  row14_view.trans (row14_source.trans (row14_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 14 1)))

numeric_data_binding row15_view : (data.drop 15).take 1 = (data12.drop 3).take 1

numeric_data_binding row15_source : (data12.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate16
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row15_entry : ((originalEntries.drop 15).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate16
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row15_binding : (data.drop 15).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 15).take 1 :=
  row15_view.trans (row15_source.trans (row15_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 15 1)))

numeric_data_binding row16_view : (data.drop 16).take 1 = (data16.drop 0).take 1

numeric_data_binding row16_source : (data16.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate17
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row16_entry : ((originalEntries.drop 16).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate17
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row16_binding : (data.drop 16).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 1 :=
  row16_view.trans (row16_source.trans (row16_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 16 1)))

numeric_data_binding row17_view : (data.drop 17).take 1 = (data16.drop 1).take 1

numeric_data_binding row17_source : (data16.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate18
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row17_entry : ((originalEntries.drop 17).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate18
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row17_binding : (data.drop 17).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 17).take 1 :=
  row17_view.trans (row17_source.trans (row17_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 17 1)))

numeric_data_binding row18_view : (data.drop 18).take 1 = (data16.drop 2).take 1

numeric_data_binding row18_source : (data16.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate19
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row18_entry : ((originalEntries.drop 18).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate19
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row18_binding : (data.drop 18).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 18).take 1 :=
  row18_view.trans (row18_source.trans (row18_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 18 1)))

numeric_data_binding row19_view : (data.drop 19).take 1 = (data16.drop 3).take 1

numeric_data_binding row19_source : (data16.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate20
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row19_entry : ((originalEntries.drop 19).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate20
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row19_binding : (data.drop 19).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 19).take 1 :=
  row19_view.trans (row19_source.trans (row19_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 19 1)))

numeric_data_binding row20_view : (data.drop 20).take 1 = (data20.drop 0).take 1

numeric_data_binding row20_source : (data20.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate21
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

numeric_data_binding row20_entry : ((originalEntries.drop 20).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate21
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem row20_binding : (data.drop 20).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 20).take 1 :=
  row20_view.trans (row20_source.trans (row20_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 20 1)))

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

theorem entriesNode16_2 : (data.drop 16).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 16 1 1 17 2 rfl rfl row16_binding row17_binding

theorem entriesNode15_3 : (data.drop 15).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 15).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 15 1 2 16 3 rfl rfl row15_binding entriesNode16_2

theorem entriesNode19_2 : (data.drop 19).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 19).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 19 1 1 20 2 rfl rfl row19_binding row20_binding

theorem entriesNode18_3 : (data.drop 18).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 18).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 18 1 2 19 3 rfl rfl row18_binding entriesNode19_2

theorem entriesNode15_6 : (data.drop 15).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 15).take 6 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 15 3 3 18 6 rfl rfl entriesNode15_3 entriesNode18_3

theorem entriesNode10_11 : (data.drop 10).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 10).take 11 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 10 5 6 15 11 rfl rfl entriesNode10_5 entriesNode15_6

theorem entriesNode0_21 : (data.drop 0).take 21 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 21 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 10 11 10 21 rfl rfl entriesNode0_10 entriesNode10_11

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 21
    (by decide +kernel) (by decide +kernel) entriesNode0_21

end Airbender.Compiler.HelperPayloadChecks.BlakeGUncached
