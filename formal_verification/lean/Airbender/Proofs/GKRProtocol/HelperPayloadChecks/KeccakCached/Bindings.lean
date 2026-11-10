import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.KeccakCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.HelperPayloadChecks.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

attribute [local irreducible] originalEntries data

numeric_data_binding row0_view : (data.drop 0).take 1 = (data0.drop 0).take 1

numeric_data_binding row0_source : (data0.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate0
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row0_entry : ((originalEntries.drop 0).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate0
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row0_binding : (data.drop 0).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 1 :=
  row0_view.trans (row0_source.trans (row0_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 0 1)))

numeric_data_binding row1_view : (data.drop 1).take 1 = (data0.drop 1).take 1

numeric_data_binding row1_source : (data0.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate2
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row1_entry : ((originalEntries.drop 1).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate2
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row1_binding : (data.drop 1).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 1).take 1 :=
  row1_view.trans (row1_source.trans (row1_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 1 1)))

numeric_data_binding row2_view : (data.drop 2).take 1 = (data0.drop 2).take 1

numeric_data_binding row2_source : (data0.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate3
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row2_entry : ((originalEntries.drop 2).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate3
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row2_binding : (data.drop 2).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 2).take 1 :=
  row2_view.trans (row2_source.trans (row2_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 2 1)))

numeric_data_binding row3_view : (data.drop 3).take 1 = (data0.drop 3).take 1

numeric_data_binding row3_source : (data0.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate4
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row3_entry : ((originalEntries.drop 3).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate4
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row3_binding : (data.drop 3).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 3).take 1 :=
  row3_view.trans (row3_source.trans (row3_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 3 1)))

numeric_data_binding row4_view : (data.drop 4).take 1 = (data4.drop 0).take 1

numeric_data_binding row4_source : (data4.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate5
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row4_entry : ((originalEntries.drop 4).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate5
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row4_binding : (data.drop 4).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 4).take 1 :=
  row4_view.trans (row4_source.trans (row4_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 4 1)))

numeric_data_binding row5_view : (data.drop 5).take 1 = (data4.drop 1).take 1

numeric_data_binding row5_source : (data4.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate6
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row5_entry : ((originalEntries.drop 5).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate6
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row5_binding : (data.drop 5).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 5).take 1 :=
  row5_view.trans (row5_source.trans (row5_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 5 1)))

numeric_data_binding row6_view : (data.drop 6).take 1 = (data4.drop 2).take 1

numeric_data_binding row6_source : (data4.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate7
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row6_entry : ((originalEntries.drop 6).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate7
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row6_binding : (data.drop 6).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 6).take 1 :=
  row6_view.trans (row6_source.trans (row6_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 6 1)))

numeric_data_binding row7_view : (data.drop 7).take 1 = (data4.drop 3).take 1

numeric_data_binding row7_source : (data4.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate8
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row7_entry : ((originalEntries.drop 7).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate8
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row7_binding : (data.drop 7).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 7).take 1 :=
  row7_view.trans (row7_source.trans (row7_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 7 1)))

numeric_data_binding row8_view : (data.drop 8).take 1 = (data8.drop 0).take 1

numeric_data_binding row8_source : (data8.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate9
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row8_entry : ((originalEntries.drop 8).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate9
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row8_binding : (data.drop 8).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 1 :=
  row8_view.trans (row8_source.trans (row8_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 8 1)))

numeric_data_binding row9_view : (data.drop 9).take 1 = (data8.drop 1).take 1

numeric_data_binding row9_source : (data8.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate10
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row9_entry : ((originalEntries.drop 9).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate10
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row9_binding : (data.drop 9).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 9).take 1 :=
  row9_view.trans (row9_source.trans (row9_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 9 1)))

numeric_data_binding row10_view : (data.drop 10).take 1 = (data8.drop 2).take 1

numeric_data_binding row10_source : (data8.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate11
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row10_entry : ((originalEntries.drop 10).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate11
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row10_binding : (data.drop 10).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 10).take 1 :=
  row10_view.trans (row10_source.trans (row10_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 10 1)))

numeric_data_binding row11_view : (data.drop 11).take 1 = (data8.drop 3).take 1

numeric_data_binding row11_source : (data8.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate12
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row11_entry : ((originalEntries.drop 11).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate12
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row11_binding : (data.drop 11).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 11).take 1 :=
  row11_view.trans (row11_source.trans (row11_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 11 1)))

numeric_data_binding row12_view : (data.drop 12).take 1 = (data12.drop 0).take 1

numeric_data_binding row12_source : (data12.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate13
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row12_entry : ((originalEntries.drop 12).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate13
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row12_binding : (data.drop 12).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 12).take 1 :=
  row12_view.trans (row12_source.trans (row12_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 12 1)))

numeric_data_binding row13_view : (data.drop 13).take 1 = (data12.drop 1).take 1

numeric_data_binding row13_source : (data12.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate14
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row13_entry : ((originalEntries.drop 13).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate14
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row13_binding : (data.drop 13).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 13).take 1 :=
  row13_view.trans (row13_source.trans (row13_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 13 1)))

numeric_data_binding row14_view : (data.drop 14).take 1 = (data12.drop 2).take 1

numeric_data_binding row14_source : (data12.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate15
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row14_entry : ((originalEntries.drop 14).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate15
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row14_binding : (data.drop 14).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 14).take 1 :=
  row14_view.trans (row14_source.trans (row14_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 14 1)))

numeric_data_binding row15_view : (data.drop 15).take 1 = (data12.drop 3).take 1

numeric_data_binding row15_source : (data12.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate16
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row15_entry : ((originalEntries.drop 15).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate16
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row15_binding : (data.drop 15).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 15).take 1 :=
  row15_view.trans (row15_source.trans (row15_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 15 1)))

numeric_data_binding row16_view : (data.drop 16).take 1 = (data16.drop 0).take 1

numeric_data_binding row16_source : (data16.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate17
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row16_entry : ((originalEntries.drop 16).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate17
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row16_binding : (data.drop 16).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 1 :=
  row16_view.trans (row16_source.trans (row16_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 16 1)))

numeric_data_binding row17_view : (data.drop 17).take 1 = (data16.drop 1).take 1

numeric_data_binding row17_source : (data16.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate18
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row17_entry : ((originalEntries.drop 17).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate18
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row17_binding : (data.drop 17).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 17).take 1 :=
  row17_view.trans (row17_source.trans (row17_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 17 1)))

numeric_data_binding row18_view : (data.drop 18).take 1 = (data16.drop 2).take 1

numeric_data_binding row18_source : (data16.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate19
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row18_entry : ((originalEntries.drop 18).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate19
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row18_binding : (data.drop 18).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 18).take 1 :=
  row18_view.trans (row18_source.trans (row18_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 18 1)))

numeric_data_binding row19_view : (data.drop 19).take 1 = (data16.drop 3).take 1

numeric_data_binding row19_source : (data16.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate20
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row19_entry : ((originalEntries.drop 19).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate20
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row19_binding : (data.drop 19).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 19).take 1 :=
  row19_view.trans (row19_source.trans (row19_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 19 1)))

numeric_data_binding row20_view : (data.drop 20).take 1 = (data20.drop 0).take 1

numeric_data_binding row20_source : (data20.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate21
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row20_entry : ((originalEntries.drop 20).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate21
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row20_binding : (data.drop 20).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 20).take 1 :=
  row20_view.trans (row20_source.trans (row20_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 20 1)))

numeric_data_binding row21_view : (data.drop 21).take 1 = (data20.drop 1).take 1

numeric_data_binding row21_source : (data20.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate22
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row21_entry : ((originalEntries.drop 21).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate22
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row21_binding : (data.drop 21).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 21).take 1 :=
  row21_view.trans (row21_source.trans (row21_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 21 1)))

numeric_data_binding row22_view : (data.drop 22).take 1 = (data20.drop 2).take 1

numeric_data_binding row22_source : (data20.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate23
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row22_entry : ((originalEntries.drop 22).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate23
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row22_binding : (data.drop 22).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 1 :=
  row22_view.trans (row22_source.trans (row22_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 22 1)))

numeric_data_binding row23_view : (data.drop 23).take 1 = (data20.drop 3).take 1

numeric_data_binding row23_source : (data20.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate24
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row23_entry : ((originalEntries.drop 23).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate24
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row23_binding : (data.drop 23).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 23).take 1 :=
  row23_view.trans (row23_source.trans (row23_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 23 1)))

numeric_data_binding row24_view : (data.drop 24).take 1 = (data24.drop 0).take 1

numeric_data_binding row24_source : (data24.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate25
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row24_entry : ((originalEntries.drop 24).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate25
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row24_binding : (data.drop 24).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 1 :=
  row24_view.trans (row24_source.trans (row24_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 24 1)))

numeric_data_binding row25_view : (data.drop 25).take 1 = (data24.drop 1).take 1

numeric_data_binding row25_source : (data24.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate26
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row25_entry : ((originalEntries.drop 25).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate26
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row25_binding : (data.drop 25).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 25).take 1 :=
  row25_view.trans (row25_source.trans (row25_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 25 1)))

numeric_data_binding row26_view : (data.drop 26).take 1 = (data24.drop 2).take 1

numeric_data_binding row26_source : (data24.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate27
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row26_entry : ((originalEntries.drop 26).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate27
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row26_binding : (data.drop 26).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 26).take 1 :=
  row26_view.trans (row26_source.trans (row26_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 26 1)))

numeric_data_binding row27_view : (data.drop 27).take 1 = (data24.drop 3).take 1

numeric_data_binding row27_source : (data24.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate28
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row27_entry : ((originalEntries.drop 27).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate28
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row27_binding : (data.drop 27).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 27).take 1 :=
  row27_view.trans (row27_source.trans (row27_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 27 1)))

numeric_data_binding row28_view : (data.drop 28).take 1 = (data28.drop 0).take 1

numeric_data_binding row28_source : (data28.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate29
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row28_entry : ((originalEntries.drop 28).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate29
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row28_binding : (data.drop 28).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 28).take 1 :=
  row28_view.trans (row28_source.trans (row28_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 28 1)))

numeric_data_binding row29_view : (data.drop 29).take 1 = (data28.drop 1).take 1

numeric_data_binding row29_source : (data28.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate72
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

numeric_data_binding row29_entry : ((originalEntries.drop 29).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.KeccakCached.native.candidate72
  Airbender.Compiler.HelperNative.KeccakCached.native.placement Airbender.Compiler.MemoryNative.KeccakCached.native.bank
  Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem row29_binding : (data.drop 29).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 29).take 1 :=
  row29_view.trans (row29_source.trans (row29_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 29 1)))

theorem entriesNode1_2 : (data.drop 1).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 1).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 1 1 1 2 2 rfl rfl row1_binding row2_binding

theorem entriesNode0_3 : (data.drop 0).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 1 2 1 3 rfl rfl row0_binding entriesNode1_2

theorem entriesNode3_2 : (data.drop 3).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 3).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 3 1 1 4 2 rfl rfl row3_binding row4_binding

theorem entriesNode5_2 : (data.drop 5).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 5).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 5 1 1 6 2 rfl rfl row5_binding row6_binding

theorem entriesNode3_4 : (data.drop 3).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 3).take 4 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 3 2 2 5 4 rfl rfl entriesNode3_2 entriesNode5_2

theorem entriesNode0_7 : (data.drop 0).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 7 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 3 4 3 7 rfl rfl entriesNode0_3 entriesNode3_4

theorem entriesNode7_2 : (data.drop 7).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 7).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 7 1 1 8 2 rfl rfl row7_binding row8_binding

theorem entriesNode9_2 : (data.drop 9).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 9).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 9 1 1 10 2 rfl rfl row9_binding row10_binding

theorem entriesNode7_4 : (data.drop 7).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 7).take 4 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 7 2 2 9 4 rfl rfl entriesNode7_2 entriesNode9_2

theorem entriesNode11_2 : (data.drop 11).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 11).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 11 1 1 12 2 rfl rfl row11_binding row12_binding

theorem entriesNode13_2 : (data.drop 13).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 13).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 13 1 1 14 2 rfl rfl row13_binding row14_binding

theorem entriesNode11_4 : (data.drop 11).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 11).take 4 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 11 2 2 13 4 rfl rfl entriesNode11_2 entriesNode13_2

theorem entriesNode7_8 : (data.drop 7).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 7).take 8 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 7 4 4 11 8 rfl rfl entriesNode7_4 entriesNode11_4

theorem entriesNode0_15 : (data.drop 0).take 15 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 15 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 7 8 7 15 rfl rfl entriesNode0_7 entriesNode7_8

theorem entriesNode16_2 : (data.drop 16).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 16 1 1 17 2 rfl rfl row16_binding row17_binding

theorem entriesNode15_3 : (data.drop 15).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 15).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 15 1 2 16 3 rfl rfl row15_binding entriesNode16_2

theorem entriesNode18_2 : (data.drop 18).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 18).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 18 1 1 19 2 rfl rfl row18_binding row19_binding

theorem entriesNode20_2 : (data.drop 20).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 20).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 20 1 1 21 2 rfl rfl row20_binding row21_binding

theorem entriesNode18_4 : (data.drop 18).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 18).take 4 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 18 2 2 20 4 rfl rfl entriesNode18_2 entriesNode20_2

theorem entriesNode15_7 : (data.drop 15).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 15).take 7 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 15 3 4 18 7 rfl rfl entriesNode15_3 entriesNode18_4

theorem entriesNode22_2 : (data.drop 22).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 22 1 1 23 2 rfl rfl row22_binding row23_binding

theorem entriesNode24_2 : (data.drop 24).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 24 1 1 25 2 rfl rfl row24_binding row25_binding

theorem entriesNode22_4 : (data.drop 22).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 4 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 22 2 2 24 4 rfl rfl entriesNode22_2 entriesNode24_2

theorem entriesNode26_2 : (data.drop 26).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 26).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 26 1 1 27 2 rfl rfl row26_binding row27_binding

theorem entriesNode28_2 : (data.drop 28).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 28).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 28 1 1 29 2 rfl rfl row28_binding row29_binding

theorem entriesNode26_4 : (data.drop 26).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 26).take 4 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 26 2 2 28 4 rfl rfl entriesNode26_2 entriesNode28_2

theorem entriesNode22_8 : (data.drop 22).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 8 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 22 4 4 26 8 rfl rfl entriesNode22_4 entriesNode26_4

theorem entriesNode15_15 : (data.drop 15).take 15 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 15).take 15 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 15 7 8 22 15 rfl rfl entriesNode15_7 entriesNode22_8

theorem entriesNode0_30 : (data.drop 0).take 30 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 30 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 15 15 15 30 rfl rfl entriesNode0_15 entriesNode15_15

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 30
    (by decide +kernel) (by decide +kernel) entriesNode0_30

end Airbender.Compiler.HelperPayloadChecks.KeccakCached
