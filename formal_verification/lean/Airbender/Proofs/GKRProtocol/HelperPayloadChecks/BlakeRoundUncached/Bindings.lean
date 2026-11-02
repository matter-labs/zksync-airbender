import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.BlakeRoundUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.HelperPayloadChecks.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

attribute [local irreducible] originalEntries data

numeric_data_binding row0_view : (data.drop 0).take 1 = (data0.drop 0).take 1

numeric_data_binding row0_source : (data0.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate0
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row0_entry : ((originalEntries.drop 0).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate0
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row0_binding : (data.drop 0).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 1 :=
  row0_view.trans (row0_source.trans (row0_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 0 1)))

numeric_data_binding row1_view : (data.drop 1).take 1 = (data0.drop 1).take 1

numeric_data_binding row1_source : (data0.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate2
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row1_entry : ((originalEntries.drop 1).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate2
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row1_binding : (data.drop 1).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 1).take 1 :=
  row1_view.trans (row1_source.trans (row1_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 1 1)))

numeric_data_binding row2_view : (data.drop 2).take 1 = (data0.drop 2).take 1

numeric_data_binding row2_source : (data0.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate3
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row2_entry : ((originalEntries.drop 2).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate3
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row2_binding : (data.drop 2).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 2).take 1 :=
  row2_view.trans (row2_source.trans (row2_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 2 1)))

numeric_data_binding row3_view : (data.drop 3).take 1 = (data0.drop 3).take 1

numeric_data_binding row3_source : (data0.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate4
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row3_entry : ((originalEntries.drop 3).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate4
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row3_binding : (data.drop 3).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 3).take 1 :=
  row3_view.trans (row3_source.trans (row3_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 3 1)))

numeric_data_binding row4_view : (data.drop 4).take 1 = (data4.drop 0).take 1

numeric_data_binding row4_source : (data4.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate5
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row4_entry : ((originalEntries.drop 4).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate5
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row4_binding : (data.drop 4).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 4).take 1 :=
  row4_view.trans (row4_source.trans (row4_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 4 1)))

numeric_data_binding row5_view : (data.drop 5).take 1 = (data4.drop 1).take 1

numeric_data_binding row5_source : (data4.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate6
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row5_entry : ((originalEntries.drop 5).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate6
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row5_binding : (data.drop 5).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 5).take 1 :=
  row5_view.trans (row5_source.trans (row5_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 5 1)))

numeric_data_binding row6_view : (data.drop 6).take 1 = (data4.drop 2).take 1

numeric_data_binding row6_source : (data4.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate7
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row6_entry : ((originalEntries.drop 6).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate7
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row6_binding : (data.drop 6).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 6).take 1 :=
  row6_view.trans (row6_source.trans (row6_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 6 1)))

numeric_data_binding row7_view : (data.drop 7).take 1 = (data4.drop 3).take 1

numeric_data_binding row7_source : (data4.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate8
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row7_entry : ((originalEntries.drop 7).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate8
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row7_binding : (data.drop 7).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 7).take 1 :=
  row7_view.trans (row7_source.trans (row7_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 7 1)))

numeric_data_binding row8_view : (data.drop 8).take 1 = (data8.drop 0).take 1

numeric_data_binding row8_source : (data8.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate9
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row8_entry : ((originalEntries.drop 8).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate9
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row8_binding : (data.drop 8).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 1 :=
  row8_view.trans (row8_source.trans (row8_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 8 1)))

numeric_data_binding row9_view : (data.drop 9).take 1 = (data8.drop 1).take 1

numeric_data_binding row9_source : (data8.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate10
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row9_entry : ((originalEntries.drop 9).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate10
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row9_binding : (data.drop 9).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 9).take 1 :=
  row9_view.trans (row9_source.trans (row9_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 9 1)))

numeric_data_binding row10_view : (data.drop 10).take 1 = (data8.drop 2).take 1

numeric_data_binding row10_source : (data8.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate11
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row10_entry : ((originalEntries.drop 10).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate11
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row10_binding : (data.drop 10).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 10).take 1 :=
  row10_view.trans (row10_source.trans (row10_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 10 1)))

numeric_data_binding row11_view : (data.drop 11).take 1 = (data8.drop 3).take 1

numeric_data_binding row11_source : (data8.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate12
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row11_entry : ((originalEntries.drop 11).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate12
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row11_binding : (data.drop 11).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 11).take 1 :=
  row11_view.trans (row11_source.trans (row11_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 11 1)))

numeric_data_binding row12_view : (data.drop 12).take 1 = (data12.drop 0).take 1

numeric_data_binding row12_source : (data12.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate13
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row12_entry : ((originalEntries.drop 12).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate13
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row12_binding : (data.drop 12).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 12).take 1 :=
  row12_view.trans (row12_source.trans (row12_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 12 1)))

numeric_data_binding row13_view : (data.drop 13).take 1 = (data12.drop 1).take 1

numeric_data_binding row13_source : (data12.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate14
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row13_entry : ((originalEntries.drop 13).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate14
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row13_binding : (data.drop 13).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 13).take 1 :=
  row13_view.trans (row13_source.trans (row13_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 13 1)))

numeric_data_binding row14_view : (data.drop 14).take 1 = (data12.drop 2).take 1

numeric_data_binding row14_source : (data12.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate15
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row14_entry : ((originalEntries.drop 14).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate15
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row14_binding : (data.drop 14).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 14).take 1 :=
  row14_view.trans (row14_source.trans (row14_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 14 1)))

numeric_data_binding row15_view : (data.drop 15).take 1 = (data12.drop 3).take 1

numeric_data_binding row15_source : (data12.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate16
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row15_entry : ((originalEntries.drop 15).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate16
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row15_binding : (data.drop 15).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 15).take 1 :=
  row15_view.trans (row15_source.trans (row15_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 15 1)))

numeric_data_binding row16_view : (data.drop 16).take 1 = (data16.drop 0).take 1

numeric_data_binding row16_source : (data16.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate17
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row16_entry : ((originalEntries.drop 16).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate17
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row16_binding : (data.drop 16).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 1 :=
  row16_view.trans (row16_source.trans (row16_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 16 1)))

numeric_data_binding row17_view : (data.drop 17).take 1 = (data16.drop 1).take 1

numeric_data_binding row17_source : (data16.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate18
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row17_entry : ((originalEntries.drop 17).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate18
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row17_binding : (data.drop 17).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 17).take 1 :=
  row17_view.trans (row17_source.trans (row17_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 17 1)))

numeric_data_binding row18_view : (data.drop 18).take 1 = (data16.drop 2).take 1

numeric_data_binding row18_source : (data16.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate19
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row18_entry : ((originalEntries.drop 18).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate19
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row18_binding : (data.drop 18).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 18).take 1 :=
  row18_view.trans (row18_source.trans (row18_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 18 1)))

numeric_data_binding row19_view : (data.drop 19).take 1 = (data16.drop 3).take 1

numeric_data_binding row19_source : (data16.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate20
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row19_entry : ((originalEntries.drop 19).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate20
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row19_binding : (data.drop 19).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 19).take 1 :=
  row19_view.trans (row19_source.trans (row19_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 19 1)))

numeric_data_binding row20_view : (data.drop 20).take 1 = (data20.drop 0).take 1

numeric_data_binding row20_source : (data20.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate21
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row20_entry : ((originalEntries.drop 20).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate21
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row20_binding : (data.drop 20).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 20).take 1 :=
  row20_view.trans (row20_source.trans (row20_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 20 1)))

numeric_data_binding row21_view : (data.drop 21).take 1 = (data20.drop 1).take 1

numeric_data_binding row21_source : (data20.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate22
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row21_entry : ((originalEntries.drop 21).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate22
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row21_binding : (data.drop 21).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 21).take 1 :=
  row21_view.trans (row21_source.trans (row21_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 21 1)))

numeric_data_binding row22_view : (data.drop 22).take 1 = (data20.drop 2).take 1

numeric_data_binding row22_source : (data20.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate23
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row22_entry : ((originalEntries.drop 22).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate23
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row22_binding : (data.drop 22).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 1 :=
  row22_view.trans (row22_source.trans (row22_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 22 1)))

numeric_data_binding row23_view : (data.drop 23).take 1 = (data20.drop 3).take 1

numeric_data_binding row23_source : (data20.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate24
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row23_entry : ((originalEntries.drop 23).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate24
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row23_binding : (data.drop 23).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 23).take 1 :=
  row23_view.trans (row23_source.trans (row23_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 23 1)))

numeric_data_binding row24_view : (data.drop 24).take 1 = (data24.drop 0).take 1

numeric_data_binding row24_source : (data24.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate25
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row24_entry : ((originalEntries.drop 24).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate25
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row24_binding : (data.drop 24).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 1 :=
  row24_view.trans (row24_source.trans (row24_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 24 1)))

numeric_data_binding row25_view : (data.drop 25).take 1 = (data24.drop 1).take 1

numeric_data_binding row25_source : (data24.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate26
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row25_entry : ((originalEntries.drop 25).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate26
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row25_binding : (data.drop 25).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 25).take 1 :=
  row25_view.trans (row25_source.trans (row25_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 25 1)))

numeric_data_binding row26_view : (data.drop 26).take 1 = (data24.drop 2).take 1

numeric_data_binding row26_source : (data24.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate27
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row26_entry : ((originalEntries.drop 26).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate27
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row26_binding : (data.drop 26).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 26).take 1 :=
  row26_view.trans (row26_source.trans (row26_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 26 1)))

numeric_data_binding row27_view : (data.drop 27).take 1 = (data24.drop 3).take 1

numeric_data_binding row27_source : (data24.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate28
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row27_entry : ((originalEntries.drop 27).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate28
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row27_binding : (data.drop 27).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 27).take 1 :=
  row27_view.trans (row27_source.trans (row27_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 27 1)))

numeric_data_binding row28_view : (data.drop 28).take 1 = (data28.drop 0).take 1

numeric_data_binding row28_source : (data28.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate29
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row28_entry : ((originalEntries.drop 28).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate29
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row28_binding : (data.drop 28).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 28).take 1 :=
  row28_view.trans (row28_source.trans (row28_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 28 1)))

numeric_data_binding row29_view : (data.drop 29).take 1 = (data28.drop 1).take 1

numeric_data_binding row29_source : (data28.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate30
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row29_entry : ((originalEntries.drop 29).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate30
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row29_binding : (data.drop 29).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 29).take 1 :=
  row29_view.trans (row29_source.trans (row29_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 29 1)))

numeric_data_binding row30_view : (data.drop 30).take 1 = (data28.drop 2).take 1

numeric_data_binding row30_source : (data28.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate31
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row30_entry : ((originalEntries.drop 30).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate31
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row30_binding : (data.drop 30).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 30).take 1 :=
  row30_view.trans (row30_source.trans (row30_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 30 1)))

numeric_data_binding row31_view : (data.drop 31).take 1 = (data28.drop 3).take 1

numeric_data_binding row31_source : (data28.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate32
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row31_entry : ((originalEntries.drop 31).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate32
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row31_binding : (data.drop 31).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 31).take 1 :=
  row31_view.trans (row31_source.trans (row31_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 31 1)))

numeric_data_binding row32_view : (data.drop 32).take 1 = (data32.drop 0).take 1

numeric_data_binding row32_source : (data32.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate33
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row32_entry : ((originalEntries.drop 32).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate33
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row32_binding : (data.drop 32).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 1 :=
  row32_view.trans (row32_source.trans (row32_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 32 1)))

numeric_data_binding row33_view : (data.drop 33).take 1 = (data32.drop 1).take 1

numeric_data_binding row33_source : (data32.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate34
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row33_entry : ((originalEntries.drop 33).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate34
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row33_binding : (data.drop 33).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 33).take 1 :=
  row33_view.trans (row33_source.trans (row33_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 33 1)))

numeric_data_binding row34_view : (data.drop 34).take 1 = (data32.drop 2).take 1

numeric_data_binding row34_source : (data32.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate35
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row34_entry : ((originalEntries.drop 34).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate35
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row34_binding : (data.drop 34).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 34).take 1 :=
  row34_view.trans (row34_source.trans (row34_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 34 1)))

numeric_data_binding row35_view : (data.drop 35).take 1 = (data32.drop 3).take 1

numeric_data_binding row35_source : (data32.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate36
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row35_entry : ((originalEntries.drop 35).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate36
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row35_binding : (data.drop 35).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 35).take 1 :=
  row35_view.trans (row35_source.trans (row35_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 35 1)))

numeric_data_binding row36_view : (data.drop 36).take 1 = (data36.drop 0).take 1

numeric_data_binding row36_source : (data36.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate37
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row36_entry : ((originalEntries.drop 36).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate37
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row36_binding : (data.drop 36).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 36).take 1 :=
  row36_view.trans (row36_source.trans (row36_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 36 1)))

numeric_data_binding row37_view : (data.drop 37).take 1 = (data36.drop 1).take 1

numeric_data_binding row37_source : (data36.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate38
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row37_entry : ((originalEntries.drop 37).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate38
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row37_binding : (data.drop 37).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 37).take 1 :=
  row37_view.trans (row37_source.trans (row37_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 37 1)))

numeric_data_binding row38_view : (data.drop 38).take 1 = (data36.drop 2).take 1

numeric_data_binding row38_source : (data36.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate39
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row38_entry : ((originalEntries.drop 38).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate39
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row38_binding : (data.drop 38).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 38).take 1 :=
  row38_view.trans (row38_source.trans (row38_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 38 1)))

numeric_data_binding row39_view : (data.drop 39).take 1 = (data36.drop 3).take 1

numeric_data_binding row39_source : (data36.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate40
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row39_entry : ((originalEntries.drop 39).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate40
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row39_binding : (data.drop 39).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 39).take 1 :=
  row39_view.trans (row39_source.trans (row39_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 39 1)))

numeric_data_binding row40_view : (data.drop 40).take 1 = (data40.drop 0).take 1

numeric_data_binding row40_source : (data40.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate41
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row40_entry : ((originalEntries.drop 40).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate41
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row40_binding : (data.drop 40).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 40).take 1 :=
  row40_view.trans (row40_source.trans (row40_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 40 1)))

numeric_data_binding row41_view : (data.drop 41).take 1 = (data40.drop 1).take 1

numeric_data_binding row41_source : (data40.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate42
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row41_entry : ((originalEntries.drop 41).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate42
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row41_binding : (data.drop 41).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 41).take 1 :=
  row41_view.trans (row41_source.trans (row41_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 41 1)))

numeric_data_binding row42_view : (data.drop 42).take 1 = (data40.drop 2).take 1

numeric_data_binding row42_source : (data40.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate43
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row42_entry : ((originalEntries.drop 42).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate43
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row42_binding : (data.drop 42).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 42).take 1 :=
  row42_view.trans (row42_source.trans (row42_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 42 1)))

numeric_data_binding row43_view : (data.drop 43).take 1 = (data40.drop 3).take 1

numeric_data_binding row43_source : (data40.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate44
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row43_entry : ((originalEntries.drop 43).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate44
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row43_binding : (data.drop 43).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 43).take 1 :=
  row43_view.trans (row43_source.trans (row43_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 43 1)))

numeric_data_binding row44_view : (data.drop 44).take 1 = (data44.drop 0).take 1

numeric_data_binding row44_source : (data44.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate45
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row44_entry : ((originalEntries.drop 44).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate45
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row44_binding : (data.drop 44).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 1 :=
  row44_view.trans (row44_source.trans (row44_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 44 1)))

numeric_data_binding row45_view : (data.drop 45).take 1 = (data44.drop 1).take 1

numeric_data_binding row45_source : (data44.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate46
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row45_entry : ((originalEntries.drop 45).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate46
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row45_binding : (data.drop 45).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 45).take 1 :=
  row45_view.trans (row45_source.trans (row45_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 45 1)))

numeric_data_binding row46_view : (data.drop 46).take 1 = (data44.drop 2).take 1

numeric_data_binding row46_source : (data44.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate47
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row46_entry : ((originalEntries.drop 46).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate47
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row46_binding : (data.drop 46).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 46).take 1 :=
  row46_view.trans (row46_source.trans (row46_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 46 1)))

numeric_data_binding row47_view : (data.drop 47).take 1 = (data44.drop 3).take 1

numeric_data_binding row47_source : (data44.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate48
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row47_entry : ((originalEntries.drop 47).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate48
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row47_binding : (data.drop 47).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 47).take 1 :=
  row47_view.trans (row47_source.trans (row47_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 47 1)))

numeric_data_binding row48_view : (data.drop 48).take 1 = (data48.drop 0).take 1

numeric_data_binding row48_source : (data48.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate49
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row48_entry : ((originalEntries.drop 48).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate49
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row48_binding : (data.drop 48).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 48).take 1 :=
  row48_view.trans (row48_source.trans (row48_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 48 1)))

numeric_data_binding row49_view : (data.drop 49).take 1 = (data48.drop 1).take 1

numeric_data_binding row49_source : (data48.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate50
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row49_entry : ((originalEntries.drop 49).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate50
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row49_binding : (data.drop 49).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 49).take 1 :=
  row49_view.trans (row49_source.trans (row49_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 49 1)))

numeric_data_binding row50_view : (data.drop 50).take 1 = (data48.drop 2).take 1

numeric_data_binding row50_source : (data48.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate51
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row50_entry : ((originalEntries.drop 50).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate51
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row50_binding : (data.drop 50).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 50).take 1 :=
  row50_view.trans (row50_source.trans (row50_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 50 1)))

numeric_data_binding row51_view : (data.drop 51).take 1 = (data48.drop 3).take 1

numeric_data_binding row51_source : (data48.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate52
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row51_entry : ((originalEntries.drop 51).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate52
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row51_binding : (data.drop 51).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 51).take 1 :=
  row51_view.trans (row51_source.trans (row51_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 51 1)))

numeric_data_binding row52_view : (data.drop 52).take 1 = (data52.drop 0).take 1

numeric_data_binding row52_source : (data52.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate53
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row52_entry : ((originalEntries.drop 52).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate53
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row52_binding : (data.drop 52).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 52).take 1 :=
  row52_view.trans (row52_source.trans (row52_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 52 1)))

numeric_data_binding row53_view : (data.drop 53).take 1 = (data52.drop 1).take 1

numeric_data_binding row53_source : (data52.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate54
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row53_entry : ((originalEntries.drop 53).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate54
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row53_binding : (data.drop 53).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 53).take 1 :=
  row53_view.trans (row53_source.trans (row53_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 53 1)))

numeric_data_binding row54_view : (data.drop 54).take 1 = (data52.drop 2).take 1

numeric_data_binding row54_source : (data52.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate55
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row54_entry : ((originalEntries.drop 54).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate55
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row54_binding : (data.drop 54).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 54).take 1 :=
  row54_view.trans (row54_source.trans (row54_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 54 1)))

numeric_data_binding row55_view : (data.drop 55).take 1 = (data52.drop 3).take 1

numeric_data_binding row55_source : (data52.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate56
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row55_entry : ((originalEntries.drop 55).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate56
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row55_binding : (data.drop 55).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 55).take 1 :=
  row55_view.trans (row55_source.trans (row55_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 55 1)))

numeric_data_binding row56_view : (data.drop 56).take 1 = (data56.drop 0).take 1

numeric_data_binding row56_source : (data56.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate57
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row56_entry : ((originalEntries.drop 56).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate57
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row56_binding : (data.drop 56).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 56).take 1 :=
  row56_view.trans (row56_source.trans (row56_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 56 1)))

numeric_data_binding row57_view : (data.drop 57).take 1 = (data56.drop 1).take 1

numeric_data_binding row57_source : (data56.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate58
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row57_entry : ((originalEntries.drop 57).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate58
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row57_binding : (data.drop 57).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 57).take 1 :=
  row57_view.trans (row57_source.trans (row57_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 57 1)))

numeric_data_binding row58_view : (data.drop 58).take 1 = (data56.drop 2).take 1

numeric_data_binding row58_source : (data56.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate59
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row58_entry : ((originalEntries.drop 58).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate59
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row58_binding : (data.drop 58).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 58).take 1 :=
  row58_view.trans (row58_source.trans (row58_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 58 1)))

numeric_data_binding row59_view : (data.drop 59).take 1 = (data56.drop 3).take 1

numeric_data_binding row59_source : (data56.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate60
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row59_entry : ((originalEntries.drop 59).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate60
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row59_binding : (data.drop 59).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 59).take 1 :=
  row59_view.trans (row59_source.trans (row59_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 59 1)))

numeric_data_binding row60_view : (data.drop 60).take 1 = (data60.drop 0).take 1

numeric_data_binding row60_source : (data60.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate61
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row60_entry : ((originalEntries.drop 60).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate61
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row60_binding : (data.drop 60).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 60).take 1 :=
  row60_view.trans (row60_source.trans (row60_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 60 1)))

numeric_data_binding row61_view : (data.drop 61).take 1 = (data60.drop 1).take 1

numeric_data_binding row61_source : (data60.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate62
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row61_entry : ((originalEntries.drop 61).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate62
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row61_binding : (data.drop 61).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 61).take 1 :=
  row61_view.trans (row61_source.trans (row61_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 61 1)))

numeric_data_binding row62_view : (data.drop 62).take 1 = (data60.drop 2).take 1

numeric_data_binding row62_source : (data60.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate63
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row62_entry : ((originalEntries.drop 62).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate63
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row62_binding : (data.drop 62).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 62).take 1 :=
  row62_view.trans (row62_source.trans (row62_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 62 1)))

numeric_data_binding row63_view : (data.drop 63).take 1 = (data60.drop 3).take 1

numeric_data_binding row63_source : (data60.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate64
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row63_entry : ((originalEntries.drop 63).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate64
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row63_binding : (data.drop 63).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 63).take 1 :=
  row63_view.trans (row63_source.trans (row63_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 63 1)))

numeric_data_binding row64_view : (data.drop 64).take 1 = (data64.drop 0).take 1

numeric_data_binding row64_source : (data64.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate65
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row64_entry : ((originalEntries.drop 64).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate65
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row64_binding : (data.drop 64).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 1 :=
  row64_view.trans (row64_source.trans (row64_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 64 1)))

numeric_data_binding row65_view : (data.drop 65).take 1 = (data64.drop 1).take 1

numeric_data_binding row65_source : (data64.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate66
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row65_entry : ((originalEntries.drop 65).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate66
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row65_binding : (data.drop 65).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 65).take 1 :=
  row65_view.trans (row65_source.trans (row65_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 65 1)))

numeric_data_binding row66_view : (data.drop 66).take 1 = (data64.drop 2).take 1

numeric_data_binding row66_source : (data64.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate67
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row66_entry : ((originalEntries.drop 66).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate67
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row66_binding : (data.drop 66).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 66).take 1 :=
  row66_view.trans (row66_source.trans (row66_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 66 1)))

numeric_data_binding row67_view : (data.drop 67).take 1 = (data64.drop 3).take 1

numeric_data_binding row67_source : (data64.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate68
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row67_entry : ((originalEntries.drop 67).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate68
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row67_binding : (data.drop 67).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 67).take 1 :=
  row67_view.trans (row67_source.trans (row67_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 67 1)))

numeric_data_binding row68_view : (data.drop 68).take 1 = (data68.drop 0).take 1

numeric_data_binding row68_source : (data68.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate69
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row68_entry : ((originalEntries.drop 68).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate69
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row68_binding : (data.drop 68).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 68).take 1 :=
  row68_view.trans (row68_source.trans (row68_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 68 1)))

numeric_data_binding row69_view : (data.drop 69).take 1 = (data68.drop 1).take 1

numeric_data_binding row69_source : (data68.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate70
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row69_entry : ((originalEntries.drop 69).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate70
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row69_binding : (data.drop 69).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 69).take 1 :=
  row69_view.trans (row69_source.trans (row69_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 69 1)))

numeric_data_binding row70_view : (data.drop 70).take 1 = (data68.drop 2).take 1

numeric_data_binding row70_source : (data68.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate71
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row70_entry : ((originalEntries.drop 70).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate71
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row70_binding : (data.drop 70).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 70).take 1 :=
  row70_view.trans (row70_source.trans (row70_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 70 1)))

numeric_data_binding row71_view : (data.drop 71).take 1 = (data68.drop 3).take 1

numeric_data_binding row71_source : (data68.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate72
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row71_entry : ((originalEntries.drop 71).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate72
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row71_binding : (data.drop 71).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 71).take 1 :=
  row71_view.trans (row71_source.trans (row71_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 71 1)))

numeric_data_binding row72_view : (data.drop 72).take 1 = (data72.drop 0).take 1

numeric_data_binding row72_source : (data72.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate73
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row72_entry : ((originalEntries.drop 72).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate73
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row72_binding : (data.drop 72).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 72).take 1 :=
  row72_view.trans (row72_source.trans (row72_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 72 1)))

numeric_data_binding row73_view : (data.drop 73).take 1 = (data72.drop 1).take 1

numeric_data_binding row73_source : (data72.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate74
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row73_entry : ((originalEntries.drop 73).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate74
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row73_binding : (data.drop 73).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 73).take 1 :=
  row73_view.trans (row73_source.trans (row73_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 73 1)))

numeric_data_binding row74_view : (data.drop 74).take 1 = (data72.drop 2).take 1

numeric_data_binding row74_source : (data72.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate75
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row74_entry : ((originalEntries.drop 74).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate75
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row74_binding : (data.drop 74).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 74).take 1 :=
  row74_view.trans (row74_source.trans (row74_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 74 1)))

numeric_data_binding row75_view : (data.drop 75).take 1 = (data72.drop 3).take 1

numeric_data_binding row75_source : (data72.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate76
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row75_entry : ((originalEntries.drop 75).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate76
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row75_binding : (data.drop 75).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 75).take 1 :=
  row75_view.trans (row75_source.trans (row75_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 75 1)))

numeric_data_binding row76_view : (data.drop 76).take 1 = (data76.drop 0).take 1

numeric_data_binding row76_source : (data76.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate77
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row76_entry : ((originalEntries.drop 76).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate77
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row76_binding : (data.drop 76).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 76).take 1 :=
  row76_view.trans (row76_source.trans (row76_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 76 1)))

numeric_data_binding row77_view : (data.drop 77).take 1 = (data76.drop 1).take 1

numeric_data_binding row77_source : (data76.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate78
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row77_entry : ((originalEntries.drop 77).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate78
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row77_binding : (data.drop 77).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 77).take 1 :=
  row77_view.trans (row77_source.trans (row77_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 77 1)))

numeric_data_binding row78_view : (data.drop 78).take 1 = (data76.drop 2).take 1

numeric_data_binding row78_source : (data76.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate79
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row78_entry : ((originalEntries.drop 78).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate79
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row78_binding : (data.drop 78).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 78).take 1 :=
  row78_view.trans (row78_source.trans (row78_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 78 1)))

numeric_data_binding row79_view : (data.drop 79).take 1 = (data76.drop 3).take 1

numeric_data_binding row79_source : (data76.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate80
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row79_entry : ((originalEntries.drop 79).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate80
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row79_binding : (data.drop 79).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 79).take 1 :=
  row79_view.trans (row79_source.trans (row79_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 79 1)))

numeric_data_binding row80_view : (data.drop 80).take 1 = (data80.drop 0).take 1

numeric_data_binding row80_source : (data80.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate81
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row80_entry : ((originalEntries.drop 80).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate81
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row80_binding : (data.drop 80).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 1 :=
  row80_view.trans (row80_source.trans (row80_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 80 1)))

numeric_data_binding row81_view : (data.drop 81).take 1 = (data80.drop 1).take 1

numeric_data_binding row81_source : (data80.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate82
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row81_entry : ((originalEntries.drop 81).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate82
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row81_binding : (data.drop 81).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 81).take 1 :=
  row81_view.trans (row81_source.trans (row81_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 81 1)))

numeric_data_binding row82_view : (data.drop 82).take 1 = (data80.drop 2).take 1

numeric_data_binding row82_source : (data80.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate83
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row82_entry : ((originalEntries.drop 82).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate83
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row82_binding : (data.drop 82).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 82).take 1 :=
  row82_view.trans (row82_source.trans (row82_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 82 1)))

numeric_data_binding row83_view : (data.drop 83).take 1 = (data80.drop 3).take 1

numeric_data_binding row83_source : (data80.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate84
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row83_entry : ((originalEntries.drop 83).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate84
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row83_binding : (data.drop 83).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 83).take 1 :=
  row83_view.trans (row83_source.trans (row83_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 83 1)))

numeric_data_binding row84_view : (data.drop 84).take 1 = (data84.drop 0).take 1

numeric_data_binding row84_source : (data84.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate85
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row84_entry : ((originalEntries.drop 84).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate85
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row84_binding : (data.drop 84).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 84).take 1 :=
  row84_view.trans (row84_source.trans (row84_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 84 1)))

numeric_data_binding row85_view : (data.drop 85).take 1 = (data84.drop 1).take 1

numeric_data_binding row85_source : (data84.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate86
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row85_entry : ((originalEntries.drop 85).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate86
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row85_binding : (data.drop 85).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 85).take 1 :=
  row85_view.trans (row85_source.trans (row85_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 85 1)))

numeric_data_binding row86_view : (data.drop 86).take 1 = (data84.drop 2).take 1

numeric_data_binding row86_source : (data84.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate87
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row86_entry : ((originalEntries.drop 86).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate87
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row86_binding : (data.drop 86).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 86).take 1 :=
  row86_view.trans (row86_source.trans (row86_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 86 1)))

numeric_data_binding row87_view : (data.drop 87).take 1 = (data84.drop 3).take 1

numeric_data_binding row87_source : (data84.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate88
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row87_entry : ((originalEntries.drop 87).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate88
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row87_binding : (data.drop 87).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 87).take 1 :=
  row87_view.trans (row87_source.trans (row87_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 87 1)))

numeric_data_binding row88_view : (data.drop 88).take 1 = (data88.drop 0).take 1

numeric_data_binding row88_source : (data88.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate89
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

numeric_data_binding row88_entry : ((originalEntries.drop 88).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundUncached.native.candidate89
  Airbender.Compiler.HelperNative.BlakeRoundUncached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundUncached.native.typing)]

theorem row88_binding : (data.drop 88).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 88).take 1 :=
  row88_view.trans (row88_source.trans (row88_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 88 1)))

theorem entriesNode0_2 : (data.drop 0).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 1 1 1 2 rfl rfl row0_binding row1_binding

theorem entriesNode3_2 : (data.drop 3).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 3).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 3 1 1 4 2 rfl rfl row3_binding row4_binding

theorem entriesNode2_3 : (data.drop 2).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 2).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 2 1 2 3 3 rfl rfl row2_binding entriesNode3_2

theorem entriesNode0_5 : (data.drop 0).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 5 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 2 3 2 5 rfl rfl entriesNode0_2 entriesNode2_3

theorem entriesNode6_2 : (data.drop 6).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 6).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 6 1 1 7 2 rfl rfl row6_binding row7_binding

theorem entriesNode5_3 : (data.drop 5).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 5).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 5 1 2 6 3 rfl rfl row5_binding entriesNode6_2

theorem entriesNode9_2 : (data.drop 9).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 9).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 9 1 1 10 2 rfl rfl row9_binding row10_binding

theorem entriesNode8_3 : (data.drop 8).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 8 1 2 9 3 rfl rfl row8_binding entriesNode9_2

theorem entriesNode5_6 : (data.drop 5).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 5).take 6 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 5 3 3 8 6 rfl rfl entriesNode5_3 entriesNode8_3

theorem entriesNode0_11 : (data.drop 0).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 11 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 5 6 5 11 rfl rfl entriesNode0_5 entriesNode5_6

theorem entriesNode11_2 : (data.drop 11).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 11).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 11 1 1 12 2 rfl rfl row11_binding row12_binding

theorem entriesNode14_2 : (data.drop 14).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 14).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 14 1 1 15 2 rfl rfl row14_binding row15_binding

theorem entriesNode13_3 : (data.drop 13).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 13).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 13 1 2 14 3 rfl rfl row13_binding entriesNode14_2

theorem entriesNode11_5 : (data.drop 11).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 11).take 5 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 11 2 3 13 5 rfl rfl entriesNode11_2 entriesNode13_3

theorem entriesNode17_2 : (data.drop 17).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 17).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 17 1 1 18 2 rfl rfl row17_binding row18_binding

theorem entriesNode16_3 : (data.drop 16).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 16 1 2 17 3 rfl rfl row16_binding entriesNode17_2

theorem entriesNode20_2 : (data.drop 20).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 20).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 20 1 1 21 2 rfl rfl row20_binding row21_binding

theorem entriesNode19_3 : (data.drop 19).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 19).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 19 1 2 20 3 rfl rfl row19_binding entriesNode20_2

theorem entriesNode16_6 : (data.drop 16).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 6 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 16 3 3 19 6 rfl rfl entriesNode16_3 entriesNode19_3

theorem entriesNode11_11 : (data.drop 11).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 11).take 11 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 11 5 6 16 11 rfl rfl entriesNode11_5 entriesNode16_6

theorem entriesNode0_22 : (data.drop 0).take 22 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 22 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 11 11 11 22 rfl rfl entriesNode0_11 entriesNode11_11

theorem entriesNode22_2 : (data.drop 22).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 22 1 1 23 2 rfl rfl row22_binding row23_binding

theorem entriesNode25_2 : (data.drop 25).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 25).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 25 1 1 26 2 rfl rfl row25_binding row26_binding

theorem entriesNode24_3 : (data.drop 24).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 24 1 2 25 3 rfl rfl row24_binding entriesNode25_2

theorem entriesNode22_5 : (data.drop 22).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 5 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 22 2 3 24 5 rfl rfl entriesNode22_2 entriesNode24_3

theorem entriesNode28_2 : (data.drop 28).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 28).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 28 1 1 29 2 rfl rfl row28_binding row29_binding

theorem entriesNode27_3 : (data.drop 27).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 27).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 27 1 2 28 3 rfl rfl row27_binding entriesNode28_2

theorem entriesNode31_2 : (data.drop 31).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 31).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 31 1 1 32 2 rfl rfl row31_binding row32_binding

theorem entriesNode30_3 : (data.drop 30).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 30).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 30 1 2 31 3 rfl rfl row30_binding entriesNode31_2

theorem entriesNode27_6 : (data.drop 27).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 27).take 6 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 27 3 3 30 6 rfl rfl entriesNode27_3 entriesNode30_3

theorem entriesNode22_11 : (data.drop 22).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 11 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 22 5 6 27 11 rfl rfl entriesNode22_5 entriesNode27_6

theorem entriesNode33_2 : (data.drop 33).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 33).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 33 1 1 34 2 rfl rfl row33_binding row34_binding

theorem entriesNode36_2 : (data.drop 36).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 36).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 36 1 1 37 2 rfl rfl row36_binding row37_binding

theorem entriesNode35_3 : (data.drop 35).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 35).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 35 1 2 36 3 rfl rfl row35_binding entriesNode36_2

theorem entriesNode33_5 : (data.drop 33).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 33).take 5 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 33 2 3 35 5 rfl rfl entriesNode33_2 entriesNode35_3

theorem entriesNode39_2 : (data.drop 39).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 39).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 39 1 1 40 2 rfl rfl row39_binding row40_binding

theorem entriesNode38_3 : (data.drop 38).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 38).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 38 1 2 39 3 rfl rfl row38_binding entriesNode39_2

theorem entriesNode42_2 : (data.drop 42).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 42).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 42 1 1 43 2 rfl rfl row42_binding row43_binding

theorem entriesNode41_3 : (data.drop 41).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 41).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 41 1 2 42 3 rfl rfl row41_binding entriesNode42_2

theorem entriesNode38_6 : (data.drop 38).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 38).take 6 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 38 3 3 41 6 rfl rfl entriesNode38_3 entriesNode41_3

theorem entriesNode33_11 : (data.drop 33).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 33).take 11 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 33 5 6 38 11 rfl rfl entriesNode33_5 entriesNode38_6

theorem entriesNode22_22 : (data.drop 22).take 22 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 22 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 22 11 11 33 22 rfl rfl entriesNode22_11 entriesNode33_11

theorem entriesNode0_44 : (data.drop 0).take 44 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 44 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 22 22 22 44 rfl rfl entriesNode0_22 entriesNode22_22

theorem entriesNode44_2 : (data.drop 44).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 44 1 1 45 2 rfl rfl row44_binding row45_binding

theorem entriesNode47_2 : (data.drop 47).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 47).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 47 1 1 48 2 rfl rfl row47_binding row48_binding

theorem entriesNode46_3 : (data.drop 46).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 46).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 46 1 2 47 3 rfl rfl row46_binding entriesNode47_2

theorem entriesNode44_5 : (data.drop 44).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 5 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 44 2 3 46 5 rfl rfl entriesNode44_2 entriesNode46_3

theorem entriesNode50_2 : (data.drop 50).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 50).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 50 1 1 51 2 rfl rfl row50_binding row51_binding

theorem entriesNode49_3 : (data.drop 49).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 49).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 49 1 2 50 3 rfl rfl row49_binding entriesNode50_2

theorem entriesNode53_2 : (data.drop 53).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 53).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 53 1 1 54 2 rfl rfl row53_binding row54_binding

theorem entriesNode52_3 : (data.drop 52).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 52).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 52 1 2 53 3 rfl rfl row52_binding entriesNode53_2

theorem entriesNode49_6 : (data.drop 49).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 49).take 6 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 49 3 3 52 6 rfl rfl entriesNode49_3 entriesNode52_3

theorem entriesNode44_11 : (data.drop 44).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 11 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 44 5 6 49 11 rfl rfl entriesNode44_5 entriesNode49_6

theorem entriesNode55_2 : (data.drop 55).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 55).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 55 1 1 56 2 rfl rfl row55_binding row56_binding

theorem entriesNode58_2 : (data.drop 58).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 58).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 58 1 1 59 2 rfl rfl row58_binding row59_binding

theorem entriesNode57_3 : (data.drop 57).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 57).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 57 1 2 58 3 rfl rfl row57_binding entriesNode58_2

theorem entriesNode55_5 : (data.drop 55).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 55).take 5 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 55 2 3 57 5 rfl rfl entriesNode55_2 entriesNode57_3

theorem entriesNode61_2 : (data.drop 61).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 61).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 61 1 1 62 2 rfl rfl row61_binding row62_binding

theorem entriesNode60_3 : (data.drop 60).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 60).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 60 1 2 61 3 rfl rfl row60_binding entriesNode61_2

theorem entriesNode64_2 : (data.drop 64).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 64 1 1 65 2 rfl rfl row64_binding row65_binding

theorem entriesNode63_3 : (data.drop 63).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 63).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 63 1 2 64 3 rfl rfl row63_binding entriesNode64_2

theorem entriesNode60_6 : (data.drop 60).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 60).take 6 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 60 3 3 63 6 rfl rfl entriesNode60_3 entriesNode63_3

theorem entriesNode55_11 : (data.drop 55).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 55).take 11 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 55 5 6 60 11 rfl rfl entriesNode55_5 entriesNode60_6

theorem entriesNode44_22 : (data.drop 44).take 22 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 22 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 44 11 11 55 22 rfl rfl entriesNode44_11 entriesNode55_11

theorem entriesNode66_2 : (data.drop 66).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 66).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 66 1 1 67 2 rfl rfl row66_binding row67_binding

theorem entriesNode69_2 : (data.drop 69).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 69).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 69 1 1 70 2 rfl rfl row69_binding row70_binding

theorem entriesNode68_3 : (data.drop 68).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 68).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 68 1 2 69 3 rfl rfl row68_binding entriesNode69_2

theorem entriesNode66_5 : (data.drop 66).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 66).take 5 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 66 2 3 68 5 rfl rfl entriesNode66_2 entriesNode68_3

theorem entriesNode72_2 : (data.drop 72).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 72).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 72 1 1 73 2 rfl rfl row72_binding row73_binding

theorem entriesNode71_3 : (data.drop 71).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 71).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 71 1 2 72 3 rfl rfl row71_binding entriesNode72_2

theorem entriesNode75_2 : (data.drop 75).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 75).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 75 1 1 76 2 rfl rfl row75_binding row76_binding

theorem entriesNode74_3 : (data.drop 74).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 74).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 74 1 2 75 3 rfl rfl row74_binding entriesNode75_2

theorem entriesNode71_6 : (data.drop 71).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 71).take 6 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 71 3 3 74 6 rfl rfl entriesNode71_3 entriesNode74_3

theorem entriesNode66_11 : (data.drop 66).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 66).take 11 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 66 5 6 71 11 rfl rfl entriesNode66_5 entriesNode71_6

theorem entriesNode78_2 : (data.drop 78).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 78).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 78 1 1 79 2 rfl rfl row78_binding row79_binding

theorem entriesNode77_3 : (data.drop 77).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 77).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 77 1 2 78 3 rfl rfl row77_binding entriesNode78_2

theorem entriesNode81_2 : (data.drop 81).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 81).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 81 1 1 82 2 rfl rfl row81_binding row82_binding

theorem entriesNode80_3 : (data.drop 80).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 80 1 2 81 3 rfl rfl row80_binding entriesNode81_2

theorem entriesNode77_6 : (data.drop 77).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 77).take 6 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 77 3 3 80 6 rfl rfl entriesNode77_3 entriesNode80_3

theorem entriesNode84_2 : (data.drop 84).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 84).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 84 1 1 85 2 rfl rfl row84_binding row85_binding

theorem entriesNode83_3 : (data.drop 83).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 83).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 83 1 2 84 3 rfl rfl row83_binding entriesNode84_2

theorem entriesNode87_2 : (data.drop 87).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 87).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 87 1 1 88 2 rfl rfl row87_binding row88_binding

theorem entriesNode86_3 : (data.drop 86).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 86).take 3 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 86 1 2 87 3 rfl rfl row86_binding entriesNode87_2

theorem entriesNode83_6 : (data.drop 83).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 83).take 6 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 83 3 3 86 6 rfl rfl entriesNode83_3 entriesNode86_3

theorem entriesNode77_12 : (data.drop 77).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 77).take 12 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 77 6 6 83 12 rfl rfl entriesNode77_6 entriesNode83_6

theorem entriesNode66_23 : (data.drop 66).take 23 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 66).take 23 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 66 11 12 77 23 rfl rfl entriesNode66_11 entriesNode77_12

theorem entriesNode44_45 : (data.drop 44).take 45 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 45 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 44 22 23 66 45 rfl rfl entriesNode44_22 entriesNode66_23

theorem entriesNode0_89 : (data.drop 0).take 89 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 89 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 44 45 44 89 rfl rfl entriesNode0_44 entriesNode44_45

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 89
    (by decide +kernel) (by decide +kernel) entriesNode0_89

end Airbender.Compiler.HelperPayloadChecks.BlakeRoundUncached
