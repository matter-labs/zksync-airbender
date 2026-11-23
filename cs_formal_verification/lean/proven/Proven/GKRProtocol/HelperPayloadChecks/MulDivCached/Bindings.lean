module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.HelperPayloadChecks.MulDivCached.Data
public import Proven.Import.GKRProtocol.NumericArithmeticDataImport
public import Proven.GKRProtocol.NumericWorkerPortChecks

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.HelperPayloadChecks.MulDivCached
open Airbender Airbender.Compiler
set_option maxRecDepth 8192

attribute [local irreducible] originalEntries data

numeric_data_binding row0_view : (data.drop 0).take 1 = (data0.drop 0).take 1

numeric_data_binding row0_source : (data0.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate8
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

numeric_data_binding row0_entry : ((originalEntries.drop 0).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate8
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

theorem row0_binding : (data.drop 0).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 1 :=
  row0_view.trans (row0_source.trans (row0_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 0 1)))

numeric_data_binding row1_view : (data.drop 1).take 1 = (data0.drop 1).take 1

numeric_data_binding row1_source : (data0.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate10
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

numeric_data_binding row1_entry : ((originalEntries.drop 1).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate10
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

theorem row1_binding : (data.drop 1).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 1).take 1 :=
  row1_view.trans (row1_source.trans (row1_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 1 1)))

numeric_data_binding row2_view : (data.drop 2).take 1 = (data0.drop 2).take 1

numeric_data_binding row2_source : (data0.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate11
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

numeric_data_binding row2_entry : ((originalEntries.drop 2).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate11
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

theorem row2_binding : (data.drop 2).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 2).take 1 :=
  row2_view.trans (row2_source.trans (row2_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 2 1)))

numeric_data_binding row3_view : (data.drop 3).take 1 = (data0.drop 3).take 1

numeric_data_binding row3_source : (data0.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate12
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

numeric_data_binding row3_entry : ((originalEntries.drop 3).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate12
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

theorem row3_binding : (data.drop 3).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 3).take 1 :=
  row3_view.trans (row3_source.trans (row3_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 3 1)))

numeric_data_binding row4_view : (data.drop 4).take 1 = (data4.drop 0).take 1

numeric_data_binding row4_source : (data4.drop 0).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate13
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

numeric_data_binding row4_entry : ((originalEntries.drop 4).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate13
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

theorem row4_binding : (data.drop 4).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 4).take 1 :=
  row4_view.trans (row4_source.trans (row4_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 4 1)))

numeric_data_binding row5_view : (data.drop 5).take 1 = (data4.drop 1).take 1

numeric_data_binding row5_source : (data4.drop 1).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate14
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

numeric_data_binding row5_entry : ((originalEntries.drop 5).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate14
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

theorem row5_binding : (data.drop 5).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 5).take 1 :=
  row5_view.trans (row5_source.trans (row5_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 5 1)))

numeric_data_binding row6_view : (data.drop 6).take 1 = (data4.drop 2).take 1

numeric_data_binding row6_source : (data4.drop 2).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate15
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

numeric_data_binding row6_entry : ((originalEntries.drop 6).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate15
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

theorem row6_binding : (data.drop 6).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 6).take 1 :=
  row6_view.trans (row6_source.trans (row6_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 6 1)))

numeric_data_binding row7_view : (data.drop 7).take 1 = (data4.drop 3).take 1

numeric_data_binding row7_source : (data4.drop 3).take 1 = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate25
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

numeric_data_binding row7_entry : ((originalEntries.drop 7).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate25
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

theorem row7_binding : (data.drop 7).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 7).take 1 :=
  row7_view.trans (row7_source.trans (row7_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 7 1)))

theorem entriesNode0_2 : (data.drop 0).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 1 1 1 2 rfl rfl row0_binding row1_binding

theorem entriesNode2_2 : (data.drop 2).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 2).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 2 1 1 3 2 rfl rfl row2_binding row3_binding

theorem entriesNode0_4 : (data.drop 0).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 4 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 2 2 2 4 rfl rfl entriesNode0_2 entriesNode2_2

theorem entriesNode4_2 : (data.drop 4).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 4).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 4 1 1 5 2 rfl rfl row4_binding row5_binding

theorem entriesNode6_2 : (data.drop 6).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 6).take 2 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 6 1 1 7 2 rfl rfl row6_binding row7_binding

theorem entriesNode4_4 : (data.drop 4).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 4).take 4 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 4 2 2 6 4 rfl rfl entriesNode4_2 entriesNode6_2

theorem entriesNode0_8 : (data.drop 0).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 8 :=
  NumericWorkerPortChecks.merge_at data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 4 4 4 8 rfl rfl entriesNode0_4 entriesNode4_4

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 8
    (by decide +kernel) (by decide +kernel) entriesNode0_8

end Airbender.Compiler.HelperPayloadChecks.MulDivCached
