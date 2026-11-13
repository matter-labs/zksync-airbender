module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.LookupSourceChecks.WordMemoryCached.Data
public import Proven.GKRProtocol.NumericQueryFrameBindings
public import Proven.Import.GKRProtocol.NumericArithmeticDataImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.LookupSourceChecks.WordMemoryCached
open Airbender.Compiler
set_option maxRecDepth 8192

numeric_data_binding view0 : (data.drop 0).take 1 = (data0.drop 0).take 1

numeric_data_binding piece0 : (data0.drop 0).take 1 = ((originalEntries.drop 0).take 1).map NumericFunctionalBaseChecks.encode

theorem binding0 : (data.drop 0).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 1 :=
  view0.trans (piece0.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 0 1))

numeric_data_binding view1 : (data.drop 1).take 1 = (data0.drop 1).take 1

numeric_data_binding piece1 : (data0.drop 1).take 1 = ((originalEntries.drop 1).take 1).map NumericFunctionalBaseChecks.encode

theorem binding1 : (data.drop 1).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 1).take 1 :=
  view1.trans (piece1.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 1 1))

numeric_data_binding view2 : (data.drop 2).take 1 = (data0.drop 2).take 1

numeric_data_binding piece2 : (data0.drop 2).take 1 = ((originalEntries.drop 2).take 1).map NumericFunctionalBaseChecks.encode

theorem binding2 : (data.drop 2).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 2).take 1 :=
  view2.trans (piece2.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 2 1))

numeric_data_binding view3 : (data.drop 3).take 1 = (data0.drop 3).take 1

numeric_data_binding piece3 : (data0.drop 3).take 1 = ((originalEntries.drop 3).take 1).map NumericFunctionalBaseChecks.encode

theorem binding3 : (data.drop 3).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 3).take 1 :=
  view3.trans (piece3.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 3 1))

numeric_data_binding view4 : (data.drop 4).take 1 = (data0.drop 4).take 1

numeric_data_binding piece4 : (data0.drop 4).take 1 = ((originalEntries.drop 4).take 1).map NumericFunctionalBaseChecks.encode

theorem binding4 : (data.drop 4).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 4).take 1 :=
  view4.trans (piece4.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 4 1))

numeric_data_binding view5 : (data.drop 5).take 1 = (data0.drop 5).take 1

numeric_data_binding piece5 : (data0.drop 5).take 1 = ((originalEntries.drop 5).take 1).map NumericFunctionalBaseChecks.encode

theorem binding5 : (data.drop 5).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 5).take 1 :=
  view5.trans (piece5.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 5 1))

numeric_data_binding view6 : (data.drop 6).take 1 = (data0.drop 6).take 1

numeric_data_binding piece6 : (data0.drop 6).take 1 = ((originalEntries.drop 6).take 1).map NumericFunctionalBaseChecks.encode

theorem binding6 : (data.drop 6).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 6).take 1 :=
  view6.trans (piece6.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 6 1))

numeric_data_binding view7 : (data.drop 7).take 1 = (data0.drop 7).take 1

numeric_data_binding piece7 : (data0.drop 7).take 1 = ((originalEntries.drop 7).take 1).map NumericFunctionalBaseChecks.encode

theorem binding7 : (data.drop 7).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 7).take 1 :=
  view7.trans (piece7.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 7 1))

numeric_data_binding view8 : (data.drop 8).take 1 = (data8.drop 0).take 1

numeric_data_binding piece8 : (data8.drop 0).take 1 = ((originalEntries.drop 8).take 1).map NumericFunctionalBaseChecks.encode

theorem binding8 : (data.drop 8).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 1 :=
  view8.trans (piece8.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 8 1))

numeric_data_binding view9 : (data.drop 9).take 1 = (data8.drop 1).take 1

numeric_data_binding piece9 : (data8.drop 1).take 1 = ((originalEntries.drop 9).take 1).map NumericFunctionalBaseChecks.encode

theorem binding9 : (data.drop 9).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 9).take 1 :=
  view9.trans (piece9.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 9 1))

numeric_data_binding view10 : (data.drop 10).take 1 = (data8.drop 2).take 1

numeric_data_binding piece10 : (data8.drop 2).take 1 = ((originalEntries.drop 10).take 1).map NumericFunctionalBaseChecks.encode

theorem binding10 : (data.drop 10).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 10).take 1 :=
  view10.trans (piece10.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 10 1))

numeric_data_binding view11 : (data.drop 11).take 1 = (data8.drop 3).take 1

numeric_data_binding piece11 : (data8.drop 3).take 1 = ((originalEntries.drop 11).take 1).map NumericFunctionalBaseChecks.encode

theorem binding11 : (data.drop 11).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 11).take 1 :=
  view11.trans (piece11.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 11 1))

numeric_data_binding view12 : (data.drop 12).take 1 = (data8.drop 4).take 1

numeric_data_binding piece12 : (data8.drop 4).take 1 = ((originalEntries.drop 12).take 1).map NumericFunctionalBaseChecks.encode

theorem binding12 : (data.drop 12).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 12).take 1 :=
  view12.trans (piece12.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 12 1))

numeric_data_binding view13 : (data.drop 13).take 1 = (data8.drop 5).take 1

numeric_data_binding piece13 : (data8.drop 5).take 1 = ((originalEntries.drop 13).take 1).map NumericFunctionalBaseChecks.encode

theorem binding13 : (data.drop 13).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 13).take 1 :=
  view13.trans (piece13.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 13 1))

numeric_data_binding view14 : (data.drop 14).take 1 = (data8.drop 6).take 1

numeric_data_binding piece14 : (data8.drop 6).take 1 = ((originalEntries.drop 14).take 1).map NumericFunctionalBaseChecks.encode

theorem binding14 : (data.drop 14).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 14).take 1 :=
  view14.trans (piece14.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 14 1))

numeric_data_binding view15 : (data.drop 15).take 1 = (data8.drop 7).take 1

numeric_data_binding piece15 : (data8.drop 7).take 1 = ((originalEntries.drop 15).take 1).map NumericFunctionalBaseChecks.encode

theorem binding15 : (data.drop 15).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 15).take 1 :=
  view15.trans (piece15.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 15 1))

numeric_data_binding view16 : (data.drop 16).take 1 = (data16.drop 0).take 1

numeric_data_binding piece16 : (data16.drop 0).take 1 = ((originalEntries.drop 16).take 1).map NumericFunctionalBaseChecks.encode

theorem binding16 : (data.drop 16).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 1 :=
  view16.trans (piece16.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 16 1))

numeric_data_binding view17 : (data.drop 17).take 1 = (data16.drop 1).take 1

numeric_data_binding piece17 : (data16.drop 1).take 1 = ((originalEntries.drop 17).take 1).map NumericFunctionalBaseChecks.encode

theorem binding17 : (data.drop 17).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 17).take 1 :=
  view17.trans (piece17.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 17 1))

numeric_data_binding view18 : (data.drop 18).take 1 = (data16.drop 2).take 1

numeric_data_binding piece18 : (data16.drop 2).take 1 = ((originalEntries.drop 18).take 1).map NumericFunctionalBaseChecks.encode

theorem binding18 : (data.drop 18).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 18).take 1 :=
  view18.trans (piece18.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 18 1))

numeric_data_binding view19 : (data.drop 19).take 1 = (data16.drop 3).take 1

numeric_data_binding piece19 : (data16.drop 3).take 1 = ((originalEntries.drop 19).take 1).map NumericFunctionalBaseChecks.encode

theorem binding19 : (data.drop 19).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 19).take 1 :=
  view19.trans (piece19.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 19 1))

numeric_data_binding view20 : (data.drop 20).take 1 = (data16.drop 4).take 1

numeric_data_binding piece20 : (data16.drop 4).take 1 = ((originalEntries.drop 20).take 1).map NumericFunctionalBaseChecks.encode

theorem binding20 : (data.drop 20).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 20).take 1 :=
  view20.trans (piece20.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 20 1))

numeric_data_binding view21 : (data.drop 21).take 1 = (data16.drop 5).take 1

numeric_data_binding piece21 : (data16.drop 5).take 1 = ((originalEntries.drop 21).take 1).map NumericFunctionalBaseChecks.encode

theorem binding21 : (data.drop 21).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 21).take 1 :=
  view21.trans (piece21.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 21 1))

numeric_data_binding view22 : (data.drop 22).take 1 = (data16.drop 6).take 1

numeric_data_binding piece22 : (data16.drop 6).take 1 = ((originalEntries.drop 22).take 1).map NumericFunctionalBaseChecks.encode

theorem binding22 : (data.drop 22).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 1 :=
  view22.trans (piece22.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 22 1))

numeric_data_binding view23 : (data.drop 23).take 1 = (data16.drop 7).take 1

numeric_data_binding piece23 : (data16.drop 7).take 1 = ((originalEntries.drop 23).take 1).map NumericFunctionalBaseChecks.encode

theorem binding23 : (data.drop 23).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 23).take 1 :=
  view23.trans (piece23.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 23 1))

numeric_data_binding view24 : (data.drop 24).take 1 = (data24.drop 0).take 1

numeric_data_binding piece24 : (data24.drop 0).take 1 = ((originalEntries.drop 24).take 1).map NumericFunctionalBaseChecks.encode

theorem binding24 : (data.drop 24).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 1 :=
  view24.trans (piece24.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 24 1))

numeric_data_binding view25 : (data.drop 25).take 1 = (data24.drop 1).take 1

numeric_data_binding piece25 : (data24.drop 1).take 1 = ((originalEntries.drop 25).take 1).map NumericFunctionalBaseChecks.encode

theorem binding25 : (data.drop 25).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 25).take 1 :=
  view25.trans (piece25.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 25 1))

numeric_data_binding view26 : (data.drop 26).take 1 = (data24.drop 2).take 1

numeric_data_binding piece26 : (data24.drop 2).take 1 = ((originalEntries.drop 26).take 1).map NumericFunctionalBaseChecks.encode

theorem binding26 : (data.drop 26).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 26).take 1 :=
  view26.trans (piece26.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 26 1))

numeric_data_binding view27 : (data.drop 27).take 1 = (data24.drop 3).take 1

numeric_data_binding piece27 : (data24.drop 3).take 1 = ((originalEntries.drop 27).take 1).map NumericFunctionalBaseChecks.encode

theorem binding27 : (data.drop 27).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 27).take 1 :=
  view27.trans (piece27.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 27 1))

numeric_data_binding view28 : (data.drop 28).take 1 = (data24.drop 4).take 1

numeric_data_binding piece28 : (data24.drop 4).take 1 = ((originalEntries.drop 28).take 1).map NumericFunctionalBaseChecks.encode

theorem binding28 : (data.drop 28).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 28).take 1 :=
  view28.trans (piece28.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 28 1))

numeric_data_binding view29 : (data.drop 29).take 1 = (data24.drop 5).take 1

numeric_data_binding piece29 : (data24.drop 5).take 1 = ((originalEntries.drop 29).take 1).map NumericFunctionalBaseChecks.encode

theorem binding29 : (data.drop 29).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 29).take 1 :=
  view29.trans (piece29.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 29 1))

numeric_data_binding view30 : (data.drop 30).take 1 = (data24.drop 6).take 1

numeric_data_binding piece30 : (data24.drop 6).take 1 = ((originalEntries.drop 30).take 1).map NumericFunctionalBaseChecks.encode

theorem binding30 : (data.drop 30).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 30).take 1 :=
  view30.trans (piece30.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 30 1))

numeric_data_binding view31 : (data.drop 31).take 1 = (data24.drop 7).take 1

numeric_data_binding piece31 : (data24.drop 7).take 1 = ((originalEntries.drop 31).take 1).map NumericFunctionalBaseChecks.encode

theorem binding31 : (data.drop 31).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 31).take 1 :=
  view31.trans (piece31.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 31 1))

numeric_data_binding view32 : (data.drop 32).take 1 = (data32.drop 0).take 1

numeric_data_binding piece32 : (data32.drop 0).take 1 = ((originalEntries.drop 32).take 1).map NumericFunctionalBaseChecks.encode

theorem binding32 : (data.drop 32).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 1 :=
  view32.trans (piece32.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 32 1))

numeric_data_binding view33 : (data.drop 33).take 1 = (data32.drop 1).take 1

numeric_data_binding piece33 : (data32.drop 1).take 1 = ((originalEntries.drop 33).take 1).map NumericFunctionalBaseChecks.encode

theorem binding33 : (data.drop 33).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 33).take 1 :=
  view33.trans (piece33.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 33 1))

numeric_data_binding view34 : (data.drop 34).take 1 = (data32.drop 2).take 1

numeric_data_binding piece34 : (data32.drop 2).take 1 = ((originalEntries.drop 34).take 1).map NumericFunctionalBaseChecks.encode

theorem binding34 : (data.drop 34).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 34).take 1 :=
  view34.trans (piece34.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 34 1))

numeric_data_binding view35 : (data.drop 35).take 1 = (data32.drop 3).take 1

numeric_data_binding piece35 : (data32.drop 3).take 1 = ((originalEntries.drop 35).take 1).map NumericFunctionalBaseChecks.encode

theorem binding35 : (data.drop 35).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 35).take 1 :=
  view35.trans (piece35.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 35 1))

numeric_data_binding view36 : (data.drop 36).take 1 = (data32.drop 4).take 1

numeric_data_binding piece36 : (data32.drop 4).take 1 = ((originalEntries.drop 36).take 1).map NumericFunctionalBaseChecks.encode

theorem binding36 : (data.drop 36).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 36).take 1 :=
  view36.trans (piece36.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 36 1))

numeric_data_binding view37 : (data.drop 37).take 1 = (data32.drop 5).take 1

numeric_data_binding piece37 : (data32.drop 5).take 1 = ((originalEntries.drop 37).take 1).map NumericFunctionalBaseChecks.encode

theorem binding37 : (data.drop 37).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 37).take 1 :=
  view37.trans (piece37.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 37 1))

numeric_data_binding view38 : (data.drop 38).take 1 = (data32.drop 6).take 1

numeric_data_binding piece38 : (data32.drop 6).take 1 = ((originalEntries.drop 38).take 1).map NumericFunctionalBaseChecks.encode

theorem binding38 : (data.drop 38).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 38).take 1 :=
  view38.trans (piece38.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 38 1))

numeric_data_binding view39 : (data.drop 39).take 1 = (data32.drop 7).take 1

numeric_data_binding piece39 : (data32.drop 7).take 1 = ((originalEntries.drop 39).take 1).map NumericFunctionalBaseChecks.encode

theorem binding39 : (data.drop 39).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 39).take 1 :=
  view39.trans (piece39.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 39 1))

numeric_data_binding view40 : (data.drop 40).take 1 = (data40.drop 0).take 1

numeric_data_binding piece40 : (data40.drop 0).take 1 = ((originalEntries.drop 40).take 1).map NumericFunctionalBaseChecks.encode

theorem binding40 : (data.drop 40).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 40).take 1 :=
  view40.trans (piece40.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 40 1))

numeric_data_binding view41 : (data.drop 41).take 1 = (data40.drop 1).take 1

numeric_data_binding piece41 : (data40.drop 1).take 1 = ((originalEntries.drop 41).take 1).map NumericFunctionalBaseChecks.encode

theorem binding41 : (data.drop 41).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 41).take 1 :=
  view41.trans (piece41.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 41 1))

numeric_data_binding view42 : (data.drop 42).take 1 = (data40.drop 2).take 1

numeric_data_binding piece42 : (data40.drop 2).take 1 = ((originalEntries.drop 42).take 1).map NumericFunctionalBaseChecks.encode

theorem binding42 : (data.drop 42).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 42).take 1 :=
  view42.trans (piece42.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 42 1))

theorem sourceNode0_2 : (data.drop 0).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 1 1 binding0 binding1

theorem sourceNode3_2 : (data.drop 3).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 3).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 3 1 1 binding3 binding4

theorem sourceNode2_3 : (data.drop 2).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 2).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 2 1 2 binding2 sourceNode3_2

theorem sourceNode0_5 : (data.drop 0).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 2 3 sourceNode0_2 sourceNode2_3

theorem sourceNode5_2 : (data.drop 5).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 5).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 5 1 1 binding5 binding6

theorem sourceNode8_2 : (data.drop 8).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 8 1 1 binding8 binding9

theorem sourceNode7_3 : (data.drop 7).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 7).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 7 1 2 binding7 sourceNode8_2

theorem sourceNode5_5 : (data.drop 5).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 5).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 5 2 3 sourceNode5_2 sourceNode7_3

theorem sourceNode0_10 : (data.drop 0).take 10 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 10 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 5 5 sourceNode0_5 sourceNode5_5

theorem sourceNode10_2 : (data.drop 10).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 10).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 10 1 1 binding10 binding11

theorem sourceNode13_2 : (data.drop 13).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 13).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 13 1 1 binding13 binding14

theorem sourceNode12_3 : (data.drop 12).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 12).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 12 1 2 binding12 sourceNode13_2

theorem sourceNode10_5 : (data.drop 10).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 10).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 10 2 3 sourceNode10_2 sourceNode12_3

theorem sourceNode16_2 : (data.drop 16).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 16 1 1 binding16 binding17

theorem sourceNode15_3 : (data.drop 15).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 15).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 15 1 2 binding15 sourceNode16_2

theorem sourceNode19_2 : (data.drop 19).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 19).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 19 1 1 binding19 binding20

theorem sourceNode18_3 : (data.drop 18).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 18).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 18 1 2 binding18 sourceNode19_2

theorem sourceNode15_6 : (data.drop 15).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 15).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 15 3 3 sourceNode15_3 sourceNode18_3

theorem sourceNode10_11 : (data.drop 10).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 10).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 10 5 6 sourceNode10_5 sourceNode15_6

theorem sourceNode0_21 : (data.drop 0).take 21 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 21 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 10 11 sourceNode0_10 sourceNode10_11

theorem sourceNode21_2 : (data.drop 21).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 21).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 21 1 1 binding21 binding22

theorem sourceNode24_2 : (data.drop 24).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 24 1 1 binding24 binding25

theorem sourceNode23_3 : (data.drop 23).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 23).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 23 1 2 binding23 sourceNode24_2

theorem sourceNode21_5 : (data.drop 21).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 21).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 21 2 3 sourceNode21_2 sourceNode23_3

theorem sourceNode27_2 : (data.drop 27).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 27).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 27 1 1 binding27 binding28

theorem sourceNode26_3 : (data.drop 26).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 26).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 26 1 2 binding26 sourceNode27_2

theorem sourceNode30_2 : (data.drop 30).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 30).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 30 1 1 binding30 binding31

theorem sourceNode29_3 : (data.drop 29).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 29).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 29 1 2 binding29 sourceNode30_2

theorem sourceNode26_6 : (data.drop 26).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 26).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 26 3 3 sourceNode26_3 sourceNode29_3

theorem sourceNode21_11 : (data.drop 21).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 21).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 21 5 6 sourceNode21_5 sourceNode26_6

theorem sourceNode32_2 : (data.drop 32).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 1 1 binding32 binding33

theorem sourceNode35_2 : (data.drop 35).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 35).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 35 1 1 binding35 binding36

theorem sourceNode34_3 : (data.drop 34).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 34).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 34 1 2 binding34 sourceNode35_2

theorem sourceNode32_5 : (data.drop 32).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 2 3 sourceNode32_2 sourceNode34_3

theorem sourceNode38_2 : (data.drop 38).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 38).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 38 1 1 binding38 binding39

theorem sourceNode37_3 : (data.drop 37).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 37).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 37 1 2 binding37 sourceNode38_2

theorem sourceNode41_2 : (data.drop 41).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 41).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 41 1 1 binding41 binding42

theorem sourceNode40_3 : (data.drop 40).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 40).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 40 1 2 binding40 sourceNode41_2

theorem sourceNode37_6 : (data.drop 37).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 37).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 37 3 3 sourceNode37_3 sourceNode40_3

theorem sourceNode32_11 : (data.drop 32).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 5 6 sourceNode32_5 sourceNode37_6

theorem sourceNode21_22 : (data.drop 21).take 22 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 21).take 22 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 21 11 11 sourceNode21_11 sourceNode32_11

theorem sourceNode0_43 : (data.drop 0).take 43 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 43 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 21 22 sourceNode0_21 sourceNode21_22

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 43
    (by decide +kernel) (by decide +kernel) sourceNode0_43

end Airbender.Compiler.LookupSourceChecks.WordMemoryCached
