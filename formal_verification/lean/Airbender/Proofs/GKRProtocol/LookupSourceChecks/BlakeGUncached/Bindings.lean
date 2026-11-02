import Airbender.Proofs.GKRProtocol.LookupSourceChecks.BlakeGUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.LookupSourceChecks.BlakeGUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
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

numeric_data_binding view43 : (data.drop 43).take 1 = (data40.drop 3).take 1

numeric_data_binding piece43 : (data40.drop 3).take 1 = ((originalEntries.drop 43).take 1).map NumericFunctionalBaseChecks.encode

theorem binding43 : (data.drop 43).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 43).take 1 :=
  view43.trans (piece43.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 43 1))

numeric_data_binding view44 : (data.drop 44).take 1 = (data40.drop 4).take 1

numeric_data_binding piece44 : (data40.drop 4).take 1 = ((originalEntries.drop 44).take 1).map NumericFunctionalBaseChecks.encode

theorem binding44 : (data.drop 44).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 1 :=
  view44.trans (piece44.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 44 1))

numeric_data_binding view45 : (data.drop 45).take 1 = (data40.drop 5).take 1

numeric_data_binding piece45 : (data40.drop 5).take 1 = ((originalEntries.drop 45).take 1).map NumericFunctionalBaseChecks.encode

theorem binding45 : (data.drop 45).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 45).take 1 :=
  view45.trans (piece45.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 45 1))

numeric_data_binding view46 : (data.drop 46).take 1 = (data40.drop 6).take 1

numeric_data_binding piece46 : (data40.drop 6).take 1 = ((originalEntries.drop 46).take 1).map NumericFunctionalBaseChecks.encode

theorem binding46 : (data.drop 46).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 46).take 1 :=
  view46.trans (piece46.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 46 1))

numeric_data_binding view47 : (data.drop 47).take 1 = (data40.drop 7).take 1

numeric_data_binding piece47 : (data40.drop 7).take 1 = ((originalEntries.drop 47).take 1).map NumericFunctionalBaseChecks.encode

theorem binding47 : (data.drop 47).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 47).take 1 :=
  view47.trans (piece47.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 47 1))

numeric_data_binding view48 : (data.drop 48).take 1 = (data48.drop 0).take 1

numeric_data_binding piece48 : (data48.drop 0).take 1 = ((originalEntries.drop 48).take 1).map NumericFunctionalBaseChecks.encode

theorem binding48 : (data.drop 48).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 48).take 1 :=
  view48.trans (piece48.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 48 1))

numeric_data_binding view49 : (data.drop 49).take 1 = (data48.drop 1).take 1

numeric_data_binding piece49 : (data48.drop 1).take 1 = ((originalEntries.drop 49).take 1).map NumericFunctionalBaseChecks.encode

theorem binding49 : (data.drop 49).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 49).take 1 :=
  view49.trans (piece49.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 49 1))

numeric_data_binding view50 : (data.drop 50).take 1 = (data48.drop 2).take 1

numeric_data_binding piece50 : (data48.drop 2).take 1 = ((originalEntries.drop 50).take 1).map NumericFunctionalBaseChecks.encode

theorem binding50 : (data.drop 50).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 50).take 1 :=
  view50.trans (piece50.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 50 1))

numeric_data_binding view51 : (data.drop 51).take 1 = (data48.drop 3).take 1

numeric_data_binding piece51 : (data48.drop 3).take 1 = ((originalEntries.drop 51).take 1).map NumericFunctionalBaseChecks.encode

theorem binding51 : (data.drop 51).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 51).take 1 :=
  view51.trans (piece51.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 51 1))

numeric_data_binding view52 : (data.drop 52).take 1 = (data48.drop 4).take 1

numeric_data_binding piece52 : (data48.drop 4).take 1 = ((originalEntries.drop 52).take 1).map NumericFunctionalBaseChecks.encode

theorem binding52 : (data.drop 52).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 52).take 1 :=
  view52.trans (piece52.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 52 1))

numeric_data_binding view53 : (data.drop 53).take 1 = (data48.drop 5).take 1

numeric_data_binding piece53 : (data48.drop 5).take 1 = ((originalEntries.drop 53).take 1).map NumericFunctionalBaseChecks.encode

theorem binding53 : (data.drop 53).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 53).take 1 :=
  view53.trans (piece53.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 53 1))

numeric_data_binding view54 : (data.drop 54).take 1 = (data48.drop 6).take 1

numeric_data_binding piece54 : (data48.drop 6).take 1 = ((originalEntries.drop 54).take 1).map NumericFunctionalBaseChecks.encode

theorem binding54 : (data.drop 54).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 54).take 1 :=
  view54.trans (piece54.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 54 1))

numeric_data_binding view55 : (data.drop 55).take 1 = (data48.drop 7).take 1

numeric_data_binding piece55 : (data48.drop 7).take 1 = ((originalEntries.drop 55).take 1).map NumericFunctionalBaseChecks.encode

theorem binding55 : (data.drop 55).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 55).take 1 :=
  view55.trans (piece55.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 55 1))

numeric_data_binding view56 : (data.drop 56).take 1 = (data56.drop 0).take 1

numeric_data_binding piece56 : (data56.drop 0).take 1 = ((originalEntries.drop 56).take 1).map NumericFunctionalBaseChecks.encode

theorem binding56 : (data.drop 56).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 56).take 1 :=
  view56.trans (piece56.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 56 1))

numeric_data_binding view57 : (data.drop 57).take 1 = (data56.drop 1).take 1

numeric_data_binding piece57 : (data56.drop 1).take 1 = ((originalEntries.drop 57).take 1).map NumericFunctionalBaseChecks.encode

theorem binding57 : (data.drop 57).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 57).take 1 :=
  view57.trans (piece57.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 57 1))

numeric_data_binding view58 : (data.drop 58).take 1 = (data56.drop 2).take 1

numeric_data_binding piece58 : (data56.drop 2).take 1 = ((originalEntries.drop 58).take 1).map NumericFunctionalBaseChecks.encode

theorem binding58 : (data.drop 58).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 58).take 1 :=
  view58.trans (piece58.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 58 1))

numeric_data_binding view59 : (data.drop 59).take 1 = (data56.drop 3).take 1

numeric_data_binding piece59 : (data56.drop 3).take 1 = ((originalEntries.drop 59).take 1).map NumericFunctionalBaseChecks.encode

theorem binding59 : (data.drop 59).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 59).take 1 :=
  view59.trans (piece59.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 59 1))

numeric_data_binding view60 : (data.drop 60).take 1 = (data56.drop 4).take 1

numeric_data_binding piece60 : (data56.drop 4).take 1 = ((originalEntries.drop 60).take 1).map NumericFunctionalBaseChecks.encode

theorem binding60 : (data.drop 60).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 60).take 1 :=
  view60.trans (piece60.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 60 1))

numeric_data_binding view61 : (data.drop 61).take 1 = (data56.drop 5).take 1

numeric_data_binding piece61 : (data56.drop 5).take 1 = ((originalEntries.drop 61).take 1).map NumericFunctionalBaseChecks.encode

theorem binding61 : (data.drop 61).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 61).take 1 :=
  view61.trans (piece61.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 61 1))

numeric_data_binding view62 : (data.drop 62).take 1 = (data56.drop 6).take 1

numeric_data_binding piece62 : (data56.drop 6).take 1 = ((originalEntries.drop 62).take 1).map NumericFunctionalBaseChecks.encode

theorem binding62 : (data.drop 62).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 62).take 1 :=
  view62.trans (piece62.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 62 1))

numeric_data_binding view63 : (data.drop 63).take 1 = (data56.drop 7).take 1

numeric_data_binding piece63 : (data56.drop 7).take 1 = ((originalEntries.drop 63).take 1).map NumericFunctionalBaseChecks.encode

theorem binding63 : (data.drop 63).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 63).take 1 :=
  view63.trans (piece63.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 63 1))

numeric_data_binding view64 : (data.drop 64).take 1 = (data64.drop 0).take 1

numeric_data_binding piece64 : (data64.drop 0).take 1 = ((originalEntries.drop 64).take 1).map NumericFunctionalBaseChecks.encode

theorem binding64 : (data.drop 64).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 1 :=
  view64.trans (piece64.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 64 1))

numeric_data_binding view65 : (data.drop 65).take 1 = (data64.drop 1).take 1

numeric_data_binding piece65 : (data64.drop 1).take 1 = ((originalEntries.drop 65).take 1).map NumericFunctionalBaseChecks.encode

theorem binding65 : (data.drop 65).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 65).take 1 :=
  view65.trans (piece65.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 65 1))

numeric_data_binding view66 : (data.drop 66).take 1 = (data64.drop 2).take 1

numeric_data_binding piece66 : (data64.drop 2).take 1 = ((originalEntries.drop 66).take 1).map NumericFunctionalBaseChecks.encode

theorem binding66 : (data.drop 66).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 66).take 1 :=
  view66.trans (piece66.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 66 1))

numeric_data_binding view67 : (data.drop 67).take 1 = (data64.drop 3).take 1

numeric_data_binding piece67 : (data64.drop 3).take 1 = ((originalEntries.drop 67).take 1).map NumericFunctionalBaseChecks.encode

theorem binding67 : (data.drop 67).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 67).take 1 :=
  view67.trans (piece67.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 67 1))

numeric_data_binding view68 : (data.drop 68).take 1 = (data64.drop 4).take 1

numeric_data_binding piece68 : (data64.drop 4).take 1 = ((originalEntries.drop 68).take 1).map NumericFunctionalBaseChecks.encode

theorem binding68 : (data.drop 68).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 68).take 1 :=
  view68.trans (piece68.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 68 1))

numeric_data_binding view69 : (data.drop 69).take 1 = (data64.drop 5).take 1

numeric_data_binding piece69 : (data64.drop 5).take 1 = ((originalEntries.drop 69).take 1).map NumericFunctionalBaseChecks.encode

theorem binding69 : (data.drop 69).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 69).take 1 :=
  view69.trans (piece69.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 69 1))

numeric_data_binding view70 : (data.drop 70).take 1 = (data64.drop 6).take 1

numeric_data_binding piece70 : (data64.drop 6).take 1 = ((originalEntries.drop 70).take 1).map NumericFunctionalBaseChecks.encode

theorem binding70 : (data.drop 70).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 70).take 1 :=
  view70.trans (piece70.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 70 1))

numeric_data_binding view71 : (data.drop 71).take 1 = (data64.drop 7).take 1

numeric_data_binding piece71 : (data64.drop 7).take 1 = ((originalEntries.drop 71).take 1).map NumericFunctionalBaseChecks.encode

theorem binding71 : (data.drop 71).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 71).take 1 :=
  view71.trans (piece71.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 71 1))

numeric_data_binding view72 : (data.drop 72).take 1 = (data72.drop 0).take 1

numeric_data_binding piece72 : (data72.drop 0).take 1 = ((originalEntries.drop 72).take 1).map NumericFunctionalBaseChecks.encode

theorem binding72 : (data.drop 72).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 72).take 1 :=
  view72.trans (piece72.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 72 1))

numeric_data_binding view73 : (data.drop 73).take 1 = (data72.drop 1).take 1

numeric_data_binding piece73 : (data72.drop 1).take 1 = ((originalEntries.drop 73).take 1).map NumericFunctionalBaseChecks.encode

theorem binding73 : (data.drop 73).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 73).take 1 :=
  view73.trans (piece73.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 73 1))

numeric_data_binding view74 : (data.drop 74).take 1 = (data72.drop 2).take 1

numeric_data_binding piece74 : (data72.drop 2).take 1 = ((originalEntries.drop 74).take 1).map NumericFunctionalBaseChecks.encode

theorem binding74 : (data.drop 74).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 74).take 1 :=
  view74.trans (piece74.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 74 1))

numeric_data_binding view75 : (data.drop 75).take 1 = (data72.drop 3).take 1

numeric_data_binding piece75 : (data72.drop 3).take 1 = ((originalEntries.drop 75).take 1).map NumericFunctionalBaseChecks.encode

theorem binding75 : (data.drop 75).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 75).take 1 :=
  view75.trans (piece75.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 75 1))

numeric_data_binding view76 : (data.drop 76).take 1 = (data72.drop 4).take 1

numeric_data_binding piece76 : (data72.drop 4).take 1 = ((originalEntries.drop 76).take 1).map NumericFunctionalBaseChecks.encode

theorem binding76 : (data.drop 76).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 76).take 1 :=
  view76.trans (piece76.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 76 1))

numeric_data_binding view77 : (data.drop 77).take 1 = (data72.drop 5).take 1

numeric_data_binding piece77 : (data72.drop 5).take 1 = ((originalEntries.drop 77).take 1).map NumericFunctionalBaseChecks.encode

theorem binding77 : (data.drop 77).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 77).take 1 :=
  view77.trans (piece77.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 77 1))

numeric_data_binding view78 : (data.drop 78).take 1 = (data72.drop 6).take 1

numeric_data_binding piece78 : (data72.drop 6).take 1 = ((originalEntries.drop 78).take 1).map NumericFunctionalBaseChecks.encode

theorem binding78 : (data.drop 78).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 78).take 1 :=
  view78.trans (piece78.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 78 1))

numeric_data_binding view79 : (data.drop 79).take 1 = (data72.drop 7).take 1

numeric_data_binding piece79 : (data72.drop 7).take 1 = ((originalEntries.drop 79).take 1).map NumericFunctionalBaseChecks.encode

theorem binding79 : (data.drop 79).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 79).take 1 :=
  view79.trans (piece79.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 79 1))

numeric_data_binding view80 : (data.drop 80).take 1 = (data80.drop 0).take 1

numeric_data_binding piece80 : (data80.drop 0).take 1 = ((originalEntries.drop 80).take 1).map NumericFunctionalBaseChecks.encode

theorem binding80 : (data.drop 80).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 1 :=
  view80.trans (piece80.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 80 1))

numeric_data_binding view81 : (data.drop 81).take 1 = (data80.drop 1).take 1

numeric_data_binding piece81 : (data80.drop 1).take 1 = ((originalEntries.drop 81).take 1).map NumericFunctionalBaseChecks.encode

theorem binding81 : (data.drop 81).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 81).take 1 :=
  view81.trans (piece81.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 81 1))

numeric_data_binding view82 : (data.drop 82).take 1 = (data80.drop 2).take 1

numeric_data_binding piece82 : (data80.drop 2).take 1 = ((originalEntries.drop 82).take 1).map NumericFunctionalBaseChecks.encode

theorem binding82 : (data.drop 82).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 82).take 1 :=
  view82.trans (piece82.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 82 1))

numeric_data_binding view83 : (data.drop 83).take 1 = (data80.drop 3).take 1

numeric_data_binding piece83 : (data80.drop 3).take 1 = ((originalEntries.drop 83).take 1).map NumericFunctionalBaseChecks.encode

theorem binding83 : (data.drop 83).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 83).take 1 :=
  view83.trans (piece83.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 83 1))

numeric_data_binding view84 : (data.drop 84).take 1 = (data80.drop 4).take 1

numeric_data_binding piece84 : (data80.drop 4).take 1 = ((originalEntries.drop 84).take 1).map NumericFunctionalBaseChecks.encode

theorem binding84 : (data.drop 84).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 84).take 1 :=
  view84.trans (piece84.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 84 1))

numeric_data_binding view85 : (data.drop 85).take 1 = (data80.drop 5).take 1

numeric_data_binding piece85 : (data80.drop 5).take 1 = ((originalEntries.drop 85).take 1).map NumericFunctionalBaseChecks.encode

theorem binding85 : (data.drop 85).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 85).take 1 :=
  view85.trans (piece85.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 85 1))

numeric_data_binding view86 : (data.drop 86).take 1 = (data80.drop 6).take 1

numeric_data_binding piece86 : (data80.drop 6).take 1 = ((originalEntries.drop 86).take 1).map NumericFunctionalBaseChecks.encode

theorem binding86 : (data.drop 86).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 86).take 1 :=
  view86.trans (piece86.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 86 1))

numeric_data_binding view87 : (data.drop 87).take 1 = (data80.drop 7).take 1

numeric_data_binding piece87 : (data80.drop 7).take 1 = ((originalEntries.drop 87).take 1).map NumericFunctionalBaseChecks.encode

theorem binding87 : (data.drop 87).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 87).take 1 :=
  view87.trans (piece87.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 87 1))

numeric_data_binding view88 : (data.drop 88).take 1 = (data88.drop 0).take 1

numeric_data_binding piece88 : (data88.drop 0).take 1 = ((originalEntries.drop 88).take 1).map NumericFunctionalBaseChecks.encode

theorem binding88 : (data.drop 88).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 88).take 1 :=
  view88.trans (piece88.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 88 1))

numeric_data_binding view89 : (data.drop 89).take 1 = (data88.drop 1).take 1

numeric_data_binding piece89 : (data88.drop 1).take 1 = ((originalEntries.drop 89).take 1).map NumericFunctionalBaseChecks.encode

theorem binding89 : (data.drop 89).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 89).take 1 :=
  view89.trans (piece89.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 89 1))

numeric_data_binding view90 : (data.drop 90).take 1 = (data88.drop 2).take 1

numeric_data_binding piece90 : (data88.drop 2).take 1 = ((originalEntries.drop 90).take 1).map NumericFunctionalBaseChecks.encode

theorem binding90 : (data.drop 90).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 90).take 1 :=
  view90.trans (piece90.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 90 1))

numeric_data_binding view91 : (data.drop 91).take 1 = (data88.drop 3).take 1

numeric_data_binding piece91 : (data88.drop 3).take 1 = ((originalEntries.drop 91).take 1).map NumericFunctionalBaseChecks.encode

theorem binding91 : (data.drop 91).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 91).take 1 :=
  view91.trans (piece91.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 91 1))

numeric_data_binding view92 : (data.drop 92).take 1 = (data88.drop 4).take 1

numeric_data_binding piece92 : (data88.drop 4).take 1 = ((originalEntries.drop 92).take 1).map NumericFunctionalBaseChecks.encode

theorem binding92 : (data.drop 92).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 92).take 1 :=
  view92.trans (piece92.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 92 1))

numeric_data_binding view93 : (data.drop 93).take 1 = (data88.drop 5).take 1

numeric_data_binding piece93 : (data88.drop 5).take 1 = ((originalEntries.drop 93).take 1).map NumericFunctionalBaseChecks.encode

theorem binding93 : (data.drop 93).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 93).take 1 :=
  view93.trans (piece93.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 93 1))

numeric_data_binding view94 : (data.drop 94).take 1 = (data88.drop 6).take 1

numeric_data_binding piece94 : (data88.drop 6).take 1 = ((originalEntries.drop 94).take 1).map NumericFunctionalBaseChecks.encode

theorem binding94 : (data.drop 94).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 94).take 1 :=
  view94.trans (piece94.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 94 1))

numeric_data_binding view95 : (data.drop 95).take 1 = (data88.drop 7).take 1

numeric_data_binding piece95 : (data88.drop 7).take 1 = ((originalEntries.drop 95).take 1).map NumericFunctionalBaseChecks.encode

theorem binding95 : (data.drop 95).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 95).take 1 :=
  view95.trans (piece95.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 95 1))

numeric_data_binding view96 : (data.drop 96).take 1 = (data96.drop 0).take 1

numeric_data_binding piece96 : (data96.drop 0).take 1 = ((originalEntries.drop 96).take 1).map NumericFunctionalBaseChecks.encode

theorem binding96 : (data.drop 96).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 96).take 1 :=
  view96.trans (piece96.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 96 1))

numeric_data_binding view97 : (data.drop 97).take 1 = (data96.drop 1).take 1

numeric_data_binding piece97 : (data96.drop 1).take 1 = ((originalEntries.drop 97).take 1).map NumericFunctionalBaseChecks.encode

theorem binding97 : (data.drop 97).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 97).take 1 :=
  view97.trans (piece97.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 97 1))

numeric_data_binding view98 : (data.drop 98).take 1 = (data96.drop 2).take 1

numeric_data_binding piece98 : (data96.drop 2).take 1 = ((originalEntries.drop 98).take 1).map NumericFunctionalBaseChecks.encode

theorem binding98 : (data.drop 98).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 98).take 1 :=
  view98.trans (piece98.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 98 1))

numeric_data_binding view99 : (data.drop 99).take 1 = (data96.drop 3).take 1

numeric_data_binding piece99 : (data96.drop 3).take 1 = ((originalEntries.drop 99).take 1).map NumericFunctionalBaseChecks.encode

theorem binding99 : (data.drop 99).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 99).take 1 :=
  view99.trans (piece99.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 99 1))

numeric_data_binding view100 : (data.drop 100).take 1 = (data96.drop 4).take 1

numeric_data_binding piece100 : (data96.drop 4).take 1 = ((originalEntries.drop 100).take 1).map NumericFunctionalBaseChecks.encode

theorem binding100 : (data.drop 100).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 100).take 1 :=
  view100.trans (piece100.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 100 1))

numeric_data_binding view101 : (data.drop 101).take 1 = (data96.drop 5).take 1

numeric_data_binding piece101 : (data96.drop 5).take 1 = ((originalEntries.drop 101).take 1).map NumericFunctionalBaseChecks.encode

theorem binding101 : (data.drop 101).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 101).take 1 :=
  view101.trans (piece101.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 101 1))

numeric_data_binding view102 : (data.drop 102).take 1 = (data96.drop 6).take 1

numeric_data_binding piece102 : (data96.drop 6).take 1 = ((originalEntries.drop 102).take 1).map NumericFunctionalBaseChecks.encode

theorem binding102 : (data.drop 102).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 102).take 1 :=
  view102.trans (piece102.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 102 1))

numeric_data_binding view103 : (data.drop 103).take 1 = (data96.drop 7).take 1

numeric_data_binding piece103 : (data96.drop 7).take 1 = ((originalEntries.drop 103).take 1).map NumericFunctionalBaseChecks.encode

theorem binding103 : (data.drop 103).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 103).take 1 :=
  view103.trans (piece103.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 103 1))

numeric_data_binding view104 : (data.drop 104).take 1 = (data104.drop 0).take 1

numeric_data_binding piece104 : (data104.drop 0).take 1 = ((originalEntries.drop 104).take 1).map NumericFunctionalBaseChecks.encode

theorem binding104 : (data.drop 104).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 104).take 1 :=
  view104.trans (piece104.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 104 1))

numeric_data_binding view105 : (data.drop 105).take 1 = (data104.drop 1).take 1

numeric_data_binding piece105 : (data104.drop 1).take 1 = ((originalEntries.drop 105).take 1).map NumericFunctionalBaseChecks.encode

theorem binding105 : (data.drop 105).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 105).take 1 :=
  view105.trans (piece105.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 105 1))

numeric_data_binding view106 : (data.drop 106).take 1 = (data104.drop 2).take 1

numeric_data_binding piece106 : (data104.drop 2).take 1 = ((originalEntries.drop 106).take 1).map NumericFunctionalBaseChecks.encode

theorem binding106 : (data.drop 106).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 106).take 1 :=
  view106.trans (piece106.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 106 1))

numeric_data_binding view107 : (data.drop 107).take 1 = (data104.drop 3).take 1

numeric_data_binding piece107 : (data104.drop 3).take 1 = ((originalEntries.drop 107).take 1).map NumericFunctionalBaseChecks.encode

theorem binding107 : (data.drop 107).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 107).take 1 :=
  view107.trans (piece107.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 107 1))

numeric_data_binding view108 : (data.drop 108).take 1 = (data104.drop 4).take 1

numeric_data_binding piece108 : (data104.drop 4).take 1 = ((originalEntries.drop 108).take 1).map NumericFunctionalBaseChecks.encode

theorem binding108 : (data.drop 108).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 108).take 1 :=
  view108.trans (piece108.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 108 1))

numeric_data_binding view109 : (data.drop 109).take 1 = (data104.drop 5).take 1

numeric_data_binding piece109 : (data104.drop 5).take 1 = ((originalEntries.drop 109).take 1).map NumericFunctionalBaseChecks.encode

theorem binding109 : (data.drop 109).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 109).take 1 :=
  view109.trans (piece109.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 109 1))

numeric_data_binding view110 : (data.drop 110).take 1 = (data104.drop 6).take 1

numeric_data_binding piece110 : (data104.drop 6).take 1 = ((originalEntries.drop 110).take 1).map NumericFunctionalBaseChecks.encode

theorem binding110 : (data.drop 110).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 110).take 1 :=
  view110.trans (piece110.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 110 1))

numeric_data_binding view111 : (data.drop 111).take 1 = (data104.drop 7).take 1

numeric_data_binding piece111 : (data104.drop 7).take 1 = ((originalEntries.drop 111).take 1).map NumericFunctionalBaseChecks.encode

theorem binding111 : (data.drop 111).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 111).take 1 :=
  view111.trans (piece111.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 111 1))

numeric_data_binding view112 : (data.drop 112).take 1 = (data112.drop 0).take 1

numeric_data_binding piece112 : (data112.drop 0).take 1 = ((originalEntries.drop 112).take 1).map NumericFunctionalBaseChecks.encode

theorem binding112 : (data.drop 112).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 112).take 1 :=
  view112.trans (piece112.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 112 1))

numeric_data_binding view113 : (data.drop 113).take 1 = (data112.drop 1).take 1

numeric_data_binding piece113 : (data112.drop 1).take 1 = ((originalEntries.drop 113).take 1).map NumericFunctionalBaseChecks.encode

theorem binding113 : (data.drop 113).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 113).take 1 :=
  view113.trans (piece113.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 113 1))

numeric_data_binding view114 : (data.drop 114).take 1 = (data112.drop 2).take 1

numeric_data_binding piece114 : (data112.drop 2).take 1 = ((originalEntries.drop 114).take 1).map NumericFunctionalBaseChecks.encode

theorem binding114 : (data.drop 114).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 114).take 1 :=
  view114.trans (piece114.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 114 1))

numeric_data_binding view115 : (data.drop 115).take 1 = (data112.drop 3).take 1

numeric_data_binding piece115 : (data112.drop 3).take 1 = ((originalEntries.drop 115).take 1).map NumericFunctionalBaseChecks.encode

theorem binding115 : (data.drop 115).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 115).take 1 :=
  view115.trans (piece115.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 115 1))

numeric_data_binding view116 : (data.drop 116).take 1 = (data112.drop 4).take 1

numeric_data_binding piece116 : (data112.drop 4).take 1 = ((originalEntries.drop 116).take 1).map NumericFunctionalBaseChecks.encode

theorem binding116 : (data.drop 116).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 116).take 1 :=
  view116.trans (piece116.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 116 1))

numeric_data_binding view117 : (data.drop 117).take 1 = (data112.drop 5).take 1

numeric_data_binding piece117 : (data112.drop 5).take 1 = ((originalEntries.drop 117).take 1).map NumericFunctionalBaseChecks.encode

theorem binding117 : (data.drop 117).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 117).take 1 :=
  view117.trans (piece117.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 117 1))

numeric_data_binding view118 : (data.drop 118).take 1 = (data112.drop 6).take 1

numeric_data_binding piece118 : (data112.drop 6).take 1 = ((originalEntries.drop 118).take 1).map NumericFunctionalBaseChecks.encode

theorem binding118 : (data.drop 118).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 118).take 1 :=
  view118.trans (piece118.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 118 1))

numeric_data_binding view119 : (data.drop 119).take 1 = (data112.drop 7).take 1

numeric_data_binding piece119 : (data112.drop 7).take 1 = ((originalEntries.drop 119).take 1).map NumericFunctionalBaseChecks.encode

theorem binding119 : (data.drop 119).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 119).take 1 :=
  view119.trans (piece119.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 119 1))

numeric_data_binding view120 : (data.drop 120).take 1 = (data120.drop 0).take 1

numeric_data_binding piece120 : (data120.drop 0).take 1 = ((originalEntries.drop 120).take 1).map NumericFunctionalBaseChecks.encode

theorem binding120 : (data.drop 120).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 120).take 1 :=
  view120.trans (piece120.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 120 1))

numeric_data_binding view121 : (data.drop 121).take 1 = (data120.drop 1).take 1

numeric_data_binding piece121 : (data120.drop 1).take 1 = ((originalEntries.drop 121).take 1).map NumericFunctionalBaseChecks.encode

theorem binding121 : (data.drop 121).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 121).take 1 :=
  view121.trans (piece121.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 121 1))

numeric_data_binding view122 : (data.drop 122).take 1 = (data120.drop 2).take 1

numeric_data_binding piece122 : (data120.drop 2).take 1 = ((originalEntries.drop 122).take 1).map NumericFunctionalBaseChecks.encode

theorem binding122 : (data.drop 122).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 122).take 1 :=
  view122.trans (piece122.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 122 1))

numeric_data_binding view123 : (data.drop 123).take 1 = (data120.drop 3).take 1

numeric_data_binding piece123 : (data120.drop 3).take 1 = ((originalEntries.drop 123).take 1).map NumericFunctionalBaseChecks.encode

theorem binding123 : (data.drop 123).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 123).take 1 :=
  view123.trans (piece123.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 123 1))

numeric_data_binding view124 : (data.drop 124).take 1 = (data120.drop 4).take 1

numeric_data_binding piece124 : (data120.drop 4).take 1 = ((originalEntries.drop 124).take 1).map NumericFunctionalBaseChecks.encode

theorem binding124 : (data.drop 124).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 124).take 1 :=
  view124.trans (piece124.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 124 1))

numeric_data_binding view125 : (data.drop 125).take 1 = (data120.drop 5).take 1

numeric_data_binding piece125 : (data120.drop 5).take 1 = ((originalEntries.drop 125).take 1).map NumericFunctionalBaseChecks.encode

theorem binding125 : (data.drop 125).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 125).take 1 :=
  view125.trans (piece125.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 125 1))

numeric_data_binding view126 : (data.drop 126).take 1 = (data120.drop 6).take 1

numeric_data_binding piece126 : (data120.drop 6).take 1 = ((originalEntries.drop 126).take 1).map NumericFunctionalBaseChecks.encode

theorem binding126 : (data.drop 126).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 126).take 1 :=
  view126.trans (piece126.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 126 1))

numeric_data_binding view127 : (data.drop 127).take 1 = (data120.drop 7).take 1

numeric_data_binding piece127 : (data120.drop 7).take 1 = ((originalEntries.drop 127).take 1).map NumericFunctionalBaseChecks.encode

theorem binding127 : (data.drop 127).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 127).take 1 :=
  view127.trans (piece127.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 127 1))

numeric_data_binding view128 : (data.drop 128).take 1 = (data128.drop 0).take 1

numeric_data_binding piece128 : (data128.drop 0).take 1 = ((originalEntries.drop 128).take 1).map NumericFunctionalBaseChecks.encode

theorem binding128 : (data.drop 128).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 128).take 1 :=
  view128.trans (piece128.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 128 1))

numeric_data_binding view129 : (data.drop 129).take 1 = (data128.drop 1).take 1

numeric_data_binding piece129 : (data128.drop 1).take 1 = ((originalEntries.drop 129).take 1).map NumericFunctionalBaseChecks.encode

theorem binding129 : (data.drop 129).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 129).take 1 :=
  view129.trans (piece129.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 129 1))

numeric_data_binding view130 : (data.drop 130).take 1 = (data128.drop 2).take 1

numeric_data_binding piece130 : (data128.drop 2).take 1 = ((originalEntries.drop 130).take 1).map NumericFunctionalBaseChecks.encode

theorem binding130 : (data.drop 130).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 130).take 1 :=
  view130.trans (piece130.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 130 1))

numeric_data_binding view131 : (data.drop 131).take 1 = (data128.drop 3).take 1

numeric_data_binding piece131 : (data128.drop 3).take 1 = ((originalEntries.drop 131).take 1).map NumericFunctionalBaseChecks.encode

theorem binding131 : (data.drop 131).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 131).take 1 :=
  view131.trans (piece131.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 131 1))

numeric_data_binding view132 : (data.drop 132).take 1 = (data128.drop 4).take 1

numeric_data_binding piece132 : (data128.drop 4).take 1 = ((originalEntries.drop 132).take 1).map NumericFunctionalBaseChecks.encode

theorem binding132 : (data.drop 132).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 132).take 1 :=
  view132.trans (piece132.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 132 1))

numeric_data_binding view133 : (data.drop 133).take 1 = (data128.drop 5).take 1

numeric_data_binding piece133 : (data128.drop 5).take 1 = ((originalEntries.drop 133).take 1).map NumericFunctionalBaseChecks.encode

theorem binding133 : (data.drop 133).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 133).take 1 :=
  view133.trans (piece133.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 133 1))

numeric_data_binding view134 : (data.drop 134).take 1 = (data128.drop 6).take 1

numeric_data_binding piece134 : (data128.drop 6).take 1 = ((originalEntries.drop 134).take 1).map NumericFunctionalBaseChecks.encode

theorem binding134 : (data.drop 134).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 134).take 1 :=
  view134.trans (piece134.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 134 1))

numeric_data_binding view135 : (data.drop 135).take 1 = (data128.drop 7).take 1

numeric_data_binding piece135 : (data128.drop 7).take 1 = ((originalEntries.drop 135).take 1).map NumericFunctionalBaseChecks.encode

theorem binding135 : (data.drop 135).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 135).take 1 :=
  view135.trans (piece135.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 135 1))

numeric_data_binding view136 : (data.drop 136).take 1 = (data136.drop 0).take 1

numeric_data_binding piece136 : (data136.drop 0).take 1 = ((originalEntries.drop 136).take 1).map NumericFunctionalBaseChecks.encode

theorem binding136 : (data.drop 136).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 136).take 1 :=
  view136.trans (piece136.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 136 1))

numeric_data_binding view137 : (data.drop 137).take 1 = (data136.drop 1).take 1

numeric_data_binding piece137 : (data136.drop 1).take 1 = ((originalEntries.drop 137).take 1).map NumericFunctionalBaseChecks.encode

theorem binding137 : (data.drop 137).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 137).take 1 :=
  view137.trans (piece137.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 137 1))

numeric_data_binding view138 : (data.drop 138).take 1 = (data136.drop 2).take 1

numeric_data_binding piece138 : (data136.drop 2).take 1 = ((originalEntries.drop 138).take 1).map NumericFunctionalBaseChecks.encode

theorem binding138 : (data.drop 138).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 138).take 1 :=
  view138.trans (piece138.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 138 1))

numeric_data_binding view139 : (data.drop 139).take 1 = (data136.drop 3).take 1

numeric_data_binding piece139 : (data136.drop 3).take 1 = ((originalEntries.drop 139).take 1).map NumericFunctionalBaseChecks.encode

theorem binding139 : (data.drop 139).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 139).take 1 :=
  view139.trans (piece139.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 139 1))

numeric_data_binding view140 : (data.drop 140).take 1 = (data136.drop 4).take 1

numeric_data_binding piece140 : (data136.drop 4).take 1 = ((originalEntries.drop 140).take 1).map NumericFunctionalBaseChecks.encode

theorem binding140 : (data.drop 140).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 140).take 1 :=
  view140.trans (piece140.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 140 1))

numeric_data_binding view141 : (data.drop 141).take 1 = (data136.drop 5).take 1

numeric_data_binding piece141 : (data136.drop 5).take 1 = ((originalEntries.drop 141).take 1).map NumericFunctionalBaseChecks.encode

theorem binding141 : (data.drop 141).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 141).take 1 :=
  view141.trans (piece141.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 141 1))

numeric_data_binding view142 : (data.drop 142).take 1 = (data136.drop 6).take 1

numeric_data_binding piece142 : (data136.drop 6).take 1 = ((originalEntries.drop 142).take 1).map NumericFunctionalBaseChecks.encode

theorem binding142 : (data.drop 142).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 142).take 1 :=
  view142.trans (piece142.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 142 1))

numeric_data_binding view143 : (data.drop 143).take 1 = (data136.drop 7).take 1

numeric_data_binding piece143 : (data136.drop 7).take 1 = ((originalEntries.drop 143).take 1).map NumericFunctionalBaseChecks.encode

theorem binding143 : (data.drop 143).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 143).take 1 :=
  view143.trans (piece143.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 143 1))

numeric_data_binding view144 : (data.drop 144).take 1 = (data144.drop 0).take 1

numeric_data_binding piece144 : (data144.drop 0).take 1 = ((originalEntries.drop 144).take 1).map NumericFunctionalBaseChecks.encode

theorem binding144 : (data.drop 144).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 144).take 1 :=
  view144.trans (piece144.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 144 1))

numeric_data_binding view145 : (data.drop 145).take 1 = (data144.drop 1).take 1

numeric_data_binding piece145 : (data144.drop 1).take 1 = ((originalEntries.drop 145).take 1).map NumericFunctionalBaseChecks.encode

theorem binding145 : (data.drop 145).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 145).take 1 :=
  view145.trans (piece145.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 145 1))

numeric_data_binding view146 : (data.drop 146).take 1 = (data144.drop 2).take 1

numeric_data_binding piece146 : (data144.drop 2).take 1 = ((originalEntries.drop 146).take 1).map NumericFunctionalBaseChecks.encode

theorem binding146 : (data.drop 146).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 146).take 1 :=
  view146.trans (piece146.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 146 1))

numeric_data_binding view147 : (data.drop 147).take 1 = (data144.drop 3).take 1

numeric_data_binding piece147 : (data144.drop 3).take 1 = ((originalEntries.drop 147).take 1).map NumericFunctionalBaseChecks.encode

theorem binding147 : (data.drop 147).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 147).take 1 :=
  view147.trans (piece147.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 147 1))

numeric_data_binding view148 : (data.drop 148).take 1 = (data144.drop 4).take 1

numeric_data_binding piece148 : (data144.drop 4).take 1 = ((originalEntries.drop 148).take 1).map NumericFunctionalBaseChecks.encode

theorem binding148 : (data.drop 148).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 148).take 1 :=
  view148.trans (piece148.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 148 1))

numeric_data_binding view149 : (data.drop 149).take 1 = (data144.drop 5).take 1

numeric_data_binding piece149 : (data144.drop 5).take 1 = ((originalEntries.drop 149).take 1).map NumericFunctionalBaseChecks.encode

theorem binding149 : (data.drop 149).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 149).take 1 :=
  view149.trans (piece149.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 149 1))

numeric_data_binding view150 : (data.drop 150).take 1 = (data144.drop 6).take 1

numeric_data_binding piece150 : (data144.drop 6).take 1 = ((originalEntries.drop 150).take 1).map NumericFunctionalBaseChecks.encode

theorem binding150 : (data.drop 150).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 150).take 1 :=
  view150.trans (piece150.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 150 1))

numeric_data_binding view151 : (data.drop 151).take 1 = (data144.drop 7).take 1

numeric_data_binding piece151 : (data144.drop 7).take 1 = ((originalEntries.drop 151).take 1).map NumericFunctionalBaseChecks.encode

theorem binding151 : (data.drop 151).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 151).take 1 :=
  view151.trans (piece151.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 151 1))

numeric_data_binding view152 : (data.drop 152).take 1 = (data152.drop 0).take 1

numeric_data_binding piece152 : (data152.drop 0).take 1 = ((originalEntries.drop 152).take 1).map NumericFunctionalBaseChecks.encode

theorem binding152 : (data.drop 152).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 152).take 1 :=
  view152.trans (piece152.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 152 1))

numeric_data_binding view153 : (data.drop 153).take 1 = (data152.drop 1).take 1

numeric_data_binding piece153 : (data152.drop 1).take 1 = ((originalEntries.drop 153).take 1).map NumericFunctionalBaseChecks.encode

theorem binding153 : (data.drop 153).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 153).take 1 :=
  view153.trans (piece153.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 153 1))

numeric_data_binding view154 : (data.drop 154).take 1 = (data152.drop 2).take 1

numeric_data_binding piece154 : (data152.drop 2).take 1 = ((originalEntries.drop 154).take 1).map NumericFunctionalBaseChecks.encode

theorem binding154 : (data.drop 154).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 154).take 1 :=
  view154.trans (piece154.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 154 1))

numeric_data_binding view155 : (data.drop 155).take 1 = (data152.drop 3).take 1

numeric_data_binding piece155 : (data152.drop 3).take 1 = ((originalEntries.drop 155).take 1).map NumericFunctionalBaseChecks.encode

theorem binding155 : (data.drop 155).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 155).take 1 :=
  view155.trans (piece155.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 155 1))

numeric_data_binding view156 : (data.drop 156).take 1 = (data152.drop 4).take 1

numeric_data_binding piece156 : (data152.drop 4).take 1 = ((originalEntries.drop 156).take 1).map NumericFunctionalBaseChecks.encode

theorem binding156 : (data.drop 156).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 156).take 1 :=
  view156.trans (piece156.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 156 1))

numeric_data_binding view157 : (data.drop 157).take 1 = (data152.drop 5).take 1

numeric_data_binding piece157 : (data152.drop 5).take 1 = ((originalEntries.drop 157).take 1).map NumericFunctionalBaseChecks.encode

theorem binding157 : (data.drop 157).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 157).take 1 :=
  view157.trans (piece157.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 157 1))

numeric_data_binding view158 : (data.drop 158).take 1 = (data152.drop 6).take 1

numeric_data_binding piece158 : (data152.drop 6).take 1 = ((originalEntries.drop 158).take 1).map NumericFunctionalBaseChecks.encode

theorem binding158 : (data.drop 158).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 158).take 1 :=
  view158.trans (piece158.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 158 1))

numeric_data_binding view159 : (data.drop 159).take 1 = (data152.drop 7).take 1

numeric_data_binding piece159 : (data152.drop 7).take 1 = ((originalEntries.drop 159).take 1).map NumericFunctionalBaseChecks.encode

theorem binding159 : (data.drop 159).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 159).take 1 :=
  view159.trans (piece159.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 159 1))

numeric_data_binding view160 : (data.drop 160).take 1 = (data160.drop 0).take 1

numeric_data_binding piece160 : (data160.drop 0).take 1 = ((originalEntries.drop 160).take 1).map NumericFunctionalBaseChecks.encode

theorem binding160 : (data.drop 160).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 160).take 1 :=
  view160.trans (piece160.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 160 1))

numeric_data_binding view161 : (data.drop 161).take 1 = (data160.drop 1).take 1

numeric_data_binding piece161 : (data160.drop 1).take 1 = ((originalEntries.drop 161).take 1).map NumericFunctionalBaseChecks.encode

theorem binding161 : (data.drop 161).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 161).take 1 :=
  view161.trans (piece161.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 161 1))

numeric_data_binding view162 : (data.drop 162).take 1 = (data160.drop 2).take 1

numeric_data_binding piece162 : (data160.drop 2).take 1 = ((originalEntries.drop 162).take 1).map NumericFunctionalBaseChecks.encode

theorem binding162 : (data.drop 162).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 162).take 1 :=
  view162.trans (piece162.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 162 1))

numeric_data_binding view163 : (data.drop 163).take 1 = (data160.drop 3).take 1

numeric_data_binding piece163 : (data160.drop 3).take 1 = ((originalEntries.drop 163).take 1).map NumericFunctionalBaseChecks.encode

theorem binding163 : (data.drop 163).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 163).take 1 :=
  view163.trans (piece163.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 163 1))

numeric_data_binding view164 : (data.drop 164).take 1 = (data160.drop 4).take 1

numeric_data_binding piece164 : (data160.drop 4).take 1 = ((originalEntries.drop 164).take 1).map NumericFunctionalBaseChecks.encode

theorem binding164 : (data.drop 164).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 164).take 1 :=
  view164.trans (piece164.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 164 1))

numeric_data_binding view165 : (data.drop 165).take 1 = (data160.drop 5).take 1

numeric_data_binding piece165 : (data160.drop 5).take 1 = ((originalEntries.drop 165).take 1).map NumericFunctionalBaseChecks.encode

theorem binding165 : (data.drop 165).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 165).take 1 :=
  view165.trans (piece165.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 165 1))

numeric_data_binding view166 : (data.drop 166).take 1 = (data160.drop 6).take 1

numeric_data_binding piece166 : (data160.drop 6).take 1 = ((originalEntries.drop 166).take 1).map NumericFunctionalBaseChecks.encode

theorem binding166 : (data.drop 166).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 166).take 1 :=
  view166.trans (piece166.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 166 1))

numeric_data_binding view167 : (data.drop 167).take 1 = (data160.drop 7).take 1

numeric_data_binding piece167 : (data160.drop 7).take 1 = ((originalEntries.drop 167).take 1).map NumericFunctionalBaseChecks.encode

theorem binding167 : (data.drop 167).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 167).take 1 :=
  view167.trans (piece167.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 167 1))

numeric_data_binding view168 : (data.drop 168).take 1 = (data168.drop 0).take 1

numeric_data_binding piece168 : (data168.drop 0).take 1 = ((originalEntries.drop 168).take 1).map NumericFunctionalBaseChecks.encode

theorem binding168 : (data.drop 168).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 168).take 1 :=
  view168.trans (piece168.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 168 1))

numeric_data_binding view169 : (data.drop 169).take 1 = (data168.drop 1).take 1

numeric_data_binding piece169 : (data168.drop 1).take 1 = ((originalEntries.drop 169).take 1).map NumericFunctionalBaseChecks.encode

theorem binding169 : (data.drop 169).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 169).take 1 :=
  view169.trans (piece169.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 169 1))

numeric_data_binding view170 : (data.drop 170).take 1 = (data168.drop 2).take 1

numeric_data_binding piece170 : (data168.drop 2).take 1 = ((originalEntries.drop 170).take 1).map NumericFunctionalBaseChecks.encode

theorem binding170 : (data.drop 170).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 170).take 1 :=
  view170.trans (piece170.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 170 1))

numeric_data_binding view171 : (data.drop 171).take 1 = (data168.drop 3).take 1

numeric_data_binding piece171 : (data168.drop 3).take 1 = ((originalEntries.drop 171).take 1).map NumericFunctionalBaseChecks.encode

theorem binding171 : (data.drop 171).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 171).take 1 :=
  view171.trans (piece171.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 171 1))

numeric_data_binding view172 : (data.drop 172).take 1 = (data168.drop 4).take 1

numeric_data_binding piece172 : (data168.drop 4).take 1 = ((originalEntries.drop 172).take 1).map NumericFunctionalBaseChecks.encode

theorem binding172 : (data.drop 172).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 172).take 1 :=
  view172.trans (piece172.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 172 1))

numeric_data_binding view173 : (data.drop 173).take 1 = (data168.drop 5).take 1

numeric_data_binding piece173 : (data168.drop 5).take 1 = ((originalEntries.drop 173).take 1).map NumericFunctionalBaseChecks.encode

theorem binding173 : (data.drop 173).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 173).take 1 :=
  view173.trans (piece173.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 173 1))

numeric_data_binding view174 : (data.drop 174).take 1 = (data168.drop 6).take 1

numeric_data_binding piece174 : (data168.drop 6).take 1 = ((originalEntries.drop 174).take 1).map NumericFunctionalBaseChecks.encode

theorem binding174 : (data.drop 174).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 174).take 1 :=
  view174.trans (piece174.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 174 1))

numeric_data_binding view175 : (data.drop 175).take 1 = (data168.drop 7).take 1

numeric_data_binding piece175 : (data168.drop 7).take 1 = ((originalEntries.drop 175).take 1).map NumericFunctionalBaseChecks.encode

theorem binding175 : (data.drop 175).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 175).take 1 :=
  view175.trans (piece175.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 175 1))

numeric_data_binding view176 : (data.drop 176).take 1 = (data176.drop 0).take 1

numeric_data_binding piece176 : (data176.drop 0).take 1 = ((originalEntries.drop 176).take 1).map NumericFunctionalBaseChecks.encode

theorem binding176 : (data.drop 176).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 176).take 1 :=
  view176.trans (piece176.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 176 1))

numeric_data_binding view177 : (data.drop 177).take 1 = (data176.drop 1).take 1

numeric_data_binding piece177 : (data176.drop 1).take 1 = ((originalEntries.drop 177).take 1).map NumericFunctionalBaseChecks.encode

theorem binding177 : (data.drop 177).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 177).take 1 :=
  view177.trans (piece177.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 177 1))

numeric_data_binding view178 : (data.drop 178).take 1 = (data176.drop 2).take 1

numeric_data_binding piece178 : (data176.drop 2).take 1 = ((originalEntries.drop 178).take 1).map NumericFunctionalBaseChecks.encode

theorem binding178 : (data.drop 178).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 178).take 1 :=
  view178.trans (piece178.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 178 1))

numeric_data_binding view179 : (data.drop 179).take 1 = (data176.drop 3).take 1

numeric_data_binding piece179 : (data176.drop 3).take 1 = ((originalEntries.drop 179).take 1).map NumericFunctionalBaseChecks.encode

theorem binding179 : (data.drop 179).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 179).take 1 :=
  view179.trans (piece179.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 179 1))

numeric_data_binding view180 : (data.drop 180).take 1 = (data176.drop 4).take 1

numeric_data_binding piece180 : (data176.drop 4).take 1 = ((originalEntries.drop 180).take 1).map NumericFunctionalBaseChecks.encode

theorem binding180 : (data.drop 180).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 180).take 1 :=
  view180.trans (piece180.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 180 1))

numeric_data_binding view181 : (data.drop 181).take 1 = (data176.drop 5).take 1

numeric_data_binding piece181 : (data176.drop 5).take 1 = ((originalEntries.drop 181).take 1).map NumericFunctionalBaseChecks.encode

theorem binding181 : (data.drop 181).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 181).take 1 :=
  view181.trans (piece181.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 181 1))

numeric_data_binding view182 : (data.drop 182).take 1 = (data176.drop 6).take 1

numeric_data_binding piece182 : (data176.drop 6).take 1 = ((originalEntries.drop 182).take 1).map NumericFunctionalBaseChecks.encode

theorem binding182 : (data.drop 182).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 182).take 1 :=
  view182.trans (piece182.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 182 1))

numeric_data_binding view183 : (data.drop 183).take 1 = (data176.drop 7).take 1

numeric_data_binding piece183 : (data176.drop 7).take 1 = ((originalEntries.drop 183).take 1).map NumericFunctionalBaseChecks.encode

theorem binding183 : (data.drop 183).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 183).take 1 :=
  view183.trans (piece183.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 183 1))

numeric_data_binding view184 : (data.drop 184).take 1 = (data184.drop 0).take 1

numeric_data_binding piece184 : (data184.drop 0).take 1 = ((originalEntries.drop 184).take 1).map NumericFunctionalBaseChecks.encode

theorem binding184 : (data.drop 184).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 184).take 1 :=
  view184.trans (piece184.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 184 1))

numeric_data_binding view185 : (data.drop 185).take 1 = (data184.drop 1).take 1

numeric_data_binding piece185 : (data184.drop 1).take 1 = ((originalEntries.drop 185).take 1).map NumericFunctionalBaseChecks.encode

theorem binding185 : (data.drop 185).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 185).take 1 :=
  view185.trans (piece185.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 185 1))

numeric_data_binding view186 : (data.drop 186).take 1 = (data184.drop 2).take 1

numeric_data_binding piece186 : (data184.drop 2).take 1 = ((originalEntries.drop 186).take 1).map NumericFunctionalBaseChecks.encode

theorem binding186 : (data.drop 186).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 186).take 1 :=
  view186.trans (piece186.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 186 1))

numeric_data_binding view187 : (data.drop 187).take 1 = (data184.drop 3).take 1

numeric_data_binding piece187 : (data184.drop 3).take 1 = ((originalEntries.drop 187).take 1).map NumericFunctionalBaseChecks.encode

theorem binding187 : (data.drop 187).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 187).take 1 :=
  view187.trans (piece187.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 187 1))

numeric_data_binding view188 : (data.drop 188).take 1 = (data184.drop 4).take 1

numeric_data_binding piece188 : (data184.drop 4).take 1 = ((originalEntries.drop 188).take 1).map NumericFunctionalBaseChecks.encode

theorem binding188 : (data.drop 188).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 188).take 1 :=
  view188.trans (piece188.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 188 1))

numeric_data_binding view189 : (data.drop 189).take 1 = (data184.drop 5).take 1

numeric_data_binding piece189 : (data184.drop 5).take 1 = ((originalEntries.drop 189).take 1).map NumericFunctionalBaseChecks.encode

theorem binding189 : (data.drop 189).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 189).take 1 :=
  view189.trans (piece189.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 189 1))

numeric_data_binding view190 : (data.drop 190).take 1 = (data184.drop 6).take 1

numeric_data_binding piece190 : (data184.drop 6).take 1 = ((originalEntries.drop 190).take 1).map NumericFunctionalBaseChecks.encode

theorem binding190 : (data.drop 190).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 190).take 1 :=
  view190.trans (piece190.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 190 1))

numeric_data_binding view191 : (data.drop 191).take 1 = (data184.drop 7).take 1

numeric_data_binding piece191 : (data184.drop 7).take 1 = ((originalEntries.drop 191).take 1).map NumericFunctionalBaseChecks.encode

theorem binding191 : (data.drop 191).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 191).take 1 :=
  view191.trans (piece191.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 191 1))

numeric_data_binding view192 : (data.drop 192).take 1 = (data192.drop 0).take 1

numeric_data_binding piece192 : (data192.drop 0).take 1 = ((originalEntries.drop 192).take 1).map NumericFunctionalBaseChecks.encode

theorem binding192 : (data.drop 192).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 192).take 1 :=
  view192.trans (piece192.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 192 1))

numeric_data_binding view193 : (data.drop 193).take 1 = (data192.drop 1).take 1

numeric_data_binding piece193 : (data192.drop 1).take 1 = ((originalEntries.drop 193).take 1).map NumericFunctionalBaseChecks.encode

theorem binding193 : (data.drop 193).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 193).take 1 :=
  view193.trans (piece193.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 193 1))

numeric_data_binding view194 : (data.drop 194).take 1 = (data192.drop 2).take 1

numeric_data_binding piece194 : (data192.drop 2).take 1 = ((originalEntries.drop 194).take 1).map NumericFunctionalBaseChecks.encode

theorem binding194 : (data.drop 194).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 194).take 1 :=
  view194.trans (piece194.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 194 1))

numeric_data_binding view195 : (data.drop 195).take 1 = (data192.drop 3).take 1

numeric_data_binding piece195 : (data192.drop 3).take 1 = ((originalEntries.drop 195).take 1).map NumericFunctionalBaseChecks.encode

theorem binding195 : (data.drop 195).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 195).take 1 :=
  view195.trans (piece195.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 195 1))

numeric_data_binding view196 : (data.drop 196).take 1 = (data192.drop 4).take 1

numeric_data_binding piece196 : (data192.drop 4).take 1 = ((originalEntries.drop 196).take 1).map NumericFunctionalBaseChecks.encode

theorem binding196 : (data.drop 196).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 196).take 1 :=
  view196.trans (piece196.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 196 1))

numeric_data_binding view197 : (data.drop 197).take 1 = (data192.drop 5).take 1

numeric_data_binding piece197 : (data192.drop 5).take 1 = ((originalEntries.drop 197).take 1).map NumericFunctionalBaseChecks.encode

theorem binding197 : (data.drop 197).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 197).take 1 :=
  view197.trans (piece197.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 197 1))

numeric_data_binding view198 : (data.drop 198).take 1 = (data192.drop 6).take 1

numeric_data_binding piece198 : (data192.drop 6).take 1 = ((originalEntries.drop 198).take 1).map NumericFunctionalBaseChecks.encode

theorem binding198 : (data.drop 198).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 198).take 1 :=
  view198.trans (piece198.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 198 1))

numeric_data_binding view199 : (data.drop 199).take 1 = (data192.drop 7).take 1

numeric_data_binding piece199 : (data192.drop 7).take 1 = ((originalEntries.drop 199).take 1).map NumericFunctionalBaseChecks.encode

theorem binding199 : (data.drop 199).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 199).take 1 :=
  view199.trans (piece199.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 199 1))

numeric_data_binding view200 : (data.drop 200).take 1 = (data200.drop 0).take 1

numeric_data_binding piece200 : (data200.drop 0).take 1 = ((originalEntries.drop 200).take 1).map NumericFunctionalBaseChecks.encode

theorem binding200 : (data.drop 200).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 200).take 1 :=
  view200.trans (piece200.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 200 1))

numeric_data_binding view201 : (data.drop 201).take 1 = (data200.drop 1).take 1

numeric_data_binding piece201 : (data200.drop 1).take 1 = ((originalEntries.drop 201).take 1).map NumericFunctionalBaseChecks.encode

theorem binding201 : (data.drop 201).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 201).take 1 :=
  view201.trans (piece201.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 201 1))

numeric_data_binding view202 : (data.drop 202).take 1 = (data200.drop 2).take 1

numeric_data_binding piece202 : (data200.drop 2).take 1 = ((originalEntries.drop 202).take 1).map NumericFunctionalBaseChecks.encode

theorem binding202 : (data.drop 202).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 202).take 1 :=
  view202.trans (piece202.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 202 1))

numeric_data_binding view203 : (data.drop 203).take 1 = (data200.drop 3).take 1

numeric_data_binding piece203 : (data200.drop 3).take 1 = ((originalEntries.drop 203).take 1).map NumericFunctionalBaseChecks.encode

theorem binding203 : (data.drop 203).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 203).take 1 :=
  view203.trans (piece203.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 203 1))

numeric_data_binding view204 : (data.drop 204).take 1 = (data200.drop 4).take 1

numeric_data_binding piece204 : (data200.drop 4).take 1 = ((originalEntries.drop 204).take 1).map NumericFunctionalBaseChecks.encode

theorem binding204 : (data.drop 204).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 204).take 1 :=
  view204.trans (piece204.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 204 1))

numeric_data_binding view205 : (data.drop 205).take 1 = (data200.drop 5).take 1

numeric_data_binding piece205 : (data200.drop 5).take 1 = ((originalEntries.drop 205).take 1).map NumericFunctionalBaseChecks.encode

theorem binding205 : (data.drop 205).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 205).take 1 :=
  view205.trans (piece205.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 205 1))

numeric_data_binding view206 : (data.drop 206).take 1 = (data200.drop 6).take 1

numeric_data_binding piece206 : (data200.drop 6).take 1 = ((originalEntries.drop 206).take 1).map NumericFunctionalBaseChecks.encode

theorem binding206 : (data.drop 206).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 206).take 1 :=
  view206.trans (piece206.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 206 1))

numeric_data_binding view207 : (data.drop 207).take 1 = (data200.drop 7).take 1

numeric_data_binding piece207 : (data200.drop 7).take 1 = ((originalEntries.drop 207).take 1).map NumericFunctionalBaseChecks.encode

theorem binding207 : (data.drop 207).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 207).take 1 :=
  view207.trans (piece207.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 207 1))

numeric_data_binding view208 : (data.drop 208).take 1 = (data208.drop 0).take 1

numeric_data_binding piece208 : (data208.drop 0).take 1 = ((originalEntries.drop 208).take 1).map NumericFunctionalBaseChecks.encode

theorem binding208 : (data.drop 208).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 208).take 1 :=
  view208.trans (piece208.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 208 1))

numeric_data_binding view209 : (data.drop 209).take 1 = (data208.drop 1).take 1

numeric_data_binding piece209 : (data208.drop 1).take 1 = ((originalEntries.drop 209).take 1).map NumericFunctionalBaseChecks.encode

theorem binding209 : (data.drop 209).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 209).take 1 :=
  view209.trans (piece209.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 209 1))

numeric_data_binding view210 : (data.drop 210).take 1 = (data208.drop 2).take 1

numeric_data_binding piece210 : (data208.drop 2).take 1 = ((originalEntries.drop 210).take 1).map NumericFunctionalBaseChecks.encode

theorem binding210 : (data.drop 210).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 210).take 1 :=
  view210.trans (piece210.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 210 1))

numeric_data_binding view211 : (data.drop 211).take 1 = (data208.drop 3).take 1

numeric_data_binding piece211 : (data208.drop 3).take 1 = ((originalEntries.drop 211).take 1).map NumericFunctionalBaseChecks.encode

theorem binding211 : (data.drop 211).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 211).take 1 :=
  view211.trans (piece211.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 211 1))

numeric_data_binding view212 : (data.drop 212).take 1 = (data208.drop 4).take 1

numeric_data_binding piece212 : (data208.drop 4).take 1 = ((originalEntries.drop 212).take 1).map NumericFunctionalBaseChecks.encode

theorem binding212 : (data.drop 212).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 212).take 1 :=
  view212.trans (piece212.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 212 1))

numeric_data_binding view213 : (data.drop 213).take 1 = (data208.drop 5).take 1

numeric_data_binding piece213 : (data208.drop 5).take 1 = ((originalEntries.drop 213).take 1).map NumericFunctionalBaseChecks.encode

theorem binding213 : (data.drop 213).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 213).take 1 :=
  view213.trans (piece213.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 213 1))

numeric_data_binding view214 : (data.drop 214).take 1 = (data208.drop 6).take 1

numeric_data_binding piece214 : (data208.drop 6).take 1 = ((originalEntries.drop 214).take 1).map NumericFunctionalBaseChecks.encode

theorem binding214 : (data.drop 214).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 214).take 1 :=
  view214.trans (piece214.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 214 1))

theorem sourceNode1_2 : (data.drop 1).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 1).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 1 1 1 binding1 binding2

theorem sourceNode0_3 : (data.drop 0).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 1 2 binding0 sourceNode1_2

theorem sourceNode4_2 : (data.drop 4).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 4).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 4 1 1 binding4 binding5

theorem sourceNode3_3 : (data.drop 3).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 3).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 3 1 2 binding3 sourceNode4_2

theorem sourceNode0_6 : (data.drop 0).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 3 3 sourceNode0_3 sourceNode3_3

theorem sourceNode7_2 : (data.drop 7).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 7).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 7 1 1 binding7 binding8

theorem sourceNode6_3 : (data.drop 6).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 6).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 6 1 2 binding6 sourceNode7_2

theorem sourceNode9_2 : (data.drop 9).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 9).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 9 1 1 binding9 binding10

theorem sourceNode11_2 : (data.drop 11).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 11).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 11 1 1 binding11 binding12

theorem sourceNode9_4 : (data.drop 9).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 9).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 9 2 2 sourceNode9_2 sourceNode11_2

theorem sourceNode6_7 : (data.drop 6).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 6).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 6 3 4 sourceNode6_3 sourceNode9_4

theorem sourceNode0_13 : (data.drop 0).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 6 7 sourceNode0_6 sourceNode6_7

theorem sourceNode14_2 : (data.drop 14).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 14).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 14 1 1 binding14 binding15

theorem sourceNode13_3 : (data.drop 13).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 13).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 13 1 2 binding13 sourceNode14_2

theorem sourceNode17_2 : (data.drop 17).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 17).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 17 1 1 binding17 binding18

theorem sourceNode16_3 : (data.drop 16).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 16 1 2 binding16 sourceNode17_2

theorem sourceNode13_6 : (data.drop 13).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 13).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 13 3 3 sourceNode13_3 sourceNode16_3

theorem sourceNode20_2 : (data.drop 20).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 20).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 20 1 1 binding20 binding21

theorem sourceNode19_3 : (data.drop 19).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 19).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 19 1 2 binding19 sourceNode20_2

theorem sourceNode22_2 : (data.drop 22).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 22 1 1 binding22 binding23

theorem sourceNode24_2 : (data.drop 24).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 24 1 1 binding24 binding25

theorem sourceNode22_4 : (data.drop 22).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 22 2 2 sourceNode22_2 sourceNode24_2

theorem sourceNode19_7 : (data.drop 19).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 19).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 19 3 4 sourceNode19_3 sourceNode22_4

theorem sourceNode13_13 : (data.drop 13).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 13).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 13 6 7 sourceNode13_6 sourceNode19_7

theorem sourceNode0_26 : (data.drop 0).take 26 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 26 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 13 13 sourceNode0_13 sourceNode13_13

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

theorem sourceNode33_2 : (data.drop 33).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 33).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 33 1 1 binding33 binding34

theorem sourceNode32_3 : (data.drop 32).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 1 2 binding32 sourceNode33_2

theorem sourceNode35_2 : (data.drop 35).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 35).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 35 1 1 binding35 binding36

theorem sourceNode37_2 : (data.drop 37).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 37).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 37 1 1 binding37 binding38

theorem sourceNode35_4 : (data.drop 35).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 35).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 35 2 2 sourceNode35_2 sourceNode37_2

theorem sourceNode32_7 : (data.drop 32).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 3 4 sourceNode32_3 sourceNode35_4

theorem sourceNode26_13 : (data.drop 26).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 26).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 26 6 7 sourceNode26_6 sourceNode32_7

theorem sourceNode40_2 : (data.drop 40).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 40).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 40 1 1 binding40 binding41

theorem sourceNode39_3 : (data.drop 39).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 39).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 39 1 2 binding39 sourceNode40_2

theorem sourceNode42_2 : (data.drop 42).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 42).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 42 1 1 binding42 binding43

theorem sourceNode44_2 : (data.drop 44).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 44 1 1 binding44 binding45

theorem sourceNode42_4 : (data.drop 42).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 42).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 42 2 2 sourceNode42_2 sourceNode44_2

theorem sourceNode39_7 : (data.drop 39).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 39).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 39 3 4 sourceNode39_3 sourceNode42_4

theorem sourceNode47_2 : (data.drop 47).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 47).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 47 1 1 binding47 binding48

theorem sourceNode46_3 : (data.drop 46).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 46).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 46 1 2 binding46 sourceNode47_2

theorem sourceNode49_2 : (data.drop 49).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 49).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 49 1 1 binding49 binding50

theorem sourceNode51_2 : (data.drop 51).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 51).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 51 1 1 binding51 binding52

theorem sourceNode49_4 : (data.drop 49).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 49).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 49 2 2 sourceNode49_2 sourceNode51_2

theorem sourceNode46_7 : (data.drop 46).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 46).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 46 3 4 sourceNode46_3 sourceNode49_4

theorem sourceNode39_14 : (data.drop 39).take 14 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 39).take 14 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 39 7 7 sourceNode39_7 sourceNode46_7

theorem sourceNode26_27 : (data.drop 26).take 27 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 26).take 27 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 26 13 14 sourceNode26_13 sourceNode39_14

theorem sourceNode0_53 : (data.drop 0).take 53 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 53 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 26 27 sourceNode0_26 sourceNode26_27

theorem sourceNode54_2 : (data.drop 54).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 54).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 54 1 1 binding54 binding55

theorem sourceNode53_3 : (data.drop 53).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 53).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 53 1 2 binding53 sourceNode54_2

theorem sourceNode57_2 : (data.drop 57).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 57).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 57 1 1 binding57 binding58

theorem sourceNode56_3 : (data.drop 56).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 56).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 56 1 2 binding56 sourceNode57_2

theorem sourceNode53_6 : (data.drop 53).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 53).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 53 3 3 sourceNode53_3 sourceNode56_3

theorem sourceNode60_2 : (data.drop 60).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 60).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 60 1 1 binding60 binding61

theorem sourceNode59_3 : (data.drop 59).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 59).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 59 1 2 binding59 sourceNode60_2

theorem sourceNode62_2 : (data.drop 62).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 62).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 62 1 1 binding62 binding63

theorem sourceNode64_2 : (data.drop 64).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 64 1 1 binding64 binding65

theorem sourceNode62_4 : (data.drop 62).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 62).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 62 2 2 sourceNode62_2 sourceNode64_2

theorem sourceNode59_7 : (data.drop 59).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 59).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 59 3 4 sourceNode59_3 sourceNode62_4

theorem sourceNode53_13 : (data.drop 53).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 53).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 53 6 7 sourceNode53_6 sourceNode59_7

theorem sourceNode67_2 : (data.drop 67).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 67).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 67 1 1 binding67 binding68

theorem sourceNode66_3 : (data.drop 66).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 66).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 66 1 2 binding66 sourceNode67_2

theorem sourceNode69_2 : (data.drop 69).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 69).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 69 1 1 binding69 binding70

theorem sourceNode71_2 : (data.drop 71).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 71).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 71 1 1 binding71 binding72

theorem sourceNode69_4 : (data.drop 69).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 69).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 69 2 2 sourceNode69_2 sourceNode71_2

theorem sourceNode66_7 : (data.drop 66).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 66).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 66 3 4 sourceNode66_3 sourceNode69_4

theorem sourceNode74_2 : (data.drop 74).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 74).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 74 1 1 binding74 binding75

theorem sourceNode73_3 : (data.drop 73).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 73).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 73 1 2 binding73 sourceNode74_2

theorem sourceNode76_2 : (data.drop 76).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 76).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 76 1 1 binding76 binding77

theorem sourceNode78_2 : (data.drop 78).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 78).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 78 1 1 binding78 binding79

theorem sourceNode76_4 : (data.drop 76).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 76).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 76 2 2 sourceNode76_2 sourceNode78_2

theorem sourceNode73_7 : (data.drop 73).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 73).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 73 3 4 sourceNode73_3 sourceNode76_4

theorem sourceNode66_14 : (data.drop 66).take 14 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 66).take 14 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 66 7 7 sourceNode66_7 sourceNode73_7

theorem sourceNode53_27 : (data.drop 53).take 27 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 53).take 27 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 53 13 14 sourceNode53_13 sourceNode66_14

theorem sourceNode81_2 : (data.drop 81).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 81).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 81 1 1 binding81 binding82

theorem sourceNode80_3 : (data.drop 80).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 80 1 2 binding80 sourceNode81_2

theorem sourceNode84_2 : (data.drop 84).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 84).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 84 1 1 binding84 binding85

theorem sourceNode83_3 : (data.drop 83).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 83).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 83 1 2 binding83 sourceNode84_2

theorem sourceNode80_6 : (data.drop 80).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 80 3 3 sourceNode80_3 sourceNode83_3

theorem sourceNode87_2 : (data.drop 87).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 87).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 87 1 1 binding87 binding88

theorem sourceNode86_3 : (data.drop 86).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 86).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 86 1 2 binding86 sourceNode87_2

theorem sourceNode89_2 : (data.drop 89).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 89).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 89 1 1 binding89 binding90

theorem sourceNode91_2 : (data.drop 91).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 91).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 91 1 1 binding91 binding92

theorem sourceNode89_4 : (data.drop 89).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 89).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 89 2 2 sourceNode89_2 sourceNode91_2

theorem sourceNode86_7 : (data.drop 86).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 86).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 86 3 4 sourceNode86_3 sourceNode89_4

theorem sourceNode80_13 : (data.drop 80).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 80 6 7 sourceNode80_6 sourceNode86_7

theorem sourceNode94_2 : (data.drop 94).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 94).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 94 1 1 binding94 binding95

theorem sourceNode93_3 : (data.drop 93).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 93).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 93 1 2 binding93 sourceNode94_2

theorem sourceNode96_2 : (data.drop 96).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 96).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 96 1 1 binding96 binding97

theorem sourceNode98_2 : (data.drop 98).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 98).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 98 1 1 binding98 binding99

theorem sourceNode96_4 : (data.drop 96).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 96).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 96 2 2 sourceNode96_2 sourceNode98_2

theorem sourceNode93_7 : (data.drop 93).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 93).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 93 3 4 sourceNode93_3 sourceNode96_4

theorem sourceNode101_2 : (data.drop 101).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 101).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 101 1 1 binding101 binding102

theorem sourceNode100_3 : (data.drop 100).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 100).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 100 1 2 binding100 sourceNode101_2

theorem sourceNode103_2 : (data.drop 103).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 103).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 103 1 1 binding103 binding104

theorem sourceNode105_2 : (data.drop 105).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 105).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 105 1 1 binding105 binding106

theorem sourceNode103_4 : (data.drop 103).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 103).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 103 2 2 sourceNode103_2 sourceNode105_2

theorem sourceNode100_7 : (data.drop 100).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 100).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 100 3 4 sourceNode100_3 sourceNode103_4

theorem sourceNode93_14 : (data.drop 93).take 14 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 93).take 14 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 93 7 7 sourceNode93_7 sourceNode100_7

theorem sourceNode80_27 : (data.drop 80).take 27 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 27 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 80 13 14 sourceNode80_13 sourceNode93_14

theorem sourceNode53_54 : (data.drop 53).take 54 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 53).take 54 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 53 27 27 sourceNode53_27 sourceNode80_27

theorem sourceNode0_107 : (data.drop 0).take 107 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 107 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 53 54 sourceNode0_53 sourceNode53_54

theorem sourceNode108_2 : (data.drop 108).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 108).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 108 1 1 binding108 binding109

theorem sourceNode107_3 : (data.drop 107).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 107).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 107 1 2 binding107 sourceNode108_2

theorem sourceNode111_2 : (data.drop 111).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 111).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 111 1 1 binding111 binding112

theorem sourceNode110_3 : (data.drop 110).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 110).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 110 1 2 binding110 sourceNode111_2

theorem sourceNode107_6 : (data.drop 107).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 107).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 107 3 3 sourceNode107_3 sourceNode110_3

theorem sourceNode114_2 : (data.drop 114).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 114).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 114 1 1 binding114 binding115

theorem sourceNode113_3 : (data.drop 113).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 113).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 113 1 2 binding113 sourceNode114_2

theorem sourceNode116_2 : (data.drop 116).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 116).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 116 1 1 binding116 binding117

theorem sourceNode118_2 : (data.drop 118).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 118).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 118 1 1 binding118 binding119

theorem sourceNode116_4 : (data.drop 116).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 116).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 116 2 2 sourceNode116_2 sourceNode118_2

theorem sourceNode113_7 : (data.drop 113).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 113).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 113 3 4 sourceNode113_3 sourceNode116_4

theorem sourceNode107_13 : (data.drop 107).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 107).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 107 6 7 sourceNode107_6 sourceNode113_7

theorem sourceNode121_2 : (data.drop 121).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 121).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 121 1 1 binding121 binding122

theorem sourceNode120_3 : (data.drop 120).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 120).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 120 1 2 binding120 sourceNode121_2

theorem sourceNode123_2 : (data.drop 123).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 123).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 123 1 1 binding123 binding124

theorem sourceNode125_2 : (data.drop 125).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 125).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 125 1 1 binding125 binding126

theorem sourceNode123_4 : (data.drop 123).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 123).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 123 2 2 sourceNode123_2 sourceNode125_2

theorem sourceNode120_7 : (data.drop 120).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 120).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 120 3 4 sourceNode120_3 sourceNode123_4

theorem sourceNode128_2 : (data.drop 128).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 128).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 128 1 1 binding128 binding129

theorem sourceNode127_3 : (data.drop 127).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 127).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 127 1 2 binding127 sourceNode128_2

theorem sourceNode130_2 : (data.drop 130).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 130).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 130 1 1 binding130 binding131

theorem sourceNode132_2 : (data.drop 132).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 132).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 132 1 1 binding132 binding133

theorem sourceNode130_4 : (data.drop 130).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 130).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 130 2 2 sourceNode130_2 sourceNode132_2

theorem sourceNode127_7 : (data.drop 127).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 127).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 127 3 4 sourceNode127_3 sourceNode130_4

theorem sourceNode120_14 : (data.drop 120).take 14 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 120).take 14 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 120 7 7 sourceNode120_7 sourceNode127_7

theorem sourceNode107_27 : (data.drop 107).take 27 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 107).take 27 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 107 13 14 sourceNode107_13 sourceNode120_14

theorem sourceNode135_2 : (data.drop 135).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 135).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 135 1 1 binding135 binding136

theorem sourceNode134_3 : (data.drop 134).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 134).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 134 1 2 binding134 sourceNode135_2

theorem sourceNode138_2 : (data.drop 138).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 138).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 138 1 1 binding138 binding139

theorem sourceNode137_3 : (data.drop 137).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 137).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 137 1 2 binding137 sourceNode138_2

theorem sourceNode134_6 : (data.drop 134).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 134).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 134 3 3 sourceNode134_3 sourceNode137_3

theorem sourceNode141_2 : (data.drop 141).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 141).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 141 1 1 binding141 binding142

theorem sourceNode140_3 : (data.drop 140).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 140).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 140 1 2 binding140 sourceNode141_2

theorem sourceNode143_2 : (data.drop 143).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 143).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 143 1 1 binding143 binding144

theorem sourceNode145_2 : (data.drop 145).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 145).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 145 1 1 binding145 binding146

theorem sourceNode143_4 : (data.drop 143).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 143).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 143 2 2 sourceNode143_2 sourceNode145_2

theorem sourceNode140_7 : (data.drop 140).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 140).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 140 3 4 sourceNode140_3 sourceNode143_4

theorem sourceNode134_13 : (data.drop 134).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 134).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 134 6 7 sourceNode134_6 sourceNode140_7

theorem sourceNode148_2 : (data.drop 148).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 148).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 148 1 1 binding148 binding149

theorem sourceNode147_3 : (data.drop 147).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 147).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 147 1 2 binding147 sourceNode148_2

theorem sourceNode150_2 : (data.drop 150).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 150).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 150 1 1 binding150 binding151

theorem sourceNode152_2 : (data.drop 152).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 152).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 152 1 1 binding152 binding153

theorem sourceNode150_4 : (data.drop 150).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 150).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 150 2 2 sourceNode150_2 sourceNode152_2

theorem sourceNode147_7 : (data.drop 147).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 147).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 147 3 4 sourceNode147_3 sourceNode150_4

theorem sourceNode155_2 : (data.drop 155).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 155).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 155 1 1 binding155 binding156

theorem sourceNode154_3 : (data.drop 154).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 154).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 154 1 2 binding154 sourceNode155_2

theorem sourceNode157_2 : (data.drop 157).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 157).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 157 1 1 binding157 binding158

theorem sourceNode159_2 : (data.drop 159).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 159).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 159 1 1 binding159 binding160

theorem sourceNode157_4 : (data.drop 157).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 157).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 157 2 2 sourceNode157_2 sourceNode159_2

theorem sourceNode154_7 : (data.drop 154).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 154).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 154 3 4 sourceNode154_3 sourceNode157_4

theorem sourceNode147_14 : (data.drop 147).take 14 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 147).take 14 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 147 7 7 sourceNode147_7 sourceNode154_7

theorem sourceNode134_27 : (data.drop 134).take 27 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 134).take 27 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 134 13 14 sourceNode134_13 sourceNode147_14

theorem sourceNode107_54 : (data.drop 107).take 54 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 107).take 54 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 107 27 27 sourceNode107_27 sourceNode134_27

theorem sourceNode162_2 : (data.drop 162).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 162).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 162 1 1 binding162 binding163

theorem sourceNode161_3 : (data.drop 161).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 161).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 161 1 2 binding161 sourceNode162_2

theorem sourceNode165_2 : (data.drop 165).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 165).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 165 1 1 binding165 binding166

theorem sourceNode164_3 : (data.drop 164).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 164).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 164 1 2 binding164 sourceNode165_2

theorem sourceNode161_6 : (data.drop 161).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 161).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 161 3 3 sourceNode161_3 sourceNode164_3

theorem sourceNode168_2 : (data.drop 168).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 168).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 168 1 1 binding168 binding169

theorem sourceNode167_3 : (data.drop 167).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 167).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 167 1 2 binding167 sourceNode168_2

theorem sourceNode170_2 : (data.drop 170).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 170).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 170 1 1 binding170 binding171

theorem sourceNode172_2 : (data.drop 172).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 172).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 172 1 1 binding172 binding173

theorem sourceNode170_4 : (data.drop 170).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 170).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 170 2 2 sourceNode170_2 sourceNode172_2

theorem sourceNode167_7 : (data.drop 167).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 167).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 167 3 4 sourceNode167_3 sourceNode170_4

theorem sourceNode161_13 : (data.drop 161).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 161).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 161 6 7 sourceNode161_6 sourceNode167_7

theorem sourceNode175_2 : (data.drop 175).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 175).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 175 1 1 binding175 binding176

theorem sourceNode174_3 : (data.drop 174).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 174).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 174 1 2 binding174 sourceNode175_2

theorem sourceNode177_2 : (data.drop 177).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 177).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 177 1 1 binding177 binding178

theorem sourceNode179_2 : (data.drop 179).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 179).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 179 1 1 binding179 binding180

theorem sourceNode177_4 : (data.drop 177).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 177).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 177 2 2 sourceNode177_2 sourceNode179_2

theorem sourceNode174_7 : (data.drop 174).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 174).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 174 3 4 sourceNode174_3 sourceNode177_4

theorem sourceNode182_2 : (data.drop 182).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 182).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 182 1 1 binding182 binding183

theorem sourceNode181_3 : (data.drop 181).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 181).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 181 1 2 binding181 sourceNode182_2

theorem sourceNode184_2 : (data.drop 184).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 184).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 184 1 1 binding184 binding185

theorem sourceNode186_2 : (data.drop 186).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 186).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 186 1 1 binding186 binding187

theorem sourceNode184_4 : (data.drop 184).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 184).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 184 2 2 sourceNode184_2 sourceNode186_2

theorem sourceNode181_7 : (data.drop 181).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 181).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 181 3 4 sourceNode181_3 sourceNode184_4

theorem sourceNode174_14 : (data.drop 174).take 14 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 174).take 14 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 174 7 7 sourceNode174_7 sourceNode181_7

theorem sourceNode161_27 : (data.drop 161).take 27 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 161).take 27 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 161 13 14 sourceNode161_13 sourceNode174_14

theorem sourceNode189_2 : (data.drop 189).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 189).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 189 1 1 binding189 binding190

theorem sourceNode188_3 : (data.drop 188).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 188).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 188 1 2 binding188 sourceNode189_2

theorem sourceNode192_2 : (data.drop 192).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 192).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 192 1 1 binding192 binding193

theorem sourceNode191_3 : (data.drop 191).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 191).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 191 1 2 binding191 sourceNode192_2

theorem sourceNode188_6 : (data.drop 188).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 188).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 188 3 3 sourceNode188_3 sourceNode191_3

theorem sourceNode195_2 : (data.drop 195).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 195).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 195 1 1 binding195 binding196

theorem sourceNode194_3 : (data.drop 194).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 194).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 194 1 2 binding194 sourceNode195_2

theorem sourceNode197_2 : (data.drop 197).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 197).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 197 1 1 binding197 binding198

theorem sourceNode199_2 : (data.drop 199).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 199).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 199 1 1 binding199 binding200

theorem sourceNode197_4 : (data.drop 197).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 197).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 197 2 2 sourceNode197_2 sourceNode199_2

theorem sourceNode194_7 : (data.drop 194).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 194).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 194 3 4 sourceNode194_3 sourceNode197_4

theorem sourceNode188_13 : (data.drop 188).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 188).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 188 6 7 sourceNode188_6 sourceNode194_7

theorem sourceNode202_2 : (data.drop 202).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 202).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 202 1 1 binding202 binding203

theorem sourceNode201_3 : (data.drop 201).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 201).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 201 1 2 binding201 sourceNode202_2

theorem sourceNode204_2 : (data.drop 204).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 204).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 204 1 1 binding204 binding205

theorem sourceNode206_2 : (data.drop 206).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 206).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 206 1 1 binding206 binding207

theorem sourceNode204_4 : (data.drop 204).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 204).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 204 2 2 sourceNode204_2 sourceNode206_2

theorem sourceNode201_7 : (data.drop 201).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 201).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 201 3 4 sourceNode201_3 sourceNode204_4

theorem sourceNode209_2 : (data.drop 209).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 209).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 209 1 1 binding209 binding210

theorem sourceNode208_3 : (data.drop 208).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 208).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 208 1 2 binding208 sourceNode209_2

theorem sourceNode211_2 : (data.drop 211).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 211).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 211 1 1 binding211 binding212

theorem sourceNode213_2 : (data.drop 213).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 213).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 213 1 1 binding213 binding214

theorem sourceNode211_4 : (data.drop 211).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 211).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 211 2 2 sourceNode211_2 sourceNode213_2

theorem sourceNode208_7 : (data.drop 208).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 208).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 208 3 4 sourceNode208_3 sourceNode211_4

theorem sourceNode201_14 : (data.drop 201).take 14 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 201).take 14 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 201 7 7 sourceNode201_7 sourceNode208_7

theorem sourceNode188_27 : (data.drop 188).take 27 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 188).take 27 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 188 13 14 sourceNode188_13 sourceNode201_14

theorem sourceNode161_54 : (data.drop 161).take 54 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 161).take 54 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 161 27 27 sourceNode161_27 sourceNode188_27

theorem sourceNode107_108 : (data.drop 107).take 108 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 107).take 108 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 107 54 54 sourceNode107_54 sourceNode161_54

theorem sourceNode0_215 : (data.drop 0).take 215 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 215 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 107 108 sourceNode0_107 sourceNode107_108

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 215
    (by decide +kernel) (by decide +kernel) sourceNode0_215

end Airbender.Compiler.LookupSourceChecks.BlakeGUncached
