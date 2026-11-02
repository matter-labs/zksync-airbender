import Airbender.Proofs.GKRProtocol.LookupSourceChecks.BigintCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.LookupSourceChecks.BigintCached
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

numeric_data_binding view215 : (data.drop 215).take 1 = (data208.drop 7).take 1

numeric_data_binding piece215 : (data208.drop 7).take 1 = ((originalEntries.drop 215).take 1).map NumericFunctionalBaseChecks.encode

theorem binding215 : (data.drop 215).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 215).take 1 :=
  view215.trans (piece215.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 215 1))

numeric_data_binding view216 : (data.drop 216).take 1 = (data216.drop 0).take 1

numeric_data_binding piece216 : (data216.drop 0).take 1 = ((originalEntries.drop 216).take 1).map NumericFunctionalBaseChecks.encode

theorem binding216 : (data.drop 216).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 216).take 1 :=
  view216.trans (piece216.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 216 1))

numeric_data_binding view217 : (data.drop 217).take 1 = (data216.drop 1).take 1

numeric_data_binding piece217 : (data216.drop 1).take 1 = ((originalEntries.drop 217).take 1).map NumericFunctionalBaseChecks.encode

theorem binding217 : (data.drop 217).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 217).take 1 :=
  view217.trans (piece217.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 217 1))

numeric_data_binding view218 : (data.drop 218).take 1 = (data216.drop 2).take 1

numeric_data_binding piece218 : (data216.drop 2).take 1 = ((originalEntries.drop 218).take 1).map NumericFunctionalBaseChecks.encode

theorem binding218 : (data.drop 218).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 218).take 1 :=
  view218.trans (piece218.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 218 1))

numeric_data_binding view219 : (data.drop 219).take 1 = (data216.drop 3).take 1

numeric_data_binding piece219 : (data216.drop 3).take 1 = ((originalEntries.drop 219).take 1).map NumericFunctionalBaseChecks.encode

theorem binding219 : (data.drop 219).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 219).take 1 :=
  view219.trans (piece219.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 219 1))

numeric_data_binding view220 : (data.drop 220).take 1 = (data216.drop 4).take 1

numeric_data_binding piece220 : (data216.drop 4).take 1 = ((originalEntries.drop 220).take 1).map NumericFunctionalBaseChecks.encode

theorem binding220 : (data.drop 220).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 220).take 1 :=
  view220.trans (piece220.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 220 1))

numeric_data_binding view221 : (data.drop 221).take 1 = (data216.drop 5).take 1

numeric_data_binding piece221 : (data216.drop 5).take 1 = ((originalEntries.drop 221).take 1).map NumericFunctionalBaseChecks.encode

theorem binding221 : (data.drop 221).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 221).take 1 :=
  view221.trans (piece221.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 221 1))

numeric_data_binding view222 : (data.drop 222).take 1 = (data216.drop 6).take 1

numeric_data_binding piece222 : (data216.drop 6).take 1 = ((originalEntries.drop 222).take 1).map NumericFunctionalBaseChecks.encode

theorem binding222 : (data.drop 222).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 222).take 1 :=
  view222.trans (piece222.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 222 1))

numeric_data_binding view223 : (data.drop 223).take 1 = (data216.drop 7).take 1

numeric_data_binding piece223 : (data216.drop 7).take 1 = ((originalEntries.drop 223).take 1).map NumericFunctionalBaseChecks.encode

theorem binding223 : (data.drop 223).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 223).take 1 :=
  view223.trans (piece223.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 223 1))

numeric_data_binding view224 : (data.drop 224).take 1 = (data224.drop 0).take 1

numeric_data_binding piece224 : (data224.drop 0).take 1 = ((originalEntries.drop 224).take 1).map NumericFunctionalBaseChecks.encode

theorem binding224 : (data.drop 224).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 224).take 1 :=
  view224.trans (piece224.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 224 1))

numeric_data_binding view225 : (data.drop 225).take 1 = (data224.drop 1).take 1

numeric_data_binding piece225 : (data224.drop 1).take 1 = ((originalEntries.drop 225).take 1).map NumericFunctionalBaseChecks.encode

theorem binding225 : (data.drop 225).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 225).take 1 :=
  view225.trans (piece225.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 225 1))

numeric_data_binding view226 : (data.drop 226).take 1 = (data224.drop 2).take 1

numeric_data_binding piece226 : (data224.drop 2).take 1 = ((originalEntries.drop 226).take 1).map NumericFunctionalBaseChecks.encode

theorem binding226 : (data.drop 226).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 226).take 1 :=
  view226.trans (piece226.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 226 1))

numeric_data_binding view227 : (data.drop 227).take 1 = (data224.drop 3).take 1

numeric_data_binding piece227 : (data224.drop 3).take 1 = ((originalEntries.drop 227).take 1).map NumericFunctionalBaseChecks.encode

theorem binding227 : (data.drop 227).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 227).take 1 :=
  view227.trans (piece227.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 227 1))

numeric_data_binding view228 : (data.drop 228).take 1 = (data224.drop 4).take 1

numeric_data_binding piece228 : (data224.drop 4).take 1 = ((originalEntries.drop 228).take 1).map NumericFunctionalBaseChecks.encode

theorem binding228 : (data.drop 228).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 228).take 1 :=
  view228.trans (piece228.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 228 1))

numeric_data_binding view229 : (data.drop 229).take 1 = (data224.drop 5).take 1

numeric_data_binding piece229 : (data224.drop 5).take 1 = ((originalEntries.drop 229).take 1).map NumericFunctionalBaseChecks.encode

theorem binding229 : (data.drop 229).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 229).take 1 :=
  view229.trans (piece229.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 229 1))

numeric_data_binding view230 : (data.drop 230).take 1 = (data224.drop 6).take 1

numeric_data_binding piece230 : (data224.drop 6).take 1 = ((originalEntries.drop 230).take 1).map NumericFunctionalBaseChecks.encode

theorem binding230 : (data.drop 230).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 230).take 1 :=
  view230.trans (piece230.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 230 1))

numeric_data_binding view231 : (data.drop 231).take 1 = (data224.drop 7).take 1

numeric_data_binding piece231 : (data224.drop 7).take 1 = ((originalEntries.drop 231).take 1).map NumericFunctionalBaseChecks.encode

theorem binding231 : (data.drop 231).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 231).take 1 :=
  view231.trans (piece231.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 231 1))

numeric_data_binding view232 : (data.drop 232).take 1 = (data232.drop 0).take 1

numeric_data_binding piece232 : (data232.drop 0).take 1 = ((originalEntries.drop 232).take 1).map NumericFunctionalBaseChecks.encode

theorem binding232 : (data.drop 232).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 232).take 1 :=
  view232.trans (piece232.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 232 1))

numeric_data_binding view233 : (data.drop 233).take 1 = (data232.drop 1).take 1

numeric_data_binding piece233 : (data232.drop 1).take 1 = ((originalEntries.drop 233).take 1).map NumericFunctionalBaseChecks.encode

theorem binding233 : (data.drop 233).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 233).take 1 :=
  view233.trans (piece233.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 233 1))

numeric_data_binding view234 : (data.drop 234).take 1 = (data232.drop 2).take 1

numeric_data_binding piece234 : (data232.drop 2).take 1 = ((originalEntries.drop 234).take 1).map NumericFunctionalBaseChecks.encode

theorem binding234 : (data.drop 234).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 234).take 1 :=
  view234.trans (piece234.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 234 1))

numeric_data_binding view235 : (data.drop 235).take 1 = (data232.drop 3).take 1

numeric_data_binding piece235 : (data232.drop 3).take 1 = ((originalEntries.drop 235).take 1).map NumericFunctionalBaseChecks.encode

theorem binding235 : (data.drop 235).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 235).take 1 :=
  view235.trans (piece235.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 235 1))

numeric_data_binding view236 : (data.drop 236).take 1 = (data232.drop 4).take 1

numeric_data_binding piece236 : (data232.drop 4).take 1 = ((originalEntries.drop 236).take 1).map NumericFunctionalBaseChecks.encode

theorem binding236 : (data.drop 236).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 236).take 1 :=
  view236.trans (piece236.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 236 1))

numeric_data_binding view237 : (data.drop 237).take 1 = (data232.drop 5).take 1

numeric_data_binding piece237 : (data232.drop 5).take 1 = ((originalEntries.drop 237).take 1).map NumericFunctionalBaseChecks.encode

theorem binding237 : (data.drop 237).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 237).take 1 :=
  view237.trans (piece237.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 237 1))

numeric_data_binding view238 : (data.drop 238).take 1 = (data232.drop 6).take 1

numeric_data_binding piece238 : (data232.drop 6).take 1 = ((originalEntries.drop 238).take 1).map NumericFunctionalBaseChecks.encode

theorem binding238 : (data.drop 238).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 238).take 1 :=
  view238.trans (piece238.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 238 1))

numeric_data_binding view239 : (data.drop 239).take 1 = (data232.drop 7).take 1

numeric_data_binding piece239 : (data232.drop 7).take 1 = ((originalEntries.drop 239).take 1).map NumericFunctionalBaseChecks.encode

theorem binding239 : (data.drop 239).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 239).take 1 :=
  view239.trans (piece239.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 239 1))

numeric_data_binding view240 : (data.drop 240).take 1 = (data240.drop 0).take 1

numeric_data_binding piece240 : (data240.drop 0).take 1 = ((originalEntries.drop 240).take 1).map NumericFunctionalBaseChecks.encode

theorem binding240 : (data.drop 240).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 240).take 1 :=
  view240.trans (piece240.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 240 1))

numeric_data_binding view241 : (data.drop 241).take 1 = (data240.drop 1).take 1

numeric_data_binding piece241 : (data240.drop 1).take 1 = ((originalEntries.drop 241).take 1).map NumericFunctionalBaseChecks.encode

theorem binding241 : (data.drop 241).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 241).take 1 :=
  view241.trans (piece241.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 241 1))

numeric_data_binding view242 : (data.drop 242).take 1 = (data240.drop 2).take 1

numeric_data_binding piece242 : (data240.drop 2).take 1 = ((originalEntries.drop 242).take 1).map NumericFunctionalBaseChecks.encode

theorem binding242 : (data.drop 242).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 242).take 1 :=
  view242.trans (piece242.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 242 1))

numeric_data_binding view243 : (data.drop 243).take 1 = (data240.drop 3).take 1

numeric_data_binding piece243 : (data240.drop 3).take 1 = ((originalEntries.drop 243).take 1).map NumericFunctionalBaseChecks.encode

theorem binding243 : (data.drop 243).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 243).take 1 :=
  view243.trans (piece243.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 243 1))

numeric_data_binding view244 : (data.drop 244).take 1 = (data240.drop 4).take 1

numeric_data_binding piece244 : (data240.drop 4).take 1 = ((originalEntries.drop 244).take 1).map NumericFunctionalBaseChecks.encode

theorem binding244 : (data.drop 244).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 244).take 1 :=
  view244.trans (piece244.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 244 1))

numeric_data_binding view245 : (data.drop 245).take 1 = (data240.drop 5).take 1

numeric_data_binding piece245 : (data240.drop 5).take 1 = ((originalEntries.drop 245).take 1).map NumericFunctionalBaseChecks.encode

theorem binding245 : (data.drop 245).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 245).take 1 :=
  view245.trans (piece245.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 245 1))

numeric_data_binding view246 : (data.drop 246).take 1 = (data240.drop 6).take 1

numeric_data_binding piece246 : (data240.drop 6).take 1 = ((originalEntries.drop 246).take 1).map NumericFunctionalBaseChecks.encode

theorem binding246 : (data.drop 246).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 246).take 1 :=
  view246.trans (piece246.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 246 1))

numeric_data_binding view247 : (data.drop 247).take 1 = (data240.drop 7).take 1

numeric_data_binding piece247 : (data240.drop 7).take 1 = ((originalEntries.drop 247).take 1).map NumericFunctionalBaseChecks.encode

theorem binding247 : (data.drop 247).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 247).take 1 :=
  view247.trans (piece247.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 247 1))

numeric_data_binding view248 : (data.drop 248).take 1 = (data248.drop 0).take 1

numeric_data_binding piece248 : (data248.drop 0).take 1 = ((originalEntries.drop 248).take 1).map NumericFunctionalBaseChecks.encode

theorem binding248 : (data.drop 248).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 248).take 1 :=
  view248.trans (piece248.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 248 1))

numeric_data_binding view249 : (data.drop 249).take 1 = (data248.drop 1).take 1

numeric_data_binding piece249 : (data248.drop 1).take 1 = ((originalEntries.drop 249).take 1).map NumericFunctionalBaseChecks.encode

theorem binding249 : (data.drop 249).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 249).take 1 :=
  view249.trans (piece249.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 249 1))

numeric_data_binding view250 : (data.drop 250).take 1 = (data248.drop 2).take 1

numeric_data_binding piece250 : (data248.drop 2).take 1 = ((originalEntries.drop 250).take 1).map NumericFunctionalBaseChecks.encode

theorem binding250 : (data.drop 250).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 250).take 1 :=
  view250.trans (piece250.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 250 1))

numeric_data_binding view251 : (data.drop 251).take 1 = (data248.drop 3).take 1

numeric_data_binding piece251 : (data248.drop 3).take 1 = ((originalEntries.drop 251).take 1).map NumericFunctionalBaseChecks.encode

theorem binding251 : (data.drop 251).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 251).take 1 :=
  view251.trans (piece251.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 251 1))

numeric_data_binding view252 : (data.drop 252).take 1 = (data248.drop 4).take 1

numeric_data_binding piece252 : (data248.drop 4).take 1 = ((originalEntries.drop 252).take 1).map NumericFunctionalBaseChecks.encode

theorem binding252 : (data.drop 252).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 252).take 1 :=
  view252.trans (piece252.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 252 1))

numeric_data_binding view253 : (data.drop 253).take 1 = (data248.drop 5).take 1

numeric_data_binding piece253 : (data248.drop 5).take 1 = ((originalEntries.drop 253).take 1).map NumericFunctionalBaseChecks.encode

theorem binding253 : (data.drop 253).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 253).take 1 :=
  view253.trans (piece253.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 253 1))

numeric_data_binding view254 : (data.drop 254).take 1 = (data248.drop 6).take 1

numeric_data_binding piece254 : (data248.drop 6).take 1 = ((originalEntries.drop 254).take 1).map NumericFunctionalBaseChecks.encode

theorem binding254 : (data.drop 254).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 254).take 1 :=
  view254.trans (piece254.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 254 1))

numeric_data_binding view255 : (data.drop 255).take 1 = (data248.drop 7).take 1

numeric_data_binding piece255 : (data248.drop 7).take 1 = ((originalEntries.drop 255).take 1).map NumericFunctionalBaseChecks.encode

theorem binding255 : (data.drop 255).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 255).take 1 :=
  view255.trans (piece255.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 255 1))

numeric_data_binding view256 : (data.drop 256).take 1 = (data256.drop 0).take 1

numeric_data_binding piece256 : (data256.drop 0).take 1 = ((originalEntries.drop 256).take 1).map NumericFunctionalBaseChecks.encode

theorem binding256 : (data.drop 256).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 256).take 1 :=
  view256.trans (piece256.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 256 1))

numeric_data_binding view257 : (data.drop 257).take 1 = (data256.drop 1).take 1

numeric_data_binding piece257 : (data256.drop 1).take 1 = ((originalEntries.drop 257).take 1).map NumericFunctionalBaseChecks.encode

theorem binding257 : (data.drop 257).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 257).take 1 :=
  view257.trans (piece257.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 257 1))

numeric_data_binding view258 : (data.drop 258).take 1 = (data256.drop 2).take 1

numeric_data_binding piece258 : (data256.drop 2).take 1 = ((originalEntries.drop 258).take 1).map NumericFunctionalBaseChecks.encode

theorem binding258 : (data.drop 258).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 258).take 1 :=
  view258.trans (piece258.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 258 1))

numeric_data_binding view259 : (data.drop 259).take 1 = (data256.drop 3).take 1

numeric_data_binding piece259 : (data256.drop 3).take 1 = ((originalEntries.drop 259).take 1).map NumericFunctionalBaseChecks.encode

theorem binding259 : (data.drop 259).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 259).take 1 :=
  view259.trans (piece259.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 259 1))

numeric_data_binding view260 : (data.drop 260).take 1 = (data256.drop 4).take 1

numeric_data_binding piece260 : (data256.drop 4).take 1 = ((originalEntries.drop 260).take 1).map NumericFunctionalBaseChecks.encode

theorem binding260 : (data.drop 260).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 260).take 1 :=
  view260.trans (piece260.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 260 1))

numeric_data_binding view261 : (data.drop 261).take 1 = (data256.drop 5).take 1

numeric_data_binding piece261 : (data256.drop 5).take 1 = ((originalEntries.drop 261).take 1).map NumericFunctionalBaseChecks.encode

theorem binding261 : (data.drop 261).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 261).take 1 :=
  view261.trans (piece261.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 261 1))

numeric_data_binding view262 : (data.drop 262).take 1 = (data256.drop 6).take 1

numeric_data_binding piece262 : (data256.drop 6).take 1 = ((originalEntries.drop 262).take 1).map NumericFunctionalBaseChecks.encode

theorem binding262 : (data.drop 262).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 262).take 1 :=
  view262.trans (piece262.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 262 1))

numeric_data_binding view263 : (data.drop 263).take 1 = (data256.drop 7).take 1

numeric_data_binding piece263 : (data256.drop 7).take 1 = ((originalEntries.drop 263).take 1).map NumericFunctionalBaseChecks.encode

theorem binding263 : (data.drop 263).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 263).take 1 :=
  view263.trans (piece263.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 263 1))

numeric_data_binding view264 : (data.drop 264).take 1 = (data264.drop 0).take 1

numeric_data_binding piece264 : (data264.drop 0).take 1 = ((originalEntries.drop 264).take 1).map NumericFunctionalBaseChecks.encode

theorem binding264 : (data.drop 264).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 264).take 1 :=
  view264.trans (piece264.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 264 1))

numeric_data_binding view265 : (data.drop 265).take 1 = (data264.drop 1).take 1

numeric_data_binding piece265 : (data264.drop 1).take 1 = ((originalEntries.drop 265).take 1).map NumericFunctionalBaseChecks.encode

theorem binding265 : (data.drop 265).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 265).take 1 :=
  view265.trans (piece265.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 265 1))

numeric_data_binding view266 : (data.drop 266).take 1 = (data264.drop 2).take 1

numeric_data_binding piece266 : (data264.drop 2).take 1 = ((originalEntries.drop 266).take 1).map NumericFunctionalBaseChecks.encode

theorem binding266 : (data.drop 266).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 266).take 1 :=
  view266.trans (piece266.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 266 1))

numeric_data_binding view267 : (data.drop 267).take 1 = (data264.drop 3).take 1

numeric_data_binding piece267 : (data264.drop 3).take 1 = ((originalEntries.drop 267).take 1).map NumericFunctionalBaseChecks.encode

theorem binding267 : (data.drop 267).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 267).take 1 :=
  view267.trans (piece267.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 267 1))

numeric_data_binding view268 : (data.drop 268).take 1 = (data264.drop 4).take 1

numeric_data_binding piece268 : (data264.drop 4).take 1 = ((originalEntries.drop 268).take 1).map NumericFunctionalBaseChecks.encode

theorem binding268 : (data.drop 268).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 268).take 1 :=
  view268.trans (piece268.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 268 1))

numeric_data_binding view269 : (data.drop 269).take 1 = (data264.drop 5).take 1

numeric_data_binding piece269 : (data264.drop 5).take 1 = ((originalEntries.drop 269).take 1).map NumericFunctionalBaseChecks.encode

theorem binding269 : (data.drop 269).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 269).take 1 :=
  view269.trans (piece269.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 269 1))

numeric_data_binding view270 : (data.drop 270).take 1 = (data264.drop 6).take 1

numeric_data_binding piece270 : (data264.drop 6).take 1 = ((originalEntries.drop 270).take 1).map NumericFunctionalBaseChecks.encode

theorem binding270 : (data.drop 270).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 270).take 1 :=
  view270.trans (piece270.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 270 1))

numeric_data_binding view271 : (data.drop 271).take 1 = (data264.drop 7).take 1

numeric_data_binding piece271 : (data264.drop 7).take 1 = ((originalEntries.drop 271).take 1).map NumericFunctionalBaseChecks.encode

theorem binding271 : (data.drop 271).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 271).take 1 :=
  view271.trans (piece271.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 271 1))

numeric_data_binding view272 : (data.drop 272).take 1 = (data272.drop 0).take 1

numeric_data_binding piece272 : (data272.drop 0).take 1 = ((originalEntries.drop 272).take 1).map NumericFunctionalBaseChecks.encode

theorem binding272 : (data.drop 272).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 272).take 1 :=
  view272.trans (piece272.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 272 1))

numeric_data_binding view273 : (data.drop 273).take 1 = (data272.drop 1).take 1

numeric_data_binding piece273 : (data272.drop 1).take 1 = ((originalEntries.drop 273).take 1).map NumericFunctionalBaseChecks.encode

theorem binding273 : (data.drop 273).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 273).take 1 :=
  view273.trans (piece273.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 273 1))

numeric_data_binding view274 : (data.drop 274).take 1 = (data272.drop 2).take 1

numeric_data_binding piece274 : (data272.drop 2).take 1 = ((originalEntries.drop 274).take 1).map NumericFunctionalBaseChecks.encode

theorem binding274 : (data.drop 274).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 274).take 1 :=
  view274.trans (piece274.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 274 1))

numeric_data_binding view275 : (data.drop 275).take 1 = (data272.drop 3).take 1

numeric_data_binding piece275 : (data272.drop 3).take 1 = ((originalEntries.drop 275).take 1).map NumericFunctionalBaseChecks.encode

theorem binding275 : (data.drop 275).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 275).take 1 :=
  view275.trans (piece275.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 275 1))

numeric_data_binding view276 : (data.drop 276).take 1 = (data272.drop 4).take 1

numeric_data_binding piece276 : (data272.drop 4).take 1 = ((originalEntries.drop 276).take 1).map NumericFunctionalBaseChecks.encode

theorem binding276 : (data.drop 276).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 276).take 1 :=
  view276.trans (piece276.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 276 1))

numeric_data_binding view277 : (data.drop 277).take 1 = (data272.drop 5).take 1

numeric_data_binding piece277 : (data272.drop 5).take 1 = ((originalEntries.drop 277).take 1).map NumericFunctionalBaseChecks.encode

theorem binding277 : (data.drop 277).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 277).take 1 :=
  view277.trans (piece277.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 277 1))

numeric_data_binding view278 : (data.drop 278).take 1 = (data272.drop 6).take 1

numeric_data_binding piece278 : (data272.drop 6).take 1 = ((originalEntries.drop 278).take 1).map NumericFunctionalBaseChecks.encode

theorem binding278 : (data.drop 278).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 278).take 1 :=
  view278.trans (piece278.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 278 1))

numeric_data_binding view279 : (data.drop 279).take 1 = (data272.drop 7).take 1

numeric_data_binding piece279 : (data272.drop 7).take 1 = ((originalEntries.drop 279).take 1).map NumericFunctionalBaseChecks.encode

theorem binding279 : (data.drop 279).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 279).take 1 :=
  view279.trans (piece279.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 279 1))

numeric_data_binding view280 : (data.drop 280).take 1 = (data280.drop 0).take 1

numeric_data_binding piece280 : (data280.drop 0).take 1 = ((originalEntries.drop 280).take 1).map NumericFunctionalBaseChecks.encode

theorem binding280 : (data.drop 280).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 280).take 1 :=
  view280.trans (piece280.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 280 1))

numeric_data_binding view281 : (data.drop 281).take 1 = (data280.drop 1).take 1

numeric_data_binding piece281 : (data280.drop 1).take 1 = ((originalEntries.drop 281).take 1).map NumericFunctionalBaseChecks.encode

theorem binding281 : (data.drop 281).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 281).take 1 :=
  view281.trans (piece281.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 281 1))

numeric_data_binding view282 : (data.drop 282).take 1 = (data280.drop 2).take 1

numeric_data_binding piece282 : (data280.drop 2).take 1 = ((originalEntries.drop 282).take 1).map NumericFunctionalBaseChecks.encode

theorem binding282 : (data.drop 282).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 282).take 1 :=
  view282.trans (piece282.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 282 1))

numeric_data_binding view283 : (data.drop 283).take 1 = (data280.drop 3).take 1

numeric_data_binding piece283 : (data280.drop 3).take 1 = ((originalEntries.drop 283).take 1).map NumericFunctionalBaseChecks.encode

theorem binding283 : (data.drop 283).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 283).take 1 :=
  view283.trans (piece283.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 283 1))

numeric_data_binding view284 : (data.drop 284).take 1 = (data280.drop 4).take 1

numeric_data_binding piece284 : (data280.drop 4).take 1 = ((originalEntries.drop 284).take 1).map NumericFunctionalBaseChecks.encode

theorem binding284 : (data.drop 284).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 284).take 1 :=
  view284.trans (piece284.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 284 1))

numeric_data_binding view285 : (data.drop 285).take 1 = (data280.drop 5).take 1

numeric_data_binding piece285 : (data280.drop 5).take 1 = ((originalEntries.drop 285).take 1).map NumericFunctionalBaseChecks.encode

theorem binding285 : (data.drop 285).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 285).take 1 :=
  view285.trans (piece285.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 285 1))

numeric_data_binding view286 : (data.drop 286).take 1 = (data280.drop 6).take 1

numeric_data_binding piece286 : (data280.drop 6).take 1 = ((originalEntries.drop 286).take 1).map NumericFunctionalBaseChecks.encode

theorem binding286 : (data.drop 286).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 286).take 1 :=
  view286.trans (piece286.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 286 1))

numeric_data_binding view287 : (data.drop 287).take 1 = (data280.drop 7).take 1

numeric_data_binding piece287 : (data280.drop 7).take 1 = ((originalEntries.drop 287).take 1).map NumericFunctionalBaseChecks.encode

theorem binding287 : (data.drop 287).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 287).take 1 :=
  view287.trans (piece287.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 287 1))

numeric_data_binding view288 : (data.drop 288).take 1 = (data288.drop 0).take 1

numeric_data_binding piece288 : (data288.drop 0).take 1 = ((originalEntries.drop 288).take 1).map NumericFunctionalBaseChecks.encode

theorem binding288 : (data.drop 288).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 288).take 1 :=
  view288.trans (piece288.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 288 1))

numeric_data_binding view289 : (data.drop 289).take 1 = (data288.drop 1).take 1

numeric_data_binding piece289 : (data288.drop 1).take 1 = ((originalEntries.drop 289).take 1).map NumericFunctionalBaseChecks.encode

theorem binding289 : (data.drop 289).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 289).take 1 :=
  view289.trans (piece289.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 289 1))

numeric_data_binding view290 : (data.drop 290).take 1 = (data288.drop 2).take 1

numeric_data_binding piece290 : (data288.drop 2).take 1 = ((originalEntries.drop 290).take 1).map NumericFunctionalBaseChecks.encode

theorem binding290 : (data.drop 290).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 290).take 1 :=
  view290.trans (piece290.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 290 1))

numeric_data_binding view291 : (data.drop 291).take 1 = (data288.drop 3).take 1

numeric_data_binding piece291 : (data288.drop 3).take 1 = ((originalEntries.drop 291).take 1).map NumericFunctionalBaseChecks.encode

theorem binding291 : (data.drop 291).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 291).take 1 :=
  view291.trans (piece291.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 291 1))

numeric_data_binding view292 : (data.drop 292).take 1 = (data288.drop 4).take 1

numeric_data_binding piece292 : (data288.drop 4).take 1 = ((originalEntries.drop 292).take 1).map NumericFunctionalBaseChecks.encode

theorem binding292 : (data.drop 292).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 292).take 1 :=
  view292.trans (piece292.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 292 1))

numeric_data_binding view293 : (data.drop 293).take 1 = (data288.drop 5).take 1

numeric_data_binding piece293 : (data288.drop 5).take 1 = ((originalEntries.drop 293).take 1).map NumericFunctionalBaseChecks.encode

theorem binding293 : (data.drop 293).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 293).take 1 :=
  view293.trans (piece293.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 293 1))

numeric_data_binding view294 : (data.drop 294).take 1 = (data288.drop 6).take 1

numeric_data_binding piece294 : (data288.drop 6).take 1 = ((originalEntries.drop 294).take 1).map NumericFunctionalBaseChecks.encode

theorem binding294 : (data.drop 294).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 294).take 1 :=
  view294.trans (piece294.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 294 1))

numeric_data_binding view295 : (data.drop 295).take 1 = (data288.drop 7).take 1

numeric_data_binding piece295 : (data288.drop 7).take 1 = ((originalEntries.drop 295).take 1).map NumericFunctionalBaseChecks.encode

theorem binding295 : (data.drop 295).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 295).take 1 :=
  view295.trans (piece295.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 295 1))

numeric_data_binding view296 : (data.drop 296).take 1 = (data296.drop 0).take 1

numeric_data_binding piece296 : (data296.drop 0).take 1 = ((originalEntries.drop 296).take 1).map NumericFunctionalBaseChecks.encode

theorem binding296 : (data.drop 296).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 296).take 1 :=
  view296.trans (piece296.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 296 1))

numeric_data_binding view297 : (data.drop 297).take 1 = (data296.drop 1).take 1

numeric_data_binding piece297 : (data296.drop 1).take 1 = ((originalEntries.drop 297).take 1).map NumericFunctionalBaseChecks.encode

theorem binding297 : (data.drop 297).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 297).take 1 :=
  view297.trans (piece297.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 297 1))

numeric_data_binding view298 : (data.drop 298).take 1 = (data296.drop 2).take 1

numeric_data_binding piece298 : (data296.drop 2).take 1 = ((originalEntries.drop 298).take 1).map NumericFunctionalBaseChecks.encode

theorem binding298 : (data.drop 298).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 298).take 1 :=
  view298.trans (piece298.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 298 1))

numeric_data_binding view299 : (data.drop 299).take 1 = (data296.drop 3).take 1

numeric_data_binding piece299 : (data296.drop 3).take 1 = ((originalEntries.drop 299).take 1).map NumericFunctionalBaseChecks.encode

theorem binding299 : (data.drop 299).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 299).take 1 :=
  view299.trans (piece299.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 299 1))

numeric_data_binding view300 : (data.drop 300).take 1 = (data296.drop 4).take 1

numeric_data_binding piece300 : (data296.drop 4).take 1 = ((originalEntries.drop 300).take 1).map NumericFunctionalBaseChecks.encode

theorem binding300 : (data.drop 300).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 300).take 1 :=
  view300.trans (piece300.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 300 1))

numeric_data_binding view301 : (data.drop 301).take 1 = (data296.drop 5).take 1

numeric_data_binding piece301 : (data296.drop 5).take 1 = ((originalEntries.drop 301).take 1).map NumericFunctionalBaseChecks.encode

theorem binding301 : (data.drop 301).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 301).take 1 :=
  view301.trans (piece301.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 301 1))

numeric_data_binding view302 : (data.drop 302).take 1 = (data296.drop 6).take 1

numeric_data_binding piece302 : (data296.drop 6).take 1 = ((originalEntries.drop 302).take 1).map NumericFunctionalBaseChecks.encode

theorem binding302 : (data.drop 302).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 302).take 1 :=
  view302.trans (piece302.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 302 1))

numeric_data_binding view303 : (data.drop 303).take 1 = (data296.drop 7).take 1

numeric_data_binding piece303 : (data296.drop 7).take 1 = ((originalEntries.drop 303).take 1).map NumericFunctionalBaseChecks.encode

theorem binding303 : (data.drop 303).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 303).take 1 :=
  view303.trans (piece303.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 303 1))

numeric_data_binding view304 : (data.drop 304).take 1 = (data304.drop 0).take 1

numeric_data_binding piece304 : (data304.drop 0).take 1 = ((originalEntries.drop 304).take 1).map NumericFunctionalBaseChecks.encode

theorem binding304 : (data.drop 304).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 304).take 1 :=
  view304.trans (piece304.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 304 1))

numeric_data_binding view305 : (data.drop 305).take 1 = (data304.drop 1).take 1

numeric_data_binding piece305 : (data304.drop 1).take 1 = ((originalEntries.drop 305).take 1).map NumericFunctionalBaseChecks.encode

theorem binding305 : (data.drop 305).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 305).take 1 :=
  view305.trans (piece305.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 305 1))

numeric_data_binding view306 : (data.drop 306).take 1 = (data304.drop 2).take 1

numeric_data_binding piece306 : (data304.drop 2).take 1 = ((originalEntries.drop 306).take 1).map NumericFunctionalBaseChecks.encode

theorem binding306 : (data.drop 306).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 306).take 1 :=
  view306.trans (piece306.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 306 1))

numeric_data_binding view307 : (data.drop 307).take 1 = (data304.drop 3).take 1

numeric_data_binding piece307 : (data304.drop 3).take 1 = ((originalEntries.drop 307).take 1).map NumericFunctionalBaseChecks.encode

theorem binding307 : (data.drop 307).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 307).take 1 :=
  view307.trans (piece307.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 307 1))

numeric_data_binding view308 : (data.drop 308).take 1 = (data304.drop 4).take 1

numeric_data_binding piece308 : (data304.drop 4).take 1 = ((originalEntries.drop 308).take 1).map NumericFunctionalBaseChecks.encode

theorem binding308 : (data.drop 308).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 308).take 1 :=
  view308.trans (piece308.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 308 1))

numeric_data_binding view309 : (data.drop 309).take 1 = (data304.drop 5).take 1

numeric_data_binding piece309 : (data304.drop 5).take 1 = ((originalEntries.drop 309).take 1).map NumericFunctionalBaseChecks.encode

theorem binding309 : (data.drop 309).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 309).take 1 :=
  view309.trans (piece309.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 309 1))

numeric_data_binding view310 : (data.drop 310).take 1 = (data304.drop 6).take 1

numeric_data_binding piece310 : (data304.drop 6).take 1 = ((originalEntries.drop 310).take 1).map NumericFunctionalBaseChecks.encode

theorem binding310 : (data.drop 310).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 310).take 1 :=
  view310.trans (piece310.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 310 1))

numeric_data_binding view311 : (data.drop 311).take 1 = (data304.drop 7).take 1

numeric_data_binding piece311 : (data304.drop 7).take 1 = ((originalEntries.drop 311).take 1).map NumericFunctionalBaseChecks.encode

theorem binding311 : (data.drop 311).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 311).take 1 :=
  view311.trans (piece311.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 311 1))

numeric_data_binding view312 : (data.drop 312).take 1 = (data312.drop 0).take 1

numeric_data_binding piece312 : (data312.drop 0).take 1 = ((originalEntries.drop 312).take 1).map NumericFunctionalBaseChecks.encode

theorem binding312 : (data.drop 312).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 312).take 1 :=
  view312.trans (piece312.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 312 1))

numeric_data_binding view313 : (data.drop 313).take 1 = (data312.drop 1).take 1

numeric_data_binding piece313 : (data312.drop 1).take 1 = ((originalEntries.drop 313).take 1).map NumericFunctionalBaseChecks.encode

theorem binding313 : (data.drop 313).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 313).take 1 :=
  view313.trans (piece313.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 313 1))

numeric_data_binding view314 : (data.drop 314).take 1 = (data312.drop 2).take 1

numeric_data_binding piece314 : (data312.drop 2).take 1 = ((originalEntries.drop 314).take 1).map NumericFunctionalBaseChecks.encode

theorem binding314 : (data.drop 314).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 314).take 1 :=
  view314.trans (piece314.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 314 1))

numeric_data_binding view315 : (data.drop 315).take 1 = (data312.drop 3).take 1

numeric_data_binding piece315 : (data312.drop 3).take 1 = ((originalEntries.drop 315).take 1).map NumericFunctionalBaseChecks.encode

theorem binding315 : (data.drop 315).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 315).take 1 :=
  view315.trans (piece315.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 315 1))

numeric_data_binding view316 : (data.drop 316).take 1 = (data312.drop 4).take 1

numeric_data_binding piece316 : (data312.drop 4).take 1 = ((originalEntries.drop 316).take 1).map NumericFunctionalBaseChecks.encode

theorem binding316 : (data.drop 316).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 316).take 1 :=
  view316.trans (piece316.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 316 1))

numeric_data_binding view317 : (data.drop 317).take 1 = (data312.drop 5).take 1

numeric_data_binding piece317 : (data312.drop 5).take 1 = ((originalEntries.drop 317).take 1).map NumericFunctionalBaseChecks.encode

theorem binding317 : (data.drop 317).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 317).take 1 :=
  view317.trans (piece317.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 317 1))

numeric_data_binding view318 : (data.drop 318).take 1 = (data312.drop 6).take 1

numeric_data_binding piece318 : (data312.drop 6).take 1 = ((originalEntries.drop 318).take 1).map NumericFunctionalBaseChecks.encode

theorem binding318 : (data.drop 318).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 318).take 1 :=
  view318.trans (piece318.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 318 1))

numeric_data_binding view319 : (data.drop 319).take 1 = (data312.drop 7).take 1

numeric_data_binding piece319 : (data312.drop 7).take 1 = ((originalEntries.drop 319).take 1).map NumericFunctionalBaseChecks.encode

theorem binding319 : (data.drop 319).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 319).take 1 :=
  view319.trans (piece319.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 319 1))

numeric_data_binding view320 : (data.drop 320).take 1 = (data320.drop 0).take 1

numeric_data_binding piece320 : (data320.drop 0).take 1 = ((originalEntries.drop 320).take 1).map NumericFunctionalBaseChecks.encode

theorem binding320 : (data.drop 320).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 320).take 1 :=
  view320.trans (piece320.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 320 1))

numeric_data_binding view321 : (data.drop 321).take 1 = (data320.drop 1).take 1

numeric_data_binding piece321 : (data320.drop 1).take 1 = ((originalEntries.drop 321).take 1).map NumericFunctionalBaseChecks.encode

theorem binding321 : (data.drop 321).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 321).take 1 :=
  view321.trans (piece321.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 321 1))

numeric_data_binding view322 : (data.drop 322).take 1 = (data320.drop 2).take 1

numeric_data_binding piece322 : (data320.drop 2).take 1 = ((originalEntries.drop 322).take 1).map NumericFunctionalBaseChecks.encode

theorem binding322 : (data.drop 322).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 322).take 1 :=
  view322.trans (piece322.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 322 1))

numeric_data_binding view323 : (data.drop 323).take 1 = (data320.drop 3).take 1

numeric_data_binding piece323 : (data320.drop 3).take 1 = ((originalEntries.drop 323).take 1).map NumericFunctionalBaseChecks.encode

theorem binding323 : (data.drop 323).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 323).take 1 :=
  view323.trans (piece323.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 323 1))

numeric_data_binding view324 : (data.drop 324).take 1 = (data320.drop 4).take 1

numeric_data_binding piece324 : (data320.drop 4).take 1 = ((originalEntries.drop 324).take 1).map NumericFunctionalBaseChecks.encode

theorem binding324 : (data.drop 324).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 324).take 1 :=
  view324.trans (piece324.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 324 1))

numeric_data_binding view325 : (data.drop 325).take 1 = (data320.drop 5).take 1

numeric_data_binding piece325 : (data320.drop 5).take 1 = ((originalEntries.drop 325).take 1).map NumericFunctionalBaseChecks.encode

theorem binding325 : (data.drop 325).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 325).take 1 :=
  view325.trans (piece325.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 325 1))

numeric_data_binding view326 : (data.drop 326).take 1 = (data320.drop 6).take 1

numeric_data_binding piece326 : (data320.drop 6).take 1 = ((originalEntries.drop 326).take 1).map NumericFunctionalBaseChecks.encode

theorem binding326 : (data.drop 326).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 326).take 1 :=
  view326.trans (piece326.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 326 1))

numeric_data_binding view327 : (data.drop 327).take 1 = (data320.drop 7).take 1

numeric_data_binding piece327 : (data320.drop 7).take 1 = ((originalEntries.drop 327).take 1).map NumericFunctionalBaseChecks.encode

theorem binding327 : (data.drop 327).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 327).take 1 :=
  view327.trans (piece327.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 327 1))

numeric_data_binding view328 : (data.drop 328).take 1 = (data328.drop 0).take 1

numeric_data_binding piece328 : (data328.drop 0).take 1 = ((originalEntries.drop 328).take 1).map NumericFunctionalBaseChecks.encode

theorem binding328 : (data.drop 328).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 328).take 1 :=
  view328.trans (piece328.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 328 1))

numeric_data_binding view329 : (data.drop 329).take 1 = (data328.drop 1).take 1

numeric_data_binding piece329 : (data328.drop 1).take 1 = ((originalEntries.drop 329).take 1).map NumericFunctionalBaseChecks.encode

theorem binding329 : (data.drop 329).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 329).take 1 :=
  view329.trans (piece329.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 329 1))

numeric_data_binding view330 : (data.drop 330).take 1 = (data328.drop 2).take 1

numeric_data_binding piece330 : (data328.drop 2).take 1 = ((originalEntries.drop 330).take 1).map NumericFunctionalBaseChecks.encode

theorem binding330 : (data.drop 330).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 330).take 1 :=
  view330.trans (piece330.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 330 1))

numeric_data_binding view331 : (data.drop 331).take 1 = (data328.drop 3).take 1

numeric_data_binding piece331 : (data328.drop 3).take 1 = ((originalEntries.drop 331).take 1).map NumericFunctionalBaseChecks.encode

theorem binding331 : (data.drop 331).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 331).take 1 :=
  view331.trans (piece331.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 331 1))

numeric_data_binding view332 : (data.drop 332).take 1 = (data328.drop 4).take 1

numeric_data_binding piece332 : (data328.drop 4).take 1 = ((originalEntries.drop 332).take 1).map NumericFunctionalBaseChecks.encode

theorem binding332 : (data.drop 332).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 332).take 1 :=
  view332.trans (piece332.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 332 1))

numeric_data_binding view333 : (data.drop 333).take 1 = (data328.drop 5).take 1

numeric_data_binding piece333 : (data328.drop 5).take 1 = ((originalEntries.drop 333).take 1).map NumericFunctionalBaseChecks.encode

theorem binding333 : (data.drop 333).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 333).take 1 :=
  view333.trans (piece333.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 333 1))

numeric_data_binding view334 : (data.drop 334).take 1 = (data328.drop 6).take 1

numeric_data_binding piece334 : (data328.drop 6).take 1 = ((originalEntries.drop 334).take 1).map NumericFunctionalBaseChecks.encode

theorem binding334 : (data.drop 334).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 334).take 1 :=
  view334.trans (piece334.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 334 1))

numeric_data_binding view335 : (data.drop 335).take 1 = (data328.drop 7).take 1

numeric_data_binding piece335 : (data328.drop 7).take 1 = ((originalEntries.drop 335).take 1).map NumericFunctionalBaseChecks.encode

theorem binding335 : (data.drop 335).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 335).take 1 :=
  view335.trans (piece335.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 335 1))

numeric_data_binding view336 : (data.drop 336).take 1 = (data336.drop 0).take 1

numeric_data_binding piece336 : (data336.drop 0).take 1 = ((originalEntries.drop 336).take 1).map NumericFunctionalBaseChecks.encode

theorem binding336 : (data.drop 336).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 336).take 1 :=
  view336.trans (piece336.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 336 1))

numeric_data_binding view337 : (data.drop 337).take 1 = (data336.drop 1).take 1

numeric_data_binding piece337 : (data336.drop 1).take 1 = ((originalEntries.drop 337).take 1).map NumericFunctionalBaseChecks.encode

theorem binding337 : (data.drop 337).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 337).take 1 :=
  view337.trans (piece337.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 337 1))

numeric_data_binding view338 : (data.drop 338).take 1 = (data336.drop 2).take 1

numeric_data_binding piece338 : (data336.drop 2).take 1 = ((originalEntries.drop 338).take 1).map NumericFunctionalBaseChecks.encode

theorem binding338 : (data.drop 338).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 338).take 1 :=
  view338.trans (piece338.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 338 1))

numeric_data_binding view339 : (data.drop 339).take 1 = (data336.drop 3).take 1

numeric_data_binding piece339 : (data336.drop 3).take 1 = ((originalEntries.drop 339).take 1).map NumericFunctionalBaseChecks.encode

theorem binding339 : (data.drop 339).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 339).take 1 :=
  view339.trans (piece339.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 339 1))

numeric_data_binding view340 : (data.drop 340).take 1 = (data336.drop 4).take 1

numeric_data_binding piece340 : (data336.drop 4).take 1 = ((originalEntries.drop 340).take 1).map NumericFunctionalBaseChecks.encode

theorem binding340 : (data.drop 340).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 340).take 1 :=
  view340.trans (piece340.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 340 1))

numeric_data_binding view341 : (data.drop 341).take 1 = (data336.drop 5).take 1

numeric_data_binding piece341 : (data336.drop 5).take 1 = ((originalEntries.drop 341).take 1).map NumericFunctionalBaseChecks.encode

theorem binding341 : (data.drop 341).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 341).take 1 :=
  view341.trans (piece341.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 341 1))

numeric_data_binding view342 : (data.drop 342).take 1 = (data336.drop 6).take 1

numeric_data_binding piece342 : (data336.drop 6).take 1 = ((originalEntries.drop 342).take 1).map NumericFunctionalBaseChecks.encode

theorem binding342 : (data.drop 342).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 342).take 1 :=
  view342.trans (piece342.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 342 1))

numeric_data_binding view343 : (data.drop 343).take 1 = (data336.drop 7).take 1

numeric_data_binding piece343 : (data336.drop 7).take 1 = ((originalEntries.drop 343).take 1).map NumericFunctionalBaseChecks.encode

theorem binding343 : (data.drop 343).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 343).take 1 :=
  view343.trans (piece343.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 343 1))

numeric_data_binding view344 : (data.drop 344).take 1 = (data344.drop 0).take 1

numeric_data_binding piece344 : (data344.drop 0).take 1 = ((originalEntries.drop 344).take 1).map NumericFunctionalBaseChecks.encode

theorem binding344 : (data.drop 344).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 344).take 1 :=
  view344.trans (piece344.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 344 1))

numeric_data_binding view345 : (data.drop 345).take 1 = (data344.drop 1).take 1

numeric_data_binding piece345 : (data344.drop 1).take 1 = ((originalEntries.drop 345).take 1).map NumericFunctionalBaseChecks.encode

theorem binding345 : (data.drop 345).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 345).take 1 :=
  view345.trans (piece345.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 345 1))

numeric_data_binding view346 : (data.drop 346).take 1 = (data344.drop 2).take 1

numeric_data_binding piece346 : (data344.drop 2).take 1 = ((originalEntries.drop 346).take 1).map NumericFunctionalBaseChecks.encode

theorem binding346 : (data.drop 346).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 346).take 1 :=
  view346.trans (piece346.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 346 1))

numeric_data_binding view347 : (data.drop 347).take 1 = (data344.drop 3).take 1

numeric_data_binding piece347 : (data344.drop 3).take 1 = ((originalEntries.drop 347).take 1).map NumericFunctionalBaseChecks.encode

theorem binding347 : (data.drop 347).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 347).take 1 :=
  view347.trans (piece347.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 347 1))

numeric_data_binding view348 : (data.drop 348).take 1 = (data344.drop 4).take 1

numeric_data_binding piece348 : (data344.drop 4).take 1 = ((originalEntries.drop 348).take 1).map NumericFunctionalBaseChecks.encode

theorem binding348 : (data.drop 348).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 348).take 1 :=
  view348.trans (piece348.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 348 1))

numeric_data_binding view349 : (data.drop 349).take 1 = (data344.drop 5).take 1

numeric_data_binding piece349 : (data344.drop 5).take 1 = ((originalEntries.drop 349).take 1).map NumericFunctionalBaseChecks.encode

theorem binding349 : (data.drop 349).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 349).take 1 :=
  view349.trans (piece349.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 349 1))

numeric_data_binding view350 : (data.drop 350).take 1 = (data344.drop 6).take 1

numeric_data_binding piece350 : (data344.drop 6).take 1 = ((originalEntries.drop 350).take 1).map NumericFunctionalBaseChecks.encode

theorem binding350 : (data.drop 350).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 350).take 1 :=
  view350.trans (piece350.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 350 1))

numeric_data_binding view351 : (data.drop 351).take 1 = (data344.drop 7).take 1

numeric_data_binding piece351 : (data344.drop 7).take 1 = ((originalEntries.drop 351).take 1).map NumericFunctionalBaseChecks.encode

theorem binding351 : (data.drop 351).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 351).take 1 :=
  view351.trans (piece351.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 351 1))

numeric_data_binding view352 : (data.drop 352).take 1 = (data352.drop 0).take 1

numeric_data_binding piece352 : (data352.drop 0).take 1 = ((originalEntries.drop 352).take 1).map NumericFunctionalBaseChecks.encode

theorem binding352 : (data.drop 352).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 352).take 1 :=
  view352.trans (piece352.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 352 1))

numeric_data_binding view353 : (data.drop 353).take 1 = (data352.drop 1).take 1

numeric_data_binding piece353 : (data352.drop 1).take 1 = ((originalEntries.drop 353).take 1).map NumericFunctionalBaseChecks.encode

theorem binding353 : (data.drop 353).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 353).take 1 :=
  view353.trans (piece353.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 353 1))

numeric_data_binding view354 : (data.drop 354).take 1 = (data352.drop 2).take 1

numeric_data_binding piece354 : (data352.drop 2).take 1 = ((originalEntries.drop 354).take 1).map NumericFunctionalBaseChecks.encode

theorem binding354 : (data.drop 354).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 354).take 1 :=
  view354.trans (piece354.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 354 1))

numeric_data_binding view355 : (data.drop 355).take 1 = (data352.drop 3).take 1

numeric_data_binding piece355 : (data352.drop 3).take 1 = ((originalEntries.drop 355).take 1).map NumericFunctionalBaseChecks.encode

theorem binding355 : (data.drop 355).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 355).take 1 :=
  view355.trans (piece355.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 355 1))

theorem sourceNode0_2 : (data.drop 0).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 1 1 binding0 binding1

theorem sourceNode3_2 : (data.drop 3).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 3).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 3 1 1 binding3 binding4

theorem sourceNode2_3 : (data.drop 2).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 2).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 2 1 2 binding2 sourceNode3_2

theorem sourceNode0_5 : (data.drop 0).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 2 3 sourceNode0_2 sourceNode2_3

theorem sourceNode6_2 : (data.drop 6).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 6).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 6 1 1 binding6 binding7

theorem sourceNode5_3 : (data.drop 5).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 5).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 5 1 2 binding5 sourceNode6_2

theorem sourceNode9_2 : (data.drop 9).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 9).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 9 1 1 binding9 binding10

theorem sourceNode8_3 : (data.drop 8).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 8 1 2 binding8 sourceNode9_2

theorem sourceNode5_6 : (data.drop 5).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 5).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 5 3 3 sourceNode5_3 sourceNode8_3

theorem sourceNode0_11 : (data.drop 0).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 5 6 sourceNode0_5 sourceNode5_6

theorem sourceNode11_2 : (data.drop 11).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 11).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 11 1 1 binding11 binding12

theorem sourceNode14_2 : (data.drop 14).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 14).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 14 1 1 binding14 binding15

theorem sourceNode13_3 : (data.drop 13).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 13).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 13 1 2 binding13 sourceNode14_2

theorem sourceNode11_5 : (data.drop 11).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 11).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 11 2 3 sourceNode11_2 sourceNode13_3

theorem sourceNode17_2 : (data.drop 17).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 17).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 17 1 1 binding17 binding18

theorem sourceNode16_3 : (data.drop 16).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 16 1 2 binding16 sourceNode17_2

theorem sourceNode20_2 : (data.drop 20).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 20).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 20 1 1 binding20 binding21

theorem sourceNode19_3 : (data.drop 19).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 19).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 19 1 2 binding19 sourceNode20_2

theorem sourceNode16_6 : (data.drop 16).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 16 3 3 sourceNode16_3 sourceNode19_3

theorem sourceNode11_11 : (data.drop 11).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 11).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 11 5 6 sourceNode11_5 sourceNode16_6

theorem sourceNode0_22 : (data.drop 0).take 22 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 22 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 11 11 sourceNode0_11 sourceNode11_11

theorem sourceNode22_2 : (data.drop 22).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 22 1 1 binding22 binding23

theorem sourceNode25_2 : (data.drop 25).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 25).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 25 1 1 binding25 binding26

theorem sourceNode24_3 : (data.drop 24).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 24 1 2 binding24 sourceNode25_2

theorem sourceNode22_5 : (data.drop 22).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 22 2 3 sourceNode22_2 sourceNode24_3

theorem sourceNode28_2 : (data.drop 28).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 28).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 28 1 1 binding28 binding29

theorem sourceNode27_3 : (data.drop 27).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 27).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 27 1 2 binding27 sourceNode28_2

theorem sourceNode31_2 : (data.drop 31).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 31).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 31 1 1 binding31 binding32

theorem sourceNode30_3 : (data.drop 30).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 30).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 30 1 2 binding30 sourceNode31_2

theorem sourceNode27_6 : (data.drop 27).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 27).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 27 3 3 sourceNode27_3 sourceNode30_3

theorem sourceNode22_11 : (data.drop 22).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 22 5 6 sourceNode22_5 sourceNode27_6

theorem sourceNode33_2 : (data.drop 33).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 33).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 33 1 1 binding33 binding34

theorem sourceNode36_2 : (data.drop 36).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 36).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 36 1 1 binding36 binding37

theorem sourceNode35_3 : (data.drop 35).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 35).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 35 1 2 binding35 sourceNode36_2

theorem sourceNode33_5 : (data.drop 33).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 33).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 33 2 3 sourceNode33_2 sourceNode35_3

theorem sourceNode39_2 : (data.drop 39).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 39).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 39 1 1 binding39 binding40

theorem sourceNode38_3 : (data.drop 38).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 38).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 38 1 2 binding38 sourceNode39_2

theorem sourceNode42_2 : (data.drop 42).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 42).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 42 1 1 binding42 binding43

theorem sourceNode41_3 : (data.drop 41).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 41).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 41 1 2 binding41 sourceNode42_2

theorem sourceNode38_6 : (data.drop 38).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 38).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 38 3 3 sourceNode38_3 sourceNode41_3

theorem sourceNode33_11 : (data.drop 33).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 33).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 33 5 6 sourceNode33_5 sourceNode38_6

theorem sourceNode22_22 : (data.drop 22).take 22 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 22 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 22 11 11 sourceNode22_11 sourceNode33_11

theorem sourceNode0_44 : (data.drop 0).take 44 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 44 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 22 22 sourceNode0_22 sourceNode22_22

theorem sourceNode44_2 : (data.drop 44).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 44 1 1 binding44 binding45

theorem sourceNode47_2 : (data.drop 47).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 47).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 47 1 1 binding47 binding48

theorem sourceNode46_3 : (data.drop 46).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 46).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 46 1 2 binding46 sourceNode47_2

theorem sourceNode44_5 : (data.drop 44).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 44 2 3 sourceNode44_2 sourceNode46_3

theorem sourceNode50_2 : (data.drop 50).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 50).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 50 1 1 binding50 binding51

theorem sourceNode49_3 : (data.drop 49).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 49).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 49 1 2 binding49 sourceNode50_2

theorem sourceNode53_2 : (data.drop 53).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 53).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 53 1 1 binding53 binding54

theorem sourceNode52_3 : (data.drop 52).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 52).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 52 1 2 binding52 sourceNode53_2

theorem sourceNode49_6 : (data.drop 49).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 49).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 49 3 3 sourceNode49_3 sourceNode52_3

theorem sourceNode44_11 : (data.drop 44).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 44 5 6 sourceNode44_5 sourceNode49_6

theorem sourceNode55_2 : (data.drop 55).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 55).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 55 1 1 binding55 binding56

theorem sourceNode58_2 : (data.drop 58).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 58).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 58 1 1 binding58 binding59

theorem sourceNode57_3 : (data.drop 57).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 57).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 57 1 2 binding57 sourceNode58_2

theorem sourceNode55_5 : (data.drop 55).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 55).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 55 2 3 sourceNode55_2 sourceNode57_3

theorem sourceNode61_2 : (data.drop 61).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 61).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 61 1 1 binding61 binding62

theorem sourceNode60_3 : (data.drop 60).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 60).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 60 1 2 binding60 sourceNode61_2

theorem sourceNode64_2 : (data.drop 64).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 64 1 1 binding64 binding65

theorem sourceNode63_3 : (data.drop 63).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 63).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 63 1 2 binding63 sourceNode64_2

theorem sourceNode60_6 : (data.drop 60).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 60).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 60 3 3 sourceNode60_3 sourceNode63_3

theorem sourceNode55_11 : (data.drop 55).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 55).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 55 5 6 sourceNode55_5 sourceNode60_6

theorem sourceNode44_22 : (data.drop 44).take 22 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 22 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 44 11 11 sourceNode44_11 sourceNode55_11

theorem sourceNode66_2 : (data.drop 66).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 66).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 66 1 1 binding66 binding67

theorem sourceNode69_2 : (data.drop 69).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 69).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 69 1 1 binding69 binding70

theorem sourceNode68_3 : (data.drop 68).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 68).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 68 1 2 binding68 sourceNode69_2

theorem sourceNode66_5 : (data.drop 66).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 66).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 66 2 3 sourceNode66_2 sourceNode68_3

theorem sourceNode72_2 : (data.drop 72).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 72).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 72 1 1 binding72 binding73

theorem sourceNode71_3 : (data.drop 71).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 71).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 71 1 2 binding71 sourceNode72_2

theorem sourceNode75_2 : (data.drop 75).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 75).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 75 1 1 binding75 binding76

theorem sourceNode74_3 : (data.drop 74).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 74).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 74 1 2 binding74 sourceNode75_2

theorem sourceNode71_6 : (data.drop 71).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 71).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 71 3 3 sourceNode71_3 sourceNode74_3

theorem sourceNode66_11 : (data.drop 66).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 66).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 66 5 6 sourceNode66_5 sourceNode71_6

theorem sourceNode78_2 : (data.drop 78).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 78).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 78 1 1 binding78 binding79

theorem sourceNode77_3 : (data.drop 77).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 77).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 77 1 2 binding77 sourceNode78_2

theorem sourceNode81_2 : (data.drop 81).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 81).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 81 1 1 binding81 binding82

theorem sourceNode80_3 : (data.drop 80).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 80 1 2 binding80 sourceNode81_2

theorem sourceNode77_6 : (data.drop 77).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 77).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 77 3 3 sourceNode77_3 sourceNode80_3

theorem sourceNode84_2 : (data.drop 84).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 84).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 84 1 1 binding84 binding85

theorem sourceNode83_3 : (data.drop 83).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 83).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 83 1 2 binding83 sourceNode84_2

theorem sourceNode87_2 : (data.drop 87).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 87).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 87 1 1 binding87 binding88

theorem sourceNode86_3 : (data.drop 86).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 86).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 86 1 2 binding86 sourceNode87_2

theorem sourceNode83_6 : (data.drop 83).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 83).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 83 3 3 sourceNode83_3 sourceNode86_3

theorem sourceNode77_12 : (data.drop 77).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 77).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 77 6 6 sourceNode77_6 sourceNode83_6

theorem sourceNode66_23 : (data.drop 66).take 23 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 66).take 23 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 66 11 12 sourceNode66_11 sourceNode77_12

theorem sourceNode44_45 : (data.drop 44).take 45 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 45 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 44 22 23 sourceNode44_22 sourceNode66_23

theorem sourceNode0_89 : (data.drop 0).take 89 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 89 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 44 45 sourceNode0_44 sourceNode44_45

theorem sourceNode89_2 : (data.drop 89).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 89).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 89 1 1 binding89 binding90

theorem sourceNode92_2 : (data.drop 92).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 92).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 92 1 1 binding92 binding93

theorem sourceNode91_3 : (data.drop 91).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 91).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 91 1 2 binding91 sourceNode92_2

theorem sourceNode89_5 : (data.drop 89).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 89).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 89 2 3 sourceNode89_2 sourceNode91_3

theorem sourceNode95_2 : (data.drop 95).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 95).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 95 1 1 binding95 binding96

theorem sourceNode94_3 : (data.drop 94).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 94).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 94 1 2 binding94 sourceNode95_2

theorem sourceNode98_2 : (data.drop 98).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 98).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 98 1 1 binding98 binding99

theorem sourceNode97_3 : (data.drop 97).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 97).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 97 1 2 binding97 sourceNode98_2

theorem sourceNode94_6 : (data.drop 94).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 94).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 94 3 3 sourceNode94_3 sourceNode97_3

theorem sourceNode89_11 : (data.drop 89).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 89).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 89 5 6 sourceNode89_5 sourceNode94_6

theorem sourceNode100_2 : (data.drop 100).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 100).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 100 1 1 binding100 binding101

theorem sourceNode103_2 : (data.drop 103).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 103).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 103 1 1 binding103 binding104

theorem sourceNode102_3 : (data.drop 102).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 102).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 102 1 2 binding102 sourceNode103_2

theorem sourceNode100_5 : (data.drop 100).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 100).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 100 2 3 sourceNode100_2 sourceNode102_3

theorem sourceNode106_2 : (data.drop 106).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 106).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 106 1 1 binding106 binding107

theorem sourceNode105_3 : (data.drop 105).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 105).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 105 1 2 binding105 sourceNode106_2

theorem sourceNode109_2 : (data.drop 109).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 109).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 109 1 1 binding109 binding110

theorem sourceNode108_3 : (data.drop 108).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 108).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 108 1 2 binding108 sourceNode109_2

theorem sourceNode105_6 : (data.drop 105).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 105).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 105 3 3 sourceNode105_3 sourceNode108_3

theorem sourceNode100_11 : (data.drop 100).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 100).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 100 5 6 sourceNode100_5 sourceNode105_6

theorem sourceNode89_22 : (data.drop 89).take 22 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 89).take 22 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 89 11 11 sourceNode89_11 sourceNode100_11

theorem sourceNode111_2 : (data.drop 111).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 111).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 111 1 1 binding111 binding112

theorem sourceNode114_2 : (data.drop 114).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 114).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 114 1 1 binding114 binding115

theorem sourceNode113_3 : (data.drop 113).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 113).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 113 1 2 binding113 sourceNode114_2

theorem sourceNode111_5 : (data.drop 111).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 111).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 111 2 3 sourceNode111_2 sourceNode113_3

theorem sourceNode117_2 : (data.drop 117).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 117).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 117 1 1 binding117 binding118

theorem sourceNode116_3 : (data.drop 116).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 116).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 116 1 2 binding116 sourceNode117_2

theorem sourceNode120_2 : (data.drop 120).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 120).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 120 1 1 binding120 binding121

theorem sourceNode119_3 : (data.drop 119).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 119).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 119 1 2 binding119 sourceNode120_2

theorem sourceNode116_6 : (data.drop 116).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 116).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 116 3 3 sourceNode116_3 sourceNode119_3

theorem sourceNode111_11 : (data.drop 111).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 111).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 111 5 6 sourceNode111_5 sourceNode116_6

theorem sourceNode122_2 : (data.drop 122).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 122).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 122 1 1 binding122 binding123

theorem sourceNode125_2 : (data.drop 125).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 125).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 125 1 1 binding125 binding126

theorem sourceNode124_3 : (data.drop 124).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 124).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 124 1 2 binding124 sourceNode125_2

theorem sourceNode122_5 : (data.drop 122).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 122).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 122 2 3 sourceNode122_2 sourceNode124_3

theorem sourceNode128_2 : (data.drop 128).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 128).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 128 1 1 binding128 binding129

theorem sourceNode127_3 : (data.drop 127).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 127).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 127 1 2 binding127 sourceNode128_2

theorem sourceNode131_2 : (data.drop 131).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 131).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 131 1 1 binding131 binding132

theorem sourceNode130_3 : (data.drop 130).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 130).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 130 1 2 binding130 sourceNode131_2

theorem sourceNode127_6 : (data.drop 127).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 127).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 127 3 3 sourceNode127_3 sourceNode130_3

theorem sourceNode122_11 : (data.drop 122).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 122).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 122 5 6 sourceNode122_5 sourceNode127_6

theorem sourceNode111_22 : (data.drop 111).take 22 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 111).take 22 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 111 11 11 sourceNode111_11 sourceNode122_11

theorem sourceNode89_44 : (data.drop 89).take 44 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 89).take 44 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 89 22 22 sourceNode89_22 sourceNode111_22

theorem sourceNode133_2 : (data.drop 133).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 133).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 133 1 1 binding133 binding134

theorem sourceNode136_2 : (data.drop 136).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 136).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 136 1 1 binding136 binding137

theorem sourceNode135_3 : (data.drop 135).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 135).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 135 1 2 binding135 sourceNode136_2

theorem sourceNode133_5 : (data.drop 133).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 133).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 133 2 3 sourceNode133_2 sourceNode135_3

theorem sourceNode139_2 : (data.drop 139).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 139).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 139 1 1 binding139 binding140

theorem sourceNode138_3 : (data.drop 138).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 138).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 138 1 2 binding138 sourceNode139_2

theorem sourceNode142_2 : (data.drop 142).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 142).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 142 1 1 binding142 binding143

theorem sourceNode141_3 : (data.drop 141).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 141).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 141 1 2 binding141 sourceNode142_2

theorem sourceNode138_6 : (data.drop 138).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 138).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 138 3 3 sourceNode138_3 sourceNode141_3

theorem sourceNode133_11 : (data.drop 133).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 133).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 133 5 6 sourceNode133_5 sourceNode138_6

theorem sourceNode144_2 : (data.drop 144).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 144).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 144 1 1 binding144 binding145

theorem sourceNode147_2 : (data.drop 147).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 147).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 147 1 1 binding147 binding148

theorem sourceNode146_3 : (data.drop 146).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 146).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 146 1 2 binding146 sourceNode147_2

theorem sourceNode144_5 : (data.drop 144).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 144).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 144 2 3 sourceNode144_2 sourceNode146_3

theorem sourceNode150_2 : (data.drop 150).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 150).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 150 1 1 binding150 binding151

theorem sourceNode149_3 : (data.drop 149).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 149).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 149 1 2 binding149 sourceNode150_2

theorem sourceNode153_2 : (data.drop 153).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 153).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 153 1 1 binding153 binding154

theorem sourceNode152_3 : (data.drop 152).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 152).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 152 1 2 binding152 sourceNode153_2

theorem sourceNode149_6 : (data.drop 149).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 149).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 149 3 3 sourceNode149_3 sourceNode152_3

theorem sourceNode144_11 : (data.drop 144).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 144).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 144 5 6 sourceNode144_5 sourceNode149_6

theorem sourceNode133_22 : (data.drop 133).take 22 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 133).take 22 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 133 11 11 sourceNode133_11 sourceNode144_11

theorem sourceNode155_2 : (data.drop 155).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 155).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 155 1 1 binding155 binding156

theorem sourceNode158_2 : (data.drop 158).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 158).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 158 1 1 binding158 binding159

theorem sourceNode157_3 : (data.drop 157).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 157).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 157 1 2 binding157 sourceNode158_2

theorem sourceNode155_5 : (data.drop 155).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 155).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 155 2 3 sourceNode155_2 sourceNode157_3

theorem sourceNode161_2 : (data.drop 161).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 161).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 161 1 1 binding161 binding162

theorem sourceNode160_3 : (data.drop 160).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 160).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 160 1 2 binding160 sourceNode161_2

theorem sourceNode164_2 : (data.drop 164).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 164).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 164 1 1 binding164 binding165

theorem sourceNode163_3 : (data.drop 163).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 163).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 163 1 2 binding163 sourceNode164_2

theorem sourceNode160_6 : (data.drop 160).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 160).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 160 3 3 sourceNode160_3 sourceNode163_3

theorem sourceNode155_11 : (data.drop 155).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 155).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 155 5 6 sourceNode155_5 sourceNode160_6

theorem sourceNode167_2 : (data.drop 167).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 167).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 167 1 1 binding167 binding168

theorem sourceNode166_3 : (data.drop 166).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 166).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 166 1 2 binding166 sourceNode167_2

theorem sourceNode170_2 : (data.drop 170).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 170).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 170 1 1 binding170 binding171

theorem sourceNode169_3 : (data.drop 169).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 169).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 169 1 2 binding169 sourceNode170_2

theorem sourceNode166_6 : (data.drop 166).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 166).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 166 3 3 sourceNode166_3 sourceNode169_3

theorem sourceNode173_2 : (data.drop 173).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 173).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 173 1 1 binding173 binding174

theorem sourceNode172_3 : (data.drop 172).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 172).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 172 1 2 binding172 sourceNode173_2

theorem sourceNode176_2 : (data.drop 176).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 176).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 176 1 1 binding176 binding177

theorem sourceNode175_3 : (data.drop 175).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 175).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 175 1 2 binding175 sourceNode176_2

theorem sourceNode172_6 : (data.drop 172).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 172).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 172 3 3 sourceNode172_3 sourceNode175_3

theorem sourceNode166_12 : (data.drop 166).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 166).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 166 6 6 sourceNode166_6 sourceNode172_6

theorem sourceNode155_23 : (data.drop 155).take 23 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 155).take 23 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 155 11 12 sourceNode155_11 sourceNode166_12

theorem sourceNode133_45 : (data.drop 133).take 45 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 133).take 45 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 133 22 23 sourceNode133_22 sourceNode155_23

theorem sourceNode89_89 : (data.drop 89).take 89 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 89).take 89 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 89 44 45 sourceNode89_44 sourceNode133_45

theorem sourceNode0_178 : (data.drop 0).take 178 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 178 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 89 89 sourceNode0_89 sourceNode89_89

theorem sourceNode178_2 : (data.drop 178).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 178).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 178 1 1 binding178 binding179

theorem sourceNode181_2 : (data.drop 181).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 181).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 181 1 1 binding181 binding182

theorem sourceNode180_3 : (data.drop 180).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 180).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 180 1 2 binding180 sourceNode181_2

theorem sourceNode178_5 : (data.drop 178).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 178).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 178 2 3 sourceNode178_2 sourceNode180_3

theorem sourceNode184_2 : (data.drop 184).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 184).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 184 1 1 binding184 binding185

theorem sourceNode183_3 : (data.drop 183).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 183).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 183 1 2 binding183 sourceNode184_2

theorem sourceNode187_2 : (data.drop 187).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 187).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 187 1 1 binding187 binding188

theorem sourceNode186_3 : (data.drop 186).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 186).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 186 1 2 binding186 sourceNode187_2

theorem sourceNode183_6 : (data.drop 183).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 183).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 183 3 3 sourceNode183_3 sourceNode186_3

theorem sourceNode178_11 : (data.drop 178).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 178).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 178 5 6 sourceNode178_5 sourceNode183_6

theorem sourceNode189_2 : (data.drop 189).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 189).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 189 1 1 binding189 binding190

theorem sourceNode192_2 : (data.drop 192).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 192).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 192 1 1 binding192 binding193

theorem sourceNode191_3 : (data.drop 191).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 191).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 191 1 2 binding191 sourceNode192_2

theorem sourceNode189_5 : (data.drop 189).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 189).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 189 2 3 sourceNode189_2 sourceNode191_3

theorem sourceNode195_2 : (data.drop 195).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 195).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 195 1 1 binding195 binding196

theorem sourceNode194_3 : (data.drop 194).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 194).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 194 1 2 binding194 sourceNode195_2

theorem sourceNode198_2 : (data.drop 198).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 198).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 198 1 1 binding198 binding199

theorem sourceNode197_3 : (data.drop 197).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 197).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 197 1 2 binding197 sourceNode198_2

theorem sourceNode194_6 : (data.drop 194).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 194).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 194 3 3 sourceNode194_3 sourceNode197_3

theorem sourceNode189_11 : (data.drop 189).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 189).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 189 5 6 sourceNode189_5 sourceNode194_6

theorem sourceNode178_22 : (data.drop 178).take 22 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 178).take 22 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 178 11 11 sourceNode178_11 sourceNode189_11

theorem sourceNode200_2 : (data.drop 200).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 200).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 200 1 1 binding200 binding201

theorem sourceNode203_2 : (data.drop 203).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 203).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 203 1 1 binding203 binding204

theorem sourceNode202_3 : (data.drop 202).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 202).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 202 1 2 binding202 sourceNode203_2

theorem sourceNode200_5 : (data.drop 200).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 200).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 200 2 3 sourceNode200_2 sourceNode202_3

theorem sourceNode206_2 : (data.drop 206).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 206).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 206 1 1 binding206 binding207

theorem sourceNode205_3 : (data.drop 205).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 205).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 205 1 2 binding205 sourceNode206_2

theorem sourceNode209_2 : (data.drop 209).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 209).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 209 1 1 binding209 binding210

theorem sourceNode208_3 : (data.drop 208).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 208).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 208 1 2 binding208 sourceNode209_2

theorem sourceNode205_6 : (data.drop 205).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 205).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 205 3 3 sourceNode205_3 sourceNode208_3

theorem sourceNode200_11 : (data.drop 200).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 200).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 200 5 6 sourceNode200_5 sourceNode205_6

theorem sourceNode211_2 : (data.drop 211).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 211).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 211 1 1 binding211 binding212

theorem sourceNode214_2 : (data.drop 214).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 214).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 214 1 1 binding214 binding215

theorem sourceNode213_3 : (data.drop 213).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 213).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 213 1 2 binding213 sourceNode214_2

theorem sourceNode211_5 : (data.drop 211).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 211).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 211 2 3 sourceNode211_2 sourceNode213_3

theorem sourceNode217_2 : (data.drop 217).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 217).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 217 1 1 binding217 binding218

theorem sourceNode216_3 : (data.drop 216).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 216).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 216 1 2 binding216 sourceNode217_2

theorem sourceNode220_2 : (data.drop 220).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 220).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 220 1 1 binding220 binding221

theorem sourceNode219_3 : (data.drop 219).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 219).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 219 1 2 binding219 sourceNode220_2

theorem sourceNode216_6 : (data.drop 216).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 216).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 216 3 3 sourceNode216_3 sourceNode219_3

theorem sourceNode211_11 : (data.drop 211).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 211).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 211 5 6 sourceNode211_5 sourceNode216_6

theorem sourceNode200_22 : (data.drop 200).take 22 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 200).take 22 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 200 11 11 sourceNode200_11 sourceNode211_11

theorem sourceNode178_44 : (data.drop 178).take 44 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 178).take 44 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 178 22 22 sourceNode178_22 sourceNode200_22

theorem sourceNode222_2 : (data.drop 222).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 222).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 222 1 1 binding222 binding223

theorem sourceNode225_2 : (data.drop 225).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 225).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 225 1 1 binding225 binding226

theorem sourceNode224_3 : (data.drop 224).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 224).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 224 1 2 binding224 sourceNode225_2

theorem sourceNode222_5 : (data.drop 222).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 222).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 222 2 3 sourceNode222_2 sourceNode224_3

theorem sourceNode228_2 : (data.drop 228).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 228).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 228 1 1 binding228 binding229

theorem sourceNode227_3 : (data.drop 227).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 227).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 227 1 2 binding227 sourceNode228_2

theorem sourceNode231_2 : (data.drop 231).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 231).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 231 1 1 binding231 binding232

theorem sourceNode230_3 : (data.drop 230).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 230).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 230 1 2 binding230 sourceNode231_2

theorem sourceNode227_6 : (data.drop 227).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 227).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 227 3 3 sourceNode227_3 sourceNode230_3

theorem sourceNode222_11 : (data.drop 222).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 222).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 222 5 6 sourceNode222_5 sourceNode227_6

theorem sourceNode233_2 : (data.drop 233).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 233).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 233 1 1 binding233 binding234

theorem sourceNode236_2 : (data.drop 236).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 236).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 236 1 1 binding236 binding237

theorem sourceNode235_3 : (data.drop 235).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 235).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 235 1 2 binding235 sourceNode236_2

theorem sourceNode233_5 : (data.drop 233).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 233).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 233 2 3 sourceNode233_2 sourceNode235_3

theorem sourceNode239_2 : (data.drop 239).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 239).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 239 1 1 binding239 binding240

theorem sourceNode238_3 : (data.drop 238).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 238).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 238 1 2 binding238 sourceNode239_2

theorem sourceNode242_2 : (data.drop 242).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 242).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 242 1 1 binding242 binding243

theorem sourceNode241_3 : (data.drop 241).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 241).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 241 1 2 binding241 sourceNode242_2

theorem sourceNode238_6 : (data.drop 238).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 238).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 238 3 3 sourceNode238_3 sourceNode241_3

theorem sourceNode233_11 : (data.drop 233).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 233).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 233 5 6 sourceNode233_5 sourceNode238_6

theorem sourceNode222_22 : (data.drop 222).take 22 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 222).take 22 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 222 11 11 sourceNode222_11 sourceNode233_11

theorem sourceNode244_2 : (data.drop 244).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 244).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 244 1 1 binding244 binding245

theorem sourceNode247_2 : (data.drop 247).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 247).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 247 1 1 binding247 binding248

theorem sourceNode246_3 : (data.drop 246).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 246).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 246 1 2 binding246 sourceNode247_2

theorem sourceNode244_5 : (data.drop 244).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 244).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 244 2 3 sourceNode244_2 sourceNode246_3

theorem sourceNode250_2 : (data.drop 250).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 250).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 250 1 1 binding250 binding251

theorem sourceNode249_3 : (data.drop 249).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 249).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 249 1 2 binding249 sourceNode250_2

theorem sourceNode253_2 : (data.drop 253).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 253).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 253 1 1 binding253 binding254

theorem sourceNode252_3 : (data.drop 252).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 252).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 252 1 2 binding252 sourceNode253_2

theorem sourceNode249_6 : (data.drop 249).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 249).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 249 3 3 sourceNode249_3 sourceNode252_3

theorem sourceNode244_11 : (data.drop 244).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 244).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 244 5 6 sourceNode244_5 sourceNode249_6

theorem sourceNode256_2 : (data.drop 256).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 256).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 256 1 1 binding256 binding257

theorem sourceNode255_3 : (data.drop 255).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 255).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 255 1 2 binding255 sourceNode256_2

theorem sourceNode259_2 : (data.drop 259).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 259).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 259 1 1 binding259 binding260

theorem sourceNode258_3 : (data.drop 258).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 258).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 258 1 2 binding258 sourceNode259_2

theorem sourceNode255_6 : (data.drop 255).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 255).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 255 3 3 sourceNode255_3 sourceNode258_3

theorem sourceNode262_2 : (data.drop 262).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 262).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 262 1 1 binding262 binding263

theorem sourceNode261_3 : (data.drop 261).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 261).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 261 1 2 binding261 sourceNode262_2

theorem sourceNode265_2 : (data.drop 265).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 265).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 265 1 1 binding265 binding266

theorem sourceNode264_3 : (data.drop 264).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 264).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 264 1 2 binding264 sourceNode265_2

theorem sourceNode261_6 : (data.drop 261).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 261).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 261 3 3 sourceNode261_3 sourceNode264_3

theorem sourceNode255_12 : (data.drop 255).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 255).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 255 6 6 sourceNode255_6 sourceNode261_6

theorem sourceNode244_23 : (data.drop 244).take 23 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 244).take 23 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 244 11 12 sourceNode244_11 sourceNode255_12

theorem sourceNode222_45 : (data.drop 222).take 45 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 222).take 45 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 222 22 23 sourceNode222_22 sourceNode244_23

theorem sourceNode178_89 : (data.drop 178).take 89 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 178).take 89 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 178 44 45 sourceNode178_44 sourceNode222_45

theorem sourceNode267_2 : (data.drop 267).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 267).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 267 1 1 binding267 binding268

theorem sourceNode270_2 : (data.drop 270).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 270).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 270 1 1 binding270 binding271

theorem sourceNode269_3 : (data.drop 269).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 269).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 269 1 2 binding269 sourceNode270_2

theorem sourceNode267_5 : (data.drop 267).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 267).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 267 2 3 sourceNode267_2 sourceNode269_3

theorem sourceNode273_2 : (data.drop 273).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 273).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 273 1 1 binding273 binding274

theorem sourceNode272_3 : (data.drop 272).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 272).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 272 1 2 binding272 sourceNode273_2

theorem sourceNode276_2 : (data.drop 276).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 276).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 276 1 1 binding276 binding277

theorem sourceNode275_3 : (data.drop 275).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 275).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 275 1 2 binding275 sourceNode276_2

theorem sourceNode272_6 : (data.drop 272).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 272).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 272 3 3 sourceNode272_3 sourceNode275_3

theorem sourceNode267_11 : (data.drop 267).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 267).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 267 5 6 sourceNode267_5 sourceNode272_6

theorem sourceNode278_2 : (data.drop 278).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 278).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 278 1 1 binding278 binding279

theorem sourceNode281_2 : (data.drop 281).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 281).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 281 1 1 binding281 binding282

theorem sourceNode280_3 : (data.drop 280).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 280).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 280 1 2 binding280 sourceNode281_2

theorem sourceNode278_5 : (data.drop 278).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 278).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 278 2 3 sourceNode278_2 sourceNode280_3

theorem sourceNode284_2 : (data.drop 284).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 284).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 284 1 1 binding284 binding285

theorem sourceNode283_3 : (data.drop 283).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 283).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 283 1 2 binding283 sourceNode284_2

theorem sourceNode287_2 : (data.drop 287).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 287).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 287 1 1 binding287 binding288

theorem sourceNode286_3 : (data.drop 286).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 286).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 286 1 2 binding286 sourceNode287_2

theorem sourceNode283_6 : (data.drop 283).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 283).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 283 3 3 sourceNode283_3 sourceNode286_3

theorem sourceNode278_11 : (data.drop 278).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 278).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 278 5 6 sourceNode278_5 sourceNode283_6

theorem sourceNode267_22 : (data.drop 267).take 22 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 267).take 22 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 267 11 11 sourceNode267_11 sourceNode278_11

theorem sourceNode289_2 : (data.drop 289).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 289).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 289 1 1 binding289 binding290

theorem sourceNode292_2 : (data.drop 292).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 292).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 292 1 1 binding292 binding293

theorem sourceNode291_3 : (data.drop 291).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 291).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 291 1 2 binding291 sourceNode292_2

theorem sourceNode289_5 : (data.drop 289).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 289).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 289 2 3 sourceNode289_2 sourceNode291_3

theorem sourceNode295_2 : (data.drop 295).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 295).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 295 1 1 binding295 binding296

theorem sourceNode294_3 : (data.drop 294).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 294).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 294 1 2 binding294 sourceNode295_2

theorem sourceNode298_2 : (data.drop 298).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 298).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 298 1 1 binding298 binding299

theorem sourceNode297_3 : (data.drop 297).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 297).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 297 1 2 binding297 sourceNode298_2

theorem sourceNode294_6 : (data.drop 294).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 294).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 294 3 3 sourceNode294_3 sourceNode297_3

theorem sourceNode289_11 : (data.drop 289).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 289).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 289 5 6 sourceNode289_5 sourceNode294_6

theorem sourceNode300_2 : (data.drop 300).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 300).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 300 1 1 binding300 binding301

theorem sourceNode303_2 : (data.drop 303).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 303).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 303 1 1 binding303 binding304

theorem sourceNode302_3 : (data.drop 302).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 302).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 302 1 2 binding302 sourceNode303_2

theorem sourceNode300_5 : (data.drop 300).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 300).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 300 2 3 sourceNode300_2 sourceNode302_3

theorem sourceNode306_2 : (data.drop 306).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 306).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 306 1 1 binding306 binding307

theorem sourceNode305_3 : (data.drop 305).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 305).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 305 1 2 binding305 sourceNode306_2

theorem sourceNode309_2 : (data.drop 309).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 309).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 309 1 1 binding309 binding310

theorem sourceNode308_3 : (data.drop 308).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 308).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 308 1 2 binding308 sourceNode309_2

theorem sourceNode305_6 : (data.drop 305).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 305).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 305 3 3 sourceNode305_3 sourceNode308_3

theorem sourceNode300_11 : (data.drop 300).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 300).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 300 5 6 sourceNode300_5 sourceNode305_6

theorem sourceNode289_22 : (data.drop 289).take 22 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 289).take 22 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 289 11 11 sourceNode289_11 sourceNode300_11

theorem sourceNode267_44 : (data.drop 267).take 44 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 267).take 44 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 267 22 22 sourceNode267_22 sourceNode289_22

theorem sourceNode311_2 : (data.drop 311).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 311).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 311 1 1 binding311 binding312

theorem sourceNode314_2 : (data.drop 314).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 314).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 314 1 1 binding314 binding315

theorem sourceNode313_3 : (data.drop 313).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 313).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 313 1 2 binding313 sourceNode314_2

theorem sourceNode311_5 : (data.drop 311).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 311).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 311 2 3 sourceNode311_2 sourceNode313_3

theorem sourceNode317_2 : (data.drop 317).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 317).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 317 1 1 binding317 binding318

theorem sourceNode316_3 : (data.drop 316).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 316).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 316 1 2 binding316 sourceNode317_2

theorem sourceNode320_2 : (data.drop 320).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 320).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 320 1 1 binding320 binding321

theorem sourceNode319_3 : (data.drop 319).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 319).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 319 1 2 binding319 sourceNode320_2

theorem sourceNode316_6 : (data.drop 316).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 316).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 316 3 3 sourceNode316_3 sourceNode319_3

theorem sourceNode311_11 : (data.drop 311).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 311).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 311 5 6 sourceNode311_5 sourceNode316_6

theorem sourceNode322_2 : (data.drop 322).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 322).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 322 1 1 binding322 binding323

theorem sourceNode325_2 : (data.drop 325).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 325).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 325 1 1 binding325 binding326

theorem sourceNode324_3 : (data.drop 324).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 324).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 324 1 2 binding324 sourceNode325_2

theorem sourceNode322_5 : (data.drop 322).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 322).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 322 2 3 sourceNode322_2 sourceNode324_3

theorem sourceNode328_2 : (data.drop 328).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 328).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 328 1 1 binding328 binding329

theorem sourceNode327_3 : (data.drop 327).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 327).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 327 1 2 binding327 sourceNode328_2

theorem sourceNode331_2 : (data.drop 331).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 331).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 331 1 1 binding331 binding332

theorem sourceNode330_3 : (data.drop 330).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 330).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 330 1 2 binding330 sourceNode331_2

theorem sourceNode327_6 : (data.drop 327).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 327).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 327 3 3 sourceNode327_3 sourceNode330_3

theorem sourceNode322_11 : (data.drop 322).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 322).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 322 5 6 sourceNode322_5 sourceNode327_6

theorem sourceNode311_22 : (data.drop 311).take 22 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 311).take 22 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 311 11 11 sourceNode311_11 sourceNode322_11

theorem sourceNode333_2 : (data.drop 333).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 333).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 333 1 1 binding333 binding334

theorem sourceNode336_2 : (data.drop 336).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 336).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 336 1 1 binding336 binding337

theorem sourceNode335_3 : (data.drop 335).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 335).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 335 1 2 binding335 sourceNode336_2

theorem sourceNode333_5 : (data.drop 333).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 333).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 333 2 3 sourceNode333_2 sourceNode335_3

theorem sourceNode339_2 : (data.drop 339).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 339).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 339 1 1 binding339 binding340

theorem sourceNode338_3 : (data.drop 338).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 338).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 338 1 2 binding338 sourceNode339_2

theorem sourceNode342_2 : (data.drop 342).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 342).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 342 1 1 binding342 binding343

theorem sourceNode341_3 : (data.drop 341).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 341).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 341 1 2 binding341 sourceNode342_2

theorem sourceNode338_6 : (data.drop 338).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 338).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 338 3 3 sourceNode338_3 sourceNode341_3

theorem sourceNode333_11 : (data.drop 333).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 333).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 333 5 6 sourceNode333_5 sourceNode338_6

theorem sourceNode345_2 : (data.drop 345).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 345).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 345 1 1 binding345 binding346

theorem sourceNode344_3 : (data.drop 344).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 344).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 344 1 2 binding344 sourceNode345_2

theorem sourceNode348_2 : (data.drop 348).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 348).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 348 1 1 binding348 binding349

theorem sourceNode347_3 : (data.drop 347).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 347).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 347 1 2 binding347 sourceNode348_2

theorem sourceNode344_6 : (data.drop 344).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 344).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 344 3 3 sourceNode344_3 sourceNode347_3

theorem sourceNode351_2 : (data.drop 351).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 351).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 351 1 1 binding351 binding352

theorem sourceNode350_3 : (data.drop 350).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 350).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 350 1 2 binding350 sourceNode351_2

theorem sourceNode354_2 : (data.drop 354).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 354).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 354 1 1 binding354 binding355

theorem sourceNode353_3 : (data.drop 353).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 353).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 353 1 2 binding353 sourceNode354_2

theorem sourceNode350_6 : (data.drop 350).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 350).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 350 3 3 sourceNode350_3 sourceNode353_3

theorem sourceNode344_12 : (data.drop 344).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 344).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 344 6 6 sourceNode344_6 sourceNode350_6

theorem sourceNode333_23 : (data.drop 333).take 23 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 333).take 23 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 333 11 12 sourceNode333_11 sourceNode344_12

theorem sourceNode311_45 : (data.drop 311).take 45 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 311).take 45 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 311 22 23 sourceNode311_22 sourceNode333_23

theorem sourceNode267_89 : (data.drop 267).take 89 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 267).take 89 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 267 44 45 sourceNode267_44 sourceNode311_45

theorem sourceNode178_178 : (data.drop 178).take 178 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 178).take 178 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 178 89 89 sourceNode178_89 sourceNode267_89

theorem sourceNode0_356 : (data.drop 0).take 356 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 356 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 178 178 sourceNode0_178 sourceNode178_178

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 356
    (by decide +kernel) (by decide +kernel) sourceNode0_356

end Airbender.Compiler.LookupSourceChecks.BigintCached
