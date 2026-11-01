import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.BigintUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.CleanArgumentChecks.BigintUncached
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

theorem sourceNode0_2 : (data.drop 0).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 1 1 binding0 binding1

theorem sourceNode2_2 : (data.drop 2).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 2).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 2 1 1 binding2 binding3

theorem sourceNode0_4 : (data.drop 0).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 2 2 sourceNode0_2 sourceNode2_2

theorem sourceNode4_2 : (data.drop 4).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 4).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 4 1 1 binding4 binding5

theorem sourceNode6_2 : (data.drop 6).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 6).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 6 1 1 binding6 binding7

theorem sourceNode4_4 : (data.drop 4).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 4).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 4 2 2 sourceNode4_2 sourceNode6_2

theorem sourceNode0_8 : (data.drop 0).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 4 4 sourceNode0_4 sourceNode4_4

theorem sourceNode8_2 : (data.drop 8).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 8 1 1 binding8 binding9

theorem sourceNode10_2 : (data.drop 10).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 10).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 10 1 1 binding10 binding11

theorem sourceNode8_4 : (data.drop 8).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 8 2 2 sourceNode8_2 sourceNode10_2

theorem sourceNode12_2 : (data.drop 12).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 12).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 12 1 1 binding12 binding13

theorem sourceNode14_2 : (data.drop 14).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 14).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 14 1 1 binding14 binding15

theorem sourceNode12_4 : (data.drop 12).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 12).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 12 2 2 sourceNode12_2 sourceNode14_2

theorem sourceNode8_8 : (data.drop 8).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 8 4 4 sourceNode8_4 sourceNode12_4

theorem sourceNode0_16 : (data.drop 0).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 8 8 sourceNode0_8 sourceNode8_8

theorem sourceNode16_2 : (data.drop 16).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 16 1 1 binding16 binding17

theorem sourceNode18_2 : (data.drop 18).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 18).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 18 1 1 binding18 binding19

theorem sourceNode16_4 : (data.drop 16).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 16 2 2 sourceNode16_2 sourceNode18_2

theorem sourceNode20_2 : (data.drop 20).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 20).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 20 1 1 binding20 binding21

theorem sourceNode22_2 : (data.drop 22).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 22).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 22 1 1 binding22 binding23

theorem sourceNode20_4 : (data.drop 20).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 20).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 20 2 2 sourceNode20_2 sourceNode22_2

theorem sourceNode16_8 : (data.drop 16).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 16 4 4 sourceNode16_4 sourceNode20_4

theorem sourceNode24_2 : (data.drop 24).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 24 1 1 binding24 binding25

theorem sourceNode26_2 : (data.drop 26).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 26).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 26 1 1 binding26 binding27

theorem sourceNode24_4 : (data.drop 24).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 24 2 2 sourceNode24_2 sourceNode26_2

theorem sourceNode28_2 : (data.drop 28).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 28).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 28 1 1 binding28 binding29

theorem sourceNode30_2 : (data.drop 30).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 30).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 30 1 1 binding30 binding31

theorem sourceNode28_4 : (data.drop 28).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 28).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 28 2 2 sourceNode28_2 sourceNode30_2

theorem sourceNode24_8 : (data.drop 24).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 24 4 4 sourceNode24_4 sourceNode28_4

theorem sourceNode16_16 : (data.drop 16).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 16 8 8 sourceNode16_8 sourceNode24_8

theorem sourceNode0_32 : (data.drop 0).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 16 16 sourceNode0_16 sourceNode16_16

theorem sourceNode32_2 : (data.drop 32).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 1 1 binding32 binding33

theorem sourceNode34_2 : (data.drop 34).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 34).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 34 1 1 binding34 binding35

theorem sourceNode32_4 : (data.drop 32).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 2 2 sourceNode32_2 sourceNode34_2

theorem sourceNode36_2 : (data.drop 36).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 36).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 36 1 1 binding36 binding37

theorem sourceNode38_2 : (data.drop 38).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 38).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 38 1 1 binding38 binding39

theorem sourceNode36_4 : (data.drop 36).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 36).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 36 2 2 sourceNode36_2 sourceNode38_2

theorem sourceNode32_8 : (data.drop 32).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 4 4 sourceNode32_4 sourceNode36_4

theorem sourceNode40_2 : (data.drop 40).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 40).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 40 1 1 binding40 binding41

theorem sourceNode42_2 : (data.drop 42).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 42).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 42 1 1 binding42 binding43

theorem sourceNode40_4 : (data.drop 40).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 40).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 40 2 2 sourceNode40_2 sourceNode42_2

theorem sourceNode44_2 : (data.drop 44).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 44 1 1 binding44 binding45

theorem sourceNode46_2 : (data.drop 46).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 46).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 46 1 1 binding46 binding47

theorem sourceNode44_4 : (data.drop 44).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 44 2 2 sourceNode44_2 sourceNode46_2

theorem sourceNode40_8 : (data.drop 40).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 40).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 40 4 4 sourceNode40_4 sourceNode44_4

theorem sourceNode32_16 : (data.drop 32).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 8 8 sourceNode32_8 sourceNode40_8

theorem sourceNode48_2 : (data.drop 48).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 48).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 48 1 1 binding48 binding49

theorem sourceNode50_2 : (data.drop 50).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 50).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 50 1 1 binding50 binding51

theorem sourceNode48_4 : (data.drop 48).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 48).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 48 2 2 sourceNode48_2 sourceNode50_2

theorem sourceNode52_2 : (data.drop 52).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 52).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 52 1 1 binding52 binding53

theorem sourceNode54_2 : (data.drop 54).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 54).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 54 1 1 binding54 binding55

theorem sourceNode52_4 : (data.drop 52).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 52).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 52 2 2 sourceNode52_2 sourceNode54_2

theorem sourceNode48_8 : (data.drop 48).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 48).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 48 4 4 sourceNode48_4 sourceNode52_4

theorem sourceNode56_2 : (data.drop 56).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 56).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 56 1 1 binding56 binding57

theorem sourceNode58_2 : (data.drop 58).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 58).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 58 1 1 binding58 binding59

theorem sourceNode56_4 : (data.drop 56).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 56).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 56 2 2 sourceNode56_2 sourceNode58_2

theorem sourceNode60_2 : (data.drop 60).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 60).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 60 1 1 binding60 binding61

theorem sourceNode62_2 : (data.drop 62).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 62).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 62 1 1 binding62 binding63

theorem sourceNode60_4 : (data.drop 60).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 60).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 60 2 2 sourceNode60_2 sourceNode62_2

theorem sourceNode56_8 : (data.drop 56).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 56).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 56 4 4 sourceNode56_4 sourceNode60_4

theorem sourceNode48_16 : (data.drop 48).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 48).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 48 8 8 sourceNode48_8 sourceNode56_8

theorem sourceNode32_32 : (data.drop 32).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 16 16 sourceNode32_16 sourceNode48_16

theorem sourceNode0_64 : (data.drop 0).take 64 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 64 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 32 32 sourceNode0_32 sourceNode32_32

theorem sourceNode64_2 : (data.drop 64).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 64 1 1 binding64 binding65

theorem sourceNode66_2 : (data.drop 66).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 66).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 66 1 1 binding66 binding67

theorem sourceNode64_4 : (data.drop 64).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 64 2 2 sourceNode64_2 sourceNode66_2

theorem sourceNode68_2 : (data.drop 68).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 68).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 68 1 1 binding68 binding69

theorem sourceNode70_2 : (data.drop 70).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 70).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 70 1 1 binding70 binding71

theorem sourceNode68_4 : (data.drop 68).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 68).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 68 2 2 sourceNode68_2 sourceNode70_2

theorem sourceNode64_8 : (data.drop 64).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 64 4 4 sourceNode64_4 sourceNode68_4

theorem sourceNode72_2 : (data.drop 72).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 72).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 72 1 1 binding72 binding73

theorem sourceNode74_2 : (data.drop 74).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 74).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 74 1 1 binding74 binding75

theorem sourceNode72_4 : (data.drop 72).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 72).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 72 2 2 sourceNode72_2 sourceNode74_2

theorem sourceNode76_2 : (data.drop 76).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 76).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 76 1 1 binding76 binding77

theorem sourceNode78_2 : (data.drop 78).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 78).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 78 1 1 binding78 binding79

theorem sourceNode76_4 : (data.drop 76).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 76).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 76 2 2 sourceNode76_2 sourceNode78_2

theorem sourceNode72_8 : (data.drop 72).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 72).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 72 4 4 sourceNode72_4 sourceNode76_4

theorem sourceNode64_16 : (data.drop 64).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 64 8 8 sourceNode64_8 sourceNode72_8

theorem sourceNode80_2 : (data.drop 80).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 80 1 1 binding80 binding81

theorem sourceNode82_2 : (data.drop 82).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 82).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 82 1 1 binding82 binding83

theorem sourceNode80_4 : (data.drop 80).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 80 2 2 sourceNode80_2 sourceNode82_2

theorem sourceNode84_2 : (data.drop 84).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 84).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 84 1 1 binding84 binding85

theorem sourceNode86_2 : (data.drop 86).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 86).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 86 1 1 binding86 binding87

theorem sourceNode84_4 : (data.drop 84).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 84).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 84 2 2 sourceNode84_2 sourceNode86_2

theorem sourceNode80_8 : (data.drop 80).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 80 4 4 sourceNode80_4 sourceNode84_4

theorem sourceNode88_2 : (data.drop 88).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 88).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 88 1 1 binding88 binding89

theorem sourceNode90_2 : (data.drop 90).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 90).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 90 1 1 binding90 binding91

theorem sourceNode88_4 : (data.drop 88).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 88).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 88 2 2 sourceNode88_2 sourceNode90_2

theorem sourceNode92_2 : (data.drop 92).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 92).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 92 1 1 binding92 binding93

theorem sourceNode94_2 : (data.drop 94).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 94).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 94 1 1 binding94 binding95

theorem sourceNode92_4 : (data.drop 92).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 92).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 92 2 2 sourceNode92_2 sourceNode94_2

theorem sourceNode88_8 : (data.drop 88).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 88).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 88 4 4 sourceNode88_4 sourceNode92_4

theorem sourceNode80_16 : (data.drop 80).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 80 8 8 sourceNode80_8 sourceNode88_8

theorem sourceNode64_32 : (data.drop 64).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 64 16 16 sourceNode64_16 sourceNode80_16

theorem sourceNode96_2 : (data.drop 96).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 96).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 96 1 1 binding96 binding97

theorem sourceNode98_2 : (data.drop 98).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 98).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 98 1 1 binding98 binding99

theorem sourceNode96_4 : (data.drop 96).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 96).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 96 2 2 sourceNode96_2 sourceNode98_2

theorem sourceNode100_2 : (data.drop 100).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 100).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 100 1 1 binding100 binding101

theorem sourceNode102_2 : (data.drop 102).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 102).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 102 1 1 binding102 binding103

theorem sourceNode100_4 : (data.drop 100).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 100).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 100 2 2 sourceNode100_2 sourceNode102_2

theorem sourceNode96_8 : (data.drop 96).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 96).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 96 4 4 sourceNode96_4 sourceNode100_4

theorem sourceNode104_2 : (data.drop 104).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 104).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 104 1 1 binding104 binding105

theorem sourceNode106_2 : (data.drop 106).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 106).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 106 1 1 binding106 binding107

theorem sourceNode104_4 : (data.drop 104).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 104).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 104 2 2 sourceNode104_2 sourceNode106_2

theorem sourceNode108_2 : (data.drop 108).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 108).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 108 1 1 binding108 binding109

theorem sourceNode110_2 : (data.drop 110).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 110).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 110 1 1 binding110 binding111

theorem sourceNode108_4 : (data.drop 108).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 108).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 108 2 2 sourceNode108_2 sourceNode110_2

theorem sourceNode104_8 : (data.drop 104).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 104).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 104 4 4 sourceNode104_4 sourceNode108_4

theorem sourceNode96_16 : (data.drop 96).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 96).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 96 8 8 sourceNode96_8 sourceNode104_8

theorem sourceNode112_2 : (data.drop 112).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 112).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 112 1 1 binding112 binding113

theorem sourceNode114_2 : (data.drop 114).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 114).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 114 1 1 binding114 binding115

theorem sourceNode112_4 : (data.drop 112).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 112).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 112 2 2 sourceNode112_2 sourceNode114_2

theorem sourceNode116_2 : (data.drop 116).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 116).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 116 1 1 binding116 binding117

theorem sourceNode118_2 : (data.drop 118).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 118).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 118 1 1 binding118 binding119

theorem sourceNode116_4 : (data.drop 116).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 116).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 116 2 2 sourceNode116_2 sourceNode118_2

theorem sourceNode112_8 : (data.drop 112).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 112).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 112 4 4 sourceNode112_4 sourceNode116_4

theorem sourceNode120_2 : (data.drop 120).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 120).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 120 1 1 binding120 binding121

theorem sourceNode122_2 : (data.drop 122).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 122).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 122 1 1 binding122 binding123

theorem sourceNode120_4 : (data.drop 120).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 120).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 120 2 2 sourceNode120_2 sourceNode122_2

theorem sourceNode124_2 : (data.drop 124).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 124).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 124 1 1 binding124 binding125

theorem sourceNode126_2 : (data.drop 126).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 126).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 126 1 1 binding126 binding127

theorem sourceNode124_4 : (data.drop 124).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 124).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 124 2 2 sourceNode124_2 sourceNode126_2

theorem sourceNode120_8 : (data.drop 120).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 120).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 120 4 4 sourceNode120_4 sourceNode124_4

theorem sourceNode112_16 : (data.drop 112).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 112).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 112 8 8 sourceNode112_8 sourceNode120_8

theorem sourceNode96_32 : (data.drop 96).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 96).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 96 16 16 sourceNode96_16 sourceNode112_16

theorem sourceNode64_64 : (data.drop 64).take 64 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 64 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 64 32 32 sourceNode64_32 sourceNode96_32

theorem sourceNode0_128 : (data.drop 0).take 128 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 128 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 64 64 sourceNode0_64 sourceNode64_64

theorem sourceNode128_2 : (data.drop 128).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 128).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 128 1 1 binding128 binding129

theorem sourceNode130_2 : (data.drop 130).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 130).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 130 1 1 binding130 binding131

theorem sourceNode128_4 : (data.drop 128).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 128).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 128 2 2 sourceNode128_2 sourceNode130_2

theorem sourceNode132_2 : (data.drop 132).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 132).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 132 1 1 binding132 binding133

theorem sourceNode134_2 : (data.drop 134).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 134).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 134 1 1 binding134 binding135

theorem sourceNode132_4 : (data.drop 132).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 132).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 132 2 2 sourceNode132_2 sourceNode134_2

theorem sourceNode128_8 : (data.drop 128).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 128).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 128 4 4 sourceNode128_4 sourceNode132_4

theorem sourceNode136_2 : (data.drop 136).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 136).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 136 1 1 binding136 binding137

theorem sourceNode138_2 : (data.drop 138).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 138).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 138 1 1 binding138 binding139

theorem sourceNode136_4 : (data.drop 136).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 136).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 136 2 2 sourceNode136_2 sourceNode138_2

theorem sourceNode140_2 : (data.drop 140).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 140).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 140 1 1 binding140 binding141

theorem sourceNode142_2 : (data.drop 142).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 142).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 142 1 1 binding142 binding143

theorem sourceNode140_4 : (data.drop 140).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 140).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 140 2 2 sourceNode140_2 sourceNode142_2

theorem sourceNode136_8 : (data.drop 136).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 136).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 136 4 4 sourceNode136_4 sourceNode140_4

theorem sourceNode128_16 : (data.drop 128).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 128).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 128 8 8 sourceNode128_8 sourceNode136_8

theorem sourceNode144_2 : (data.drop 144).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 144).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 144 1 1 binding144 binding145

theorem sourceNode146_2 : (data.drop 146).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 146).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 146 1 1 binding146 binding147

theorem sourceNode144_4 : (data.drop 144).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 144).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 144 2 2 sourceNode144_2 sourceNode146_2

theorem sourceNode148_2 : (data.drop 148).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 148).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 148 1 1 binding148 binding149

theorem sourceNode150_2 : (data.drop 150).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 150).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 150 1 1 binding150 binding151

theorem sourceNode148_4 : (data.drop 148).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 148).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 148 2 2 sourceNode148_2 sourceNode150_2

theorem sourceNode144_8 : (data.drop 144).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 144).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 144 4 4 sourceNode144_4 sourceNode148_4

theorem sourceNode152_2 : (data.drop 152).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 152).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 152 1 1 binding152 binding153

theorem sourceNode154_2 : (data.drop 154).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 154).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 154 1 1 binding154 binding155

theorem sourceNode152_4 : (data.drop 152).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 152).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 152 2 2 sourceNode152_2 sourceNode154_2

theorem sourceNode156_2 : (data.drop 156).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 156).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 156 1 1 binding156 binding157

theorem sourceNode158_2 : (data.drop 158).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 158).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 158 1 1 binding158 binding159

theorem sourceNode156_4 : (data.drop 156).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 156).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 156 2 2 sourceNode156_2 sourceNode158_2

theorem sourceNode152_8 : (data.drop 152).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 152).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 152 4 4 sourceNode152_4 sourceNode156_4

theorem sourceNode144_16 : (data.drop 144).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 144).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 144 8 8 sourceNode144_8 sourceNode152_8

theorem sourceNode128_32 : (data.drop 128).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 128).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 128 16 16 sourceNode128_16 sourceNode144_16

theorem sourceNode160_2 : (data.drop 160).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 160).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 160 1 1 binding160 binding161

theorem sourceNode162_2 : (data.drop 162).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 162).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 162 1 1 binding162 binding163

theorem sourceNode160_4 : (data.drop 160).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 160).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 160 2 2 sourceNode160_2 sourceNode162_2

theorem sourceNode164_2 : (data.drop 164).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 164).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 164 1 1 binding164 binding165

theorem sourceNode166_2 : (data.drop 166).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 166).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 166 1 1 binding166 binding167

theorem sourceNode164_4 : (data.drop 164).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 164).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 164 2 2 sourceNode164_2 sourceNode166_2

theorem sourceNode160_8 : (data.drop 160).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 160).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 160 4 4 sourceNode160_4 sourceNode164_4

theorem sourceNode168_2 : (data.drop 168).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 168).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 168 1 1 binding168 binding169

theorem sourceNode170_2 : (data.drop 170).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 170).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 170 1 1 binding170 binding171

theorem sourceNode168_4 : (data.drop 168).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 168).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 168 2 2 sourceNode168_2 sourceNode170_2

theorem sourceNode172_2 : (data.drop 172).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 172).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 172 1 1 binding172 binding173

theorem sourceNode174_2 : (data.drop 174).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 174).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 174 1 1 binding174 binding175

theorem sourceNode172_4 : (data.drop 172).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 172).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 172 2 2 sourceNode172_2 sourceNode174_2

theorem sourceNode168_8 : (data.drop 168).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 168).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 168 4 4 sourceNode168_4 sourceNode172_4

theorem sourceNode160_16 : (data.drop 160).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 160).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 160 8 8 sourceNode160_8 sourceNode168_8

theorem sourceNode176_2 : (data.drop 176).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 176).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 176 1 1 binding176 binding177

theorem sourceNode178_2 : (data.drop 178).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 178).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 178 1 1 binding178 binding179

theorem sourceNode176_4 : (data.drop 176).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 176).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 176 2 2 sourceNode176_2 sourceNode178_2

theorem sourceNode180_2 : (data.drop 180).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 180).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 180 1 1 binding180 binding181

theorem sourceNode182_2 : (data.drop 182).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 182).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 182 1 1 binding182 binding183

theorem sourceNode180_4 : (data.drop 180).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 180).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 180 2 2 sourceNode180_2 sourceNode182_2

theorem sourceNode176_8 : (data.drop 176).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 176).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 176 4 4 sourceNode176_4 sourceNode180_4

theorem sourceNode184_2 : (data.drop 184).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 184).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 184 1 1 binding184 binding185

theorem sourceNode186_2 : (data.drop 186).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 186).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 186 1 1 binding186 binding187

theorem sourceNode184_4 : (data.drop 184).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 184).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 184 2 2 sourceNode184_2 sourceNode186_2

theorem sourceNode188_2 : (data.drop 188).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 188).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 188 1 1 binding188 binding189

theorem sourceNode190_2 : (data.drop 190).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 190).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 190 1 1 binding190 binding191

theorem sourceNode188_4 : (data.drop 188).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 188).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 188 2 2 sourceNode188_2 sourceNode190_2

theorem sourceNode184_8 : (data.drop 184).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 184).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 184 4 4 sourceNode184_4 sourceNode188_4

theorem sourceNode176_16 : (data.drop 176).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 176).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 176 8 8 sourceNode176_8 sourceNode184_8

theorem sourceNode160_32 : (data.drop 160).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 160).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 160 16 16 sourceNode160_16 sourceNode176_16

theorem sourceNode128_64 : (data.drop 128).take 64 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 128).take 64 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 128 32 32 sourceNode128_32 sourceNode160_32

theorem sourceNode192_2 : (data.drop 192).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 192).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 192 1 1 binding192 binding193

theorem sourceNode194_2 : (data.drop 194).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 194).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 194 1 1 binding194 binding195

theorem sourceNode192_4 : (data.drop 192).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 192).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 192 2 2 sourceNode192_2 sourceNode194_2

theorem sourceNode196_2 : (data.drop 196).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 196).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 196 1 1 binding196 binding197

theorem sourceNode198_2 : (data.drop 198).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 198).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 198 1 1 binding198 binding199

theorem sourceNode196_4 : (data.drop 196).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 196).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 196 2 2 sourceNode196_2 sourceNode198_2

theorem sourceNode192_8 : (data.drop 192).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 192).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 192 4 4 sourceNode192_4 sourceNode196_4

theorem sourceNode200_2 : (data.drop 200).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 200).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 200 1 1 binding200 binding201

theorem sourceNode202_2 : (data.drop 202).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 202).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 202 1 1 binding202 binding203

theorem sourceNode200_4 : (data.drop 200).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 200).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 200 2 2 sourceNode200_2 sourceNode202_2

theorem sourceNode204_2 : (data.drop 204).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 204).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 204 1 1 binding204 binding205

theorem sourceNode206_2 : (data.drop 206).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 206).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 206 1 1 binding206 binding207

theorem sourceNode204_4 : (data.drop 204).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 204).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 204 2 2 sourceNode204_2 sourceNode206_2

theorem sourceNode200_8 : (data.drop 200).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 200).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 200 4 4 sourceNode200_4 sourceNode204_4

theorem sourceNode192_16 : (data.drop 192).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 192).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 192 8 8 sourceNode192_8 sourceNode200_8

theorem sourceNode208_2 : (data.drop 208).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 208).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 208 1 1 binding208 binding209

theorem sourceNode210_2 : (data.drop 210).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 210).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 210 1 1 binding210 binding211

theorem sourceNode208_4 : (data.drop 208).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 208).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 208 2 2 sourceNode208_2 sourceNode210_2

theorem sourceNode212_2 : (data.drop 212).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 212).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 212 1 1 binding212 binding213

theorem sourceNode214_2 : (data.drop 214).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 214).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 214 1 1 binding214 binding215

theorem sourceNode212_4 : (data.drop 212).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 212).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 212 2 2 sourceNode212_2 sourceNode214_2

theorem sourceNode208_8 : (data.drop 208).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 208).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 208 4 4 sourceNode208_4 sourceNode212_4

theorem sourceNode216_2 : (data.drop 216).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 216).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 216 1 1 binding216 binding217

theorem sourceNode218_2 : (data.drop 218).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 218).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 218 1 1 binding218 binding219

theorem sourceNode216_4 : (data.drop 216).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 216).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 216 2 2 sourceNode216_2 sourceNode218_2

theorem sourceNode220_2 : (data.drop 220).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 220).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 220 1 1 binding220 binding221

theorem sourceNode222_2 : (data.drop 222).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 222).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 222 1 1 binding222 binding223

theorem sourceNode220_4 : (data.drop 220).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 220).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 220 2 2 sourceNode220_2 sourceNode222_2

theorem sourceNode216_8 : (data.drop 216).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 216).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 216 4 4 sourceNode216_4 sourceNode220_4

theorem sourceNode208_16 : (data.drop 208).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 208).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 208 8 8 sourceNode208_8 sourceNode216_8

theorem sourceNode192_32 : (data.drop 192).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 192).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 192 16 16 sourceNode192_16 sourceNode208_16

theorem sourceNode224_2 : (data.drop 224).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 224).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 224 1 1 binding224 binding225

theorem sourceNode226_2 : (data.drop 226).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 226).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 226 1 1 binding226 binding227

theorem sourceNode224_4 : (data.drop 224).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 224).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 224 2 2 sourceNode224_2 sourceNode226_2

theorem sourceNode228_2 : (data.drop 228).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 228).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 228 1 1 binding228 binding229

theorem sourceNode230_2 : (data.drop 230).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 230).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 230 1 1 binding230 binding231

theorem sourceNode228_4 : (data.drop 228).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 228).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 228 2 2 sourceNode228_2 sourceNode230_2

theorem sourceNode224_8 : (data.drop 224).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 224).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 224 4 4 sourceNode224_4 sourceNode228_4

theorem sourceNode232_2 : (data.drop 232).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 232).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 232 1 1 binding232 binding233

theorem sourceNode234_2 : (data.drop 234).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 234).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 234 1 1 binding234 binding235

theorem sourceNode232_4 : (data.drop 232).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 232).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 232 2 2 sourceNode232_2 sourceNode234_2

theorem sourceNode236_2 : (data.drop 236).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 236).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 236 1 1 binding236 binding237

theorem sourceNode238_2 : (data.drop 238).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 238).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 238 1 1 binding238 binding239

theorem sourceNode236_4 : (data.drop 236).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 236).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 236 2 2 sourceNode236_2 sourceNode238_2

theorem sourceNode232_8 : (data.drop 232).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 232).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 232 4 4 sourceNode232_4 sourceNode236_4

theorem sourceNode224_16 : (data.drop 224).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 224).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 224 8 8 sourceNode224_8 sourceNode232_8

theorem sourceNode240_2 : (data.drop 240).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 240).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 240 1 1 binding240 binding241

theorem sourceNode242_2 : (data.drop 242).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 242).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 242 1 1 binding242 binding243

theorem sourceNode240_4 : (data.drop 240).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 240).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 240 2 2 sourceNode240_2 sourceNode242_2

theorem sourceNode244_2 : (data.drop 244).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 244).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 244 1 1 binding244 binding245

theorem sourceNode246_2 : (data.drop 246).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 246).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 246 1 1 binding246 binding247

theorem sourceNode244_4 : (data.drop 244).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 244).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 244 2 2 sourceNode244_2 sourceNode246_2

theorem sourceNode240_8 : (data.drop 240).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 240).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 240 4 4 sourceNode240_4 sourceNode244_4

theorem sourceNode248_2 : (data.drop 248).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 248).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 248 1 1 binding248 binding249

theorem sourceNode250_2 : (data.drop 250).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 250).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 250 1 1 binding250 binding251

theorem sourceNode248_4 : (data.drop 248).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 248).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 248 2 2 sourceNode248_2 sourceNode250_2

theorem sourceNode252_2 : (data.drop 252).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 252).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 252 1 1 binding252 binding253

theorem sourceNode254_2 : (data.drop 254).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 254).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 254 1 1 binding254 binding255

theorem sourceNode252_4 : (data.drop 252).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 252).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 252 2 2 sourceNode252_2 sourceNode254_2

theorem sourceNode248_8 : (data.drop 248).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 248).take 8 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 248 4 4 sourceNode248_4 sourceNode252_4

theorem sourceNode240_16 : (data.drop 240).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 240).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 240 8 8 sourceNode240_8 sourceNode248_8

theorem sourceNode224_32 : (data.drop 224).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 224).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 224 16 16 sourceNode224_16 sourceNode240_16

theorem sourceNode192_64 : (data.drop 192).take 64 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 192).take 64 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 192 32 32 sourceNode192_32 sourceNode224_32

theorem sourceNode128_128 : (data.drop 128).take 128 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 128).take 128 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 128 64 64 sourceNode128_64 sourceNode192_64

theorem sourceNode0_256 : (data.drop 0).take 256 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 256 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 128 128 sourceNode0_128 sourceNode128_128

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 256
    (by decide +kernel) (by decide +kernel) sourceNode0_256

end Airbender.Compiler.CleanArgumentChecks.BigintUncached
