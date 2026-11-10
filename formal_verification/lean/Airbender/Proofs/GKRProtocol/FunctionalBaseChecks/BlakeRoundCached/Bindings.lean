import Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.BlakeRoundCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.FunctionalBaseChecks.BlakeRoundCached
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

theorem sourceNode12_2 : (data.drop 12).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 12).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 12 1 1 binding12 binding13

theorem sourceNode11_3 : (data.drop 11).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 11).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 11 1 2 binding11 sourceNode12_2

theorem sourceNode15_2 : (data.drop 15).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 15).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 15 1 1 binding15 binding16

theorem sourceNode14_3 : (data.drop 14).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 14).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 14 1 2 binding14 sourceNode15_2

theorem sourceNode11_6 : (data.drop 11).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 11).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 11 3 3 sourceNode11_3 sourceNode14_3

theorem sourceNode18_2 : (data.drop 18).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 18).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 18 1 1 binding18 binding19

theorem sourceNode17_3 : (data.drop 17).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 17).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 17 1 2 binding17 sourceNode18_2

theorem sourceNode21_2 : (data.drop 21).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 21).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 21 1 1 binding21 binding22

theorem sourceNode20_3 : (data.drop 20).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 20).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 20 1 2 binding20 sourceNode21_2

theorem sourceNode17_6 : (data.drop 17).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 17).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 17 3 3 sourceNode17_3 sourceNode20_3

theorem sourceNode11_12 : (data.drop 11).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 11).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 11 6 6 sourceNode11_6 sourceNode17_6

theorem sourceNode0_23 : (data.drop 0).take 23 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 23 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 11 12 sourceNode0_11 sourceNode11_12

theorem sourceNode24_2 : (data.drop 24).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 24 1 1 binding24 binding25

theorem sourceNode23_3 : (data.drop 23).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 23).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 23 1 2 binding23 sourceNode24_2

theorem sourceNode27_2 : (data.drop 27).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 27).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 27 1 1 binding27 binding28

theorem sourceNode26_3 : (data.drop 26).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 26).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 26 1 2 binding26 sourceNode27_2

theorem sourceNode23_6 : (data.drop 23).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 23).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 23 3 3 sourceNode23_3 sourceNode26_3

theorem sourceNode30_2 : (data.drop 30).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 30).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 30 1 1 binding30 binding31

theorem sourceNode29_3 : (data.drop 29).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 29).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 29 1 2 binding29 sourceNode30_2

theorem sourceNode33_2 : (data.drop 33).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 33).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 33 1 1 binding33 binding34

theorem sourceNode32_3 : (data.drop 32).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 1 2 binding32 sourceNode33_2

theorem sourceNode29_6 : (data.drop 29).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 29).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 29 3 3 sourceNode29_3 sourceNode32_3

theorem sourceNode23_12 : (data.drop 23).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 23).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 23 6 6 sourceNode23_6 sourceNode29_6

theorem sourceNode36_2 : (data.drop 36).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 36).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 36 1 1 binding36 binding37

theorem sourceNode35_3 : (data.drop 35).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 35).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 35 1 2 binding35 sourceNode36_2

theorem sourceNode39_2 : (data.drop 39).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 39).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 39 1 1 binding39 binding40

theorem sourceNode38_3 : (data.drop 38).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 38).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 38 1 2 binding38 sourceNode39_2

theorem sourceNode35_6 : (data.drop 35).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 35).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 35 3 3 sourceNode35_3 sourceNode38_3

theorem sourceNode42_2 : (data.drop 42).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 42).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 42 1 1 binding42 binding43

theorem sourceNode41_3 : (data.drop 41).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 41).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 41 1 2 binding41 sourceNode42_2

theorem sourceNode45_2 : (data.drop 45).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 45).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 45 1 1 binding45 binding46

theorem sourceNode44_3 : (data.drop 44).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 44 1 2 binding44 sourceNode45_2

theorem sourceNode41_6 : (data.drop 41).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 41).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 41 3 3 sourceNode41_3 sourceNode44_3

theorem sourceNode35_12 : (data.drop 35).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 35).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 35 6 6 sourceNode35_6 sourceNode41_6

theorem sourceNode23_24 : (data.drop 23).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 23).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 23 12 12 sourceNode23_12 sourceNode35_12

theorem sourceNode0_47 : (data.drop 0).take 47 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 47 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 23 24 sourceNode0_23 sourceNode23_24

theorem sourceNode48_2 : (data.drop 48).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 48).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 48 1 1 binding48 binding49

theorem sourceNode47_3 : (data.drop 47).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 47).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 47 1 2 binding47 sourceNode48_2

theorem sourceNode51_2 : (data.drop 51).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 51).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 51 1 1 binding51 binding52

theorem sourceNode50_3 : (data.drop 50).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 50).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 50 1 2 binding50 sourceNode51_2

theorem sourceNode47_6 : (data.drop 47).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 47).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 47 3 3 sourceNode47_3 sourceNode50_3

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

theorem sourceNode47_12 : (data.drop 47).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 47).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 47 6 6 sourceNode47_6 sourceNode53_6

theorem sourceNode60_2 : (data.drop 60).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 60).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 60 1 1 binding60 binding61

theorem sourceNode59_3 : (data.drop 59).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 59).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 59 1 2 binding59 sourceNode60_2

theorem sourceNode63_2 : (data.drop 63).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 63).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 63 1 1 binding63 binding64

theorem sourceNode62_3 : (data.drop 62).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 62).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 62 1 2 binding62 sourceNode63_2

theorem sourceNode59_6 : (data.drop 59).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 59).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 59 3 3 sourceNode59_3 sourceNode62_3

theorem sourceNode66_2 : (data.drop 66).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 66).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 66 1 1 binding66 binding67

theorem sourceNode65_3 : (data.drop 65).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 65).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 65 1 2 binding65 sourceNode66_2

theorem sourceNode69_2 : (data.drop 69).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 69).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 69 1 1 binding69 binding70

theorem sourceNode68_3 : (data.drop 68).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 68).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 68 1 2 binding68 sourceNode69_2

theorem sourceNode65_6 : (data.drop 65).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 65).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 65 3 3 sourceNode65_3 sourceNode68_3

theorem sourceNode59_12 : (data.drop 59).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 59).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 59 6 6 sourceNode59_6 sourceNode65_6

theorem sourceNode47_24 : (data.drop 47).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 47).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 47 12 12 sourceNode47_12 sourceNode59_12

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

theorem sourceNode71_12 : (data.drop 71).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 71).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 71 6 6 sourceNode71_6 sourceNode77_6

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

theorem sourceNode90_2 : (data.drop 90).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 90).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 90 1 1 binding90 binding91

theorem sourceNode89_3 : (data.drop 89).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 89).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 89 1 2 binding89 sourceNode90_2

theorem sourceNode93_2 : (data.drop 93).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 93).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 93 1 1 binding93 binding94

theorem sourceNode92_3 : (data.drop 92).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 92).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 92 1 2 binding92 sourceNode93_2

theorem sourceNode89_6 : (data.drop 89).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 89).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 89 3 3 sourceNode89_3 sourceNode92_3

theorem sourceNode83_12 : (data.drop 83).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 83).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 83 6 6 sourceNode83_6 sourceNode89_6

theorem sourceNode71_24 : (data.drop 71).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 71).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 71 12 12 sourceNode71_12 sourceNode83_12

theorem sourceNode47_48 : (data.drop 47).take 48 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 47).take 48 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 47 24 24 sourceNode47_24 sourceNode71_24

theorem sourceNode0_95 : (data.drop 0).take 95 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 95 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 47 48 sourceNode0_47 sourceNode47_48

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 95
    (by decide +kernel) (by decide +kernel) sourceNode0_95

end Airbender.Compiler.FunctionalBaseChecks.BlakeRoundCached
