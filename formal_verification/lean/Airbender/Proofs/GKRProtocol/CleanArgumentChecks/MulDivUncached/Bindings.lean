import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.MulDivUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.CleanArgumentChecks.MulDivUncached
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

theorem sourceNode77_2 : (data.drop 77).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 77).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 77 1 1 binding77 binding78

theorem sourceNode80_2 : (data.drop 80).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 80 1 1 binding80 binding81

theorem sourceNode79_3 : (data.drop 79).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 79).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 79 1 2 binding79 sourceNode80_2

theorem sourceNode77_5 : (data.drop 77).take 5 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 77).take 5 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 77 2 3 sourceNode77_2 sourceNode79_3

theorem sourceNode83_2 : (data.drop 83).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 83).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 83 1 1 binding83 binding84

theorem sourceNode82_3 : (data.drop 82).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 82).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 82 1 2 binding82 sourceNode83_2

theorem sourceNode86_2 : (data.drop 86).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 86).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 86 1 1 binding86 binding87

theorem sourceNode85_3 : (data.drop 85).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 85).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 85 1 2 binding85 sourceNode86_2

theorem sourceNode82_6 : (data.drop 82).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 82).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 82 3 3 sourceNode82_3 sourceNode85_3

theorem sourceNode77_11 : (data.drop 77).take 11 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 77).take 11 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 77 5 6 sourceNode77_5 sourceNode82_6

theorem sourceNode66_22 : (data.drop 66).take 22 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 66).take 22 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 66 11 11 sourceNode66_11 sourceNode77_11

theorem sourceNode44_44 : (data.drop 44).take 44 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 44 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 44 22 22 sourceNode44_22 sourceNode66_22

theorem sourceNode0_88 : (data.drop 0).take 88 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 88 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 44 44 sourceNode0_44 sourceNode44_44

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 88
    (by decide +kernel) (by decide +kernel) sourceNode0_88

end Airbender.Compiler.CleanArgumentChecks.MulDivUncached
