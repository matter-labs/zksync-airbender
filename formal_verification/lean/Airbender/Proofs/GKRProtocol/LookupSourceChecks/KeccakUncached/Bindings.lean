import Airbender.Proofs.GKRProtocol.LookupSourceChecks.KeccakUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.LookupSourceChecks.KeccakUncached
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

numeric_data_binding view356 : (data.drop 356).take 1 = (data352.drop 4).take 1

numeric_data_binding piece356 : (data352.drop 4).take 1 = ((originalEntries.drop 356).take 1).map NumericFunctionalBaseChecks.encode

theorem binding356 : (data.drop 356).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 356).take 1 :=
  view356.trans (piece356.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 356 1))

numeric_data_binding view357 : (data.drop 357).take 1 = (data352.drop 5).take 1

numeric_data_binding piece357 : (data352.drop 5).take 1 = ((originalEntries.drop 357).take 1).map NumericFunctionalBaseChecks.encode

theorem binding357 : (data.drop 357).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 357).take 1 :=
  view357.trans (piece357.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 357 1))

numeric_data_binding view358 : (data.drop 358).take 1 = (data352.drop 6).take 1

numeric_data_binding piece358 : (data352.drop 6).take 1 = ((originalEntries.drop 358).take 1).map NumericFunctionalBaseChecks.encode

theorem binding358 : (data.drop 358).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 358).take 1 :=
  view358.trans (piece358.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 358 1))

numeric_data_binding view359 : (data.drop 359).take 1 = (data352.drop 7).take 1

numeric_data_binding piece359 : (data352.drop 7).take 1 = ((originalEntries.drop 359).take 1).map NumericFunctionalBaseChecks.encode

theorem binding359 : (data.drop 359).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 359).take 1 :=
  view359.trans (piece359.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 359 1))

numeric_data_binding view360 : (data.drop 360).take 1 = (data360.drop 0).take 1

numeric_data_binding piece360 : (data360.drop 0).take 1 = ((originalEntries.drop 360).take 1).map NumericFunctionalBaseChecks.encode

theorem binding360 : (data.drop 360).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 360).take 1 :=
  view360.trans (piece360.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 360 1))

numeric_data_binding view361 : (data.drop 361).take 1 = (data360.drop 1).take 1

numeric_data_binding piece361 : (data360.drop 1).take 1 = ((originalEntries.drop 361).take 1).map NumericFunctionalBaseChecks.encode

theorem binding361 : (data.drop 361).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 361).take 1 :=
  view361.trans (piece361.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 361 1))

numeric_data_binding view362 : (data.drop 362).take 1 = (data360.drop 2).take 1

numeric_data_binding piece362 : (data360.drop 2).take 1 = ((originalEntries.drop 362).take 1).map NumericFunctionalBaseChecks.encode

theorem binding362 : (data.drop 362).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 362).take 1 :=
  view362.trans (piece362.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 362 1))

numeric_data_binding view363 : (data.drop 363).take 1 = (data360.drop 3).take 1

numeric_data_binding piece363 : (data360.drop 3).take 1 = ((originalEntries.drop 363).take 1).map NumericFunctionalBaseChecks.encode

theorem binding363 : (data.drop 363).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 363).take 1 :=
  view363.trans (piece363.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 363 1))

numeric_data_binding view364 : (data.drop 364).take 1 = (data360.drop 4).take 1

numeric_data_binding piece364 : (data360.drop 4).take 1 = ((originalEntries.drop 364).take 1).map NumericFunctionalBaseChecks.encode

theorem binding364 : (data.drop 364).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 364).take 1 :=
  view364.trans (piece364.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 364 1))

numeric_data_binding view365 : (data.drop 365).take 1 = (data360.drop 5).take 1

numeric_data_binding piece365 : (data360.drop 5).take 1 = ((originalEntries.drop 365).take 1).map NumericFunctionalBaseChecks.encode

theorem binding365 : (data.drop 365).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 365).take 1 :=
  view365.trans (piece365.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 365 1))

numeric_data_binding view366 : (data.drop 366).take 1 = (data360.drop 6).take 1

numeric_data_binding piece366 : (data360.drop 6).take 1 = ((originalEntries.drop 366).take 1).map NumericFunctionalBaseChecks.encode

theorem binding366 : (data.drop 366).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 366).take 1 :=
  view366.trans (piece366.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 366 1))

numeric_data_binding view367 : (data.drop 367).take 1 = (data360.drop 7).take 1

numeric_data_binding piece367 : (data360.drop 7).take 1 = ((originalEntries.drop 367).take 1).map NumericFunctionalBaseChecks.encode

theorem binding367 : (data.drop 367).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 367).take 1 :=
  view367.trans (piece367.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 367 1))

numeric_data_binding view368 : (data.drop 368).take 1 = (data368.drop 0).take 1

numeric_data_binding piece368 : (data368.drop 0).take 1 = ((originalEntries.drop 368).take 1).map NumericFunctionalBaseChecks.encode

theorem binding368 : (data.drop 368).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 368).take 1 :=
  view368.trans (piece368.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 368 1))

numeric_data_binding view369 : (data.drop 369).take 1 = (data368.drop 1).take 1

numeric_data_binding piece369 : (data368.drop 1).take 1 = ((originalEntries.drop 369).take 1).map NumericFunctionalBaseChecks.encode

theorem binding369 : (data.drop 369).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 369).take 1 :=
  view369.trans (piece369.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 369 1))

numeric_data_binding view370 : (data.drop 370).take 1 = (data368.drop 2).take 1

numeric_data_binding piece370 : (data368.drop 2).take 1 = ((originalEntries.drop 370).take 1).map NumericFunctionalBaseChecks.encode

theorem binding370 : (data.drop 370).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 370).take 1 :=
  view370.trans (piece370.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 370 1))

numeric_data_binding view371 : (data.drop 371).take 1 = (data368.drop 3).take 1

numeric_data_binding piece371 : (data368.drop 3).take 1 = ((originalEntries.drop 371).take 1).map NumericFunctionalBaseChecks.encode

theorem binding371 : (data.drop 371).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 371).take 1 :=
  view371.trans (piece371.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 371 1))

numeric_data_binding view372 : (data.drop 372).take 1 = (data368.drop 4).take 1

numeric_data_binding piece372 : (data368.drop 4).take 1 = ((originalEntries.drop 372).take 1).map NumericFunctionalBaseChecks.encode

theorem binding372 : (data.drop 372).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 372).take 1 :=
  view372.trans (piece372.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 372 1))

numeric_data_binding view373 : (data.drop 373).take 1 = (data368.drop 5).take 1

numeric_data_binding piece373 : (data368.drop 5).take 1 = ((originalEntries.drop 373).take 1).map NumericFunctionalBaseChecks.encode

theorem binding373 : (data.drop 373).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 373).take 1 :=
  view373.trans (piece373.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 373 1))

numeric_data_binding view374 : (data.drop 374).take 1 = (data368.drop 6).take 1

numeric_data_binding piece374 : (data368.drop 6).take 1 = ((originalEntries.drop 374).take 1).map NumericFunctionalBaseChecks.encode

theorem binding374 : (data.drop 374).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 374).take 1 :=
  view374.trans (piece374.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 374 1))

numeric_data_binding view375 : (data.drop 375).take 1 = (data368.drop 7).take 1

numeric_data_binding piece375 : (data368.drop 7).take 1 = ((originalEntries.drop 375).take 1).map NumericFunctionalBaseChecks.encode

theorem binding375 : (data.drop 375).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 375).take 1 :=
  view375.trans (piece375.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 375 1))

numeric_data_binding view376 : (data.drop 376).take 1 = (data376.drop 0).take 1

numeric_data_binding piece376 : (data376.drop 0).take 1 = ((originalEntries.drop 376).take 1).map NumericFunctionalBaseChecks.encode

theorem binding376 : (data.drop 376).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 376).take 1 :=
  view376.trans (piece376.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 376 1))

numeric_data_binding view377 : (data.drop 377).take 1 = (data376.drop 1).take 1

numeric_data_binding piece377 : (data376.drop 1).take 1 = ((originalEntries.drop 377).take 1).map NumericFunctionalBaseChecks.encode

theorem binding377 : (data.drop 377).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 377).take 1 :=
  view377.trans (piece377.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 377 1))

numeric_data_binding view378 : (data.drop 378).take 1 = (data376.drop 2).take 1

numeric_data_binding piece378 : (data376.drop 2).take 1 = ((originalEntries.drop 378).take 1).map NumericFunctionalBaseChecks.encode

theorem binding378 : (data.drop 378).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 378).take 1 :=
  view378.trans (piece378.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 378 1))

numeric_data_binding view379 : (data.drop 379).take 1 = (data376.drop 3).take 1

numeric_data_binding piece379 : (data376.drop 3).take 1 = ((originalEntries.drop 379).take 1).map NumericFunctionalBaseChecks.encode

theorem binding379 : (data.drop 379).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 379).take 1 :=
  view379.trans (piece379.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 379 1))

numeric_data_binding view380 : (data.drop 380).take 1 = (data376.drop 4).take 1

numeric_data_binding piece380 : (data376.drop 4).take 1 = ((originalEntries.drop 380).take 1).map NumericFunctionalBaseChecks.encode

theorem binding380 : (data.drop 380).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 380).take 1 :=
  view380.trans (piece380.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 380 1))

numeric_data_binding view381 : (data.drop 381).take 1 = (data376.drop 5).take 1

numeric_data_binding piece381 : (data376.drop 5).take 1 = ((originalEntries.drop 381).take 1).map NumericFunctionalBaseChecks.encode

theorem binding381 : (data.drop 381).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 381).take 1 :=
  view381.trans (piece381.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 381 1))

numeric_data_binding view382 : (data.drop 382).take 1 = (data376.drop 6).take 1

numeric_data_binding piece382 : (data376.drop 6).take 1 = ((originalEntries.drop 382).take 1).map NumericFunctionalBaseChecks.encode

theorem binding382 : (data.drop 382).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 382).take 1 :=
  view382.trans (piece382.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 382 1))

numeric_data_binding view383 : (data.drop 383).take 1 = (data376.drop 7).take 1

numeric_data_binding piece383 : (data376.drop 7).take 1 = ((originalEntries.drop 383).take 1).map NumericFunctionalBaseChecks.encode

theorem binding383 : (data.drop 383).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 383).take 1 :=
  view383.trans (piece383.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 383 1))

numeric_data_binding view384 : (data.drop 384).take 1 = (data384.drop 0).take 1

numeric_data_binding piece384 : (data384.drop 0).take 1 = ((originalEntries.drop 384).take 1).map NumericFunctionalBaseChecks.encode

theorem binding384 : (data.drop 384).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 384).take 1 :=
  view384.trans (piece384.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 384 1))

numeric_data_binding view385 : (data.drop 385).take 1 = (data384.drop 1).take 1

numeric_data_binding piece385 : (data384.drop 1).take 1 = ((originalEntries.drop 385).take 1).map NumericFunctionalBaseChecks.encode

theorem binding385 : (data.drop 385).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 385).take 1 :=
  view385.trans (piece385.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 385 1))

numeric_data_binding view386 : (data.drop 386).take 1 = (data384.drop 2).take 1

numeric_data_binding piece386 : (data384.drop 2).take 1 = ((originalEntries.drop 386).take 1).map NumericFunctionalBaseChecks.encode

theorem binding386 : (data.drop 386).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 386).take 1 :=
  view386.trans (piece386.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 386 1))

numeric_data_binding view387 : (data.drop 387).take 1 = (data384.drop 3).take 1

numeric_data_binding piece387 : (data384.drop 3).take 1 = ((originalEntries.drop 387).take 1).map NumericFunctionalBaseChecks.encode

theorem binding387 : (data.drop 387).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 387).take 1 :=
  view387.trans (piece387.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 387 1))

numeric_data_binding view388 : (data.drop 388).take 1 = (data384.drop 4).take 1

numeric_data_binding piece388 : (data384.drop 4).take 1 = ((originalEntries.drop 388).take 1).map NumericFunctionalBaseChecks.encode

theorem binding388 : (data.drop 388).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 388).take 1 :=
  view388.trans (piece388.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 388 1))

numeric_data_binding view389 : (data.drop 389).take 1 = (data384.drop 5).take 1

numeric_data_binding piece389 : (data384.drop 5).take 1 = ((originalEntries.drop 389).take 1).map NumericFunctionalBaseChecks.encode

theorem binding389 : (data.drop 389).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 389).take 1 :=
  view389.trans (piece389.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 389 1))

numeric_data_binding view390 : (data.drop 390).take 1 = (data384.drop 6).take 1

numeric_data_binding piece390 : (data384.drop 6).take 1 = ((originalEntries.drop 390).take 1).map NumericFunctionalBaseChecks.encode

theorem binding390 : (data.drop 390).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 390).take 1 :=
  view390.trans (piece390.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 390 1))

numeric_data_binding view391 : (data.drop 391).take 1 = (data384.drop 7).take 1

numeric_data_binding piece391 : (data384.drop 7).take 1 = ((originalEntries.drop 391).take 1).map NumericFunctionalBaseChecks.encode

theorem binding391 : (data.drop 391).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 391).take 1 :=
  view391.trans (piece391.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 391 1))

numeric_data_binding view392 : (data.drop 392).take 1 = (data392.drop 0).take 1

numeric_data_binding piece392 : (data392.drop 0).take 1 = ((originalEntries.drop 392).take 1).map NumericFunctionalBaseChecks.encode

theorem binding392 : (data.drop 392).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 392).take 1 :=
  view392.trans (piece392.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 392 1))

numeric_data_binding view393 : (data.drop 393).take 1 = (data392.drop 1).take 1

numeric_data_binding piece393 : (data392.drop 1).take 1 = ((originalEntries.drop 393).take 1).map NumericFunctionalBaseChecks.encode

theorem binding393 : (data.drop 393).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 393).take 1 :=
  view393.trans (piece393.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 393 1))

numeric_data_binding view394 : (data.drop 394).take 1 = (data392.drop 2).take 1

numeric_data_binding piece394 : (data392.drop 2).take 1 = ((originalEntries.drop 394).take 1).map NumericFunctionalBaseChecks.encode

theorem binding394 : (data.drop 394).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 394).take 1 :=
  view394.trans (piece394.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 394 1))

numeric_data_binding view395 : (data.drop 395).take 1 = (data392.drop 3).take 1

numeric_data_binding piece395 : (data392.drop 3).take 1 = ((originalEntries.drop 395).take 1).map NumericFunctionalBaseChecks.encode

theorem binding395 : (data.drop 395).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 395).take 1 :=
  view395.trans (piece395.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 395 1))

numeric_data_binding view396 : (data.drop 396).take 1 = (data392.drop 4).take 1

numeric_data_binding piece396 : (data392.drop 4).take 1 = ((originalEntries.drop 396).take 1).map NumericFunctionalBaseChecks.encode

theorem binding396 : (data.drop 396).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 396).take 1 :=
  view396.trans (piece396.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 396 1))

numeric_data_binding view397 : (data.drop 397).take 1 = (data392.drop 5).take 1

numeric_data_binding piece397 : (data392.drop 5).take 1 = ((originalEntries.drop 397).take 1).map NumericFunctionalBaseChecks.encode

theorem binding397 : (data.drop 397).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 397).take 1 :=
  view397.trans (piece397.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 397 1))

numeric_data_binding view398 : (data.drop 398).take 1 = (data392.drop 6).take 1

numeric_data_binding piece398 : (data392.drop 6).take 1 = ((originalEntries.drop 398).take 1).map NumericFunctionalBaseChecks.encode

theorem binding398 : (data.drop 398).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 398).take 1 :=
  view398.trans (piece398.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 398 1))

numeric_data_binding view399 : (data.drop 399).take 1 = (data392.drop 7).take 1

numeric_data_binding piece399 : (data392.drop 7).take 1 = ((originalEntries.drop 399).take 1).map NumericFunctionalBaseChecks.encode

theorem binding399 : (data.drop 399).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 399).take 1 :=
  view399.trans (piece399.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 399 1))

numeric_data_binding view400 : (data.drop 400).take 1 = (data400.drop 0).take 1

numeric_data_binding piece400 : (data400.drop 0).take 1 = ((originalEntries.drop 400).take 1).map NumericFunctionalBaseChecks.encode

theorem binding400 : (data.drop 400).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 400).take 1 :=
  view400.trans (piece400.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 400 1))

numeric_data_binding view401 : (data.drop 401).take 1 = (data400.drop 1).take 1

numeric_data_binding piece401 : (data400.drop 1).take 1 = ((originalEntries.drop 401).take 1).map NumericFunctionalBaseChecks.encode

theorem binding401 : (data.drop 401).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 401).take 1 :=
  view401.trans (piece401.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 401 1))

numeric_data_binding view402 : (data.drop 402).take 1 = (data400.drop 2).take 1

numeric_data_binding piece402 : (data400.drop 2).take 1 = ((originalEntries.drop 402).take 1).map NumericFunctionalBaseChecks.encode

theorem binding402 : (data.drop 402).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 402).take 1 :=
  view402.trans (piece402.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 402 1))

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

theorem sourceNode10_2 : (data.drop 10).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 10).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 10 1 1 binding10 binding11

theorem sourceNode9_3 : (data.drop 9).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 9).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 9 1 2 binding9 sourceNode10_2

theorem sourceNode6_6 : (data.drop 6).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 6).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 6 3 3 sourceNode6_3 sourceNode9_3

theorem sourceNode0_12 : (data.drop 0).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 6 6 sourceNode0_6 sourceNode6_6

theorem sourceNode13_2 : (data.drop 13).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 13).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 13 1 1 binding13 binding14

theorem sourceNode12_3 : (data.drop 12).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 12).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 12 1 2 binding12 sourceNode13_2

theorem sourceNode16_2 : (data.drop 16).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 16 1 1 binding16 binding17

theorem sourceNode15_3 : (data.drop 15).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 15).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 15 1 2 binding15 sourceNode16_2

theorem sourceNode12_6 : (data.drop 12).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 12).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 12 3 3 sourceNode12_3 sourceNode15_3

theorem sourceNode19_2 : (data.drop 19).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 19).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 19 1 1 binding19 binding20

theorem sourceNode18_3 : (data.drop 18).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 18).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 18 1 2 binding18 sourceNode19_2

theorem sourceNode21_2 : (data.drop 21).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 21).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 21 1 1 binding21 binding22

theorem sourceNode23_2 : (data.drop 23).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 23).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 23 1 1 binding23 binding24

theorem sourceNode21_4 : (data.drop 21).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 21).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 21 2 2 sourceNode21_2 sourceNode23_2

theorem sourceNode18_7 : (data.drop 18).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 18).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 18 3 4 sourceNode18_3 sourceNode21_4

theorem sourceNode12_13 : (data.drop 12).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 12).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 12 6 7 sourceNode12_6 sourceNode18_7

theorem sourceNode0_25 : (data.drop 0).take 25 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 25 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 12 13 sourceNode0_12 sourceNode12_13

theorem sourceNode26_2 : (data.drop 26).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 26).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 26 1 1 binding26 binding27

theorem sourceNode25_3 : (data.drop 25).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 25).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 25 1 2 binding25 sourceNode26_2

theorem sourceNode29_2 : (data.drop 29).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 29).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 29 1 1 binding29 binding30

theorem sourceNode28_3 : (data.drop 28).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 28).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 28 1 2 binding28 sourceNode29_2

theorem sourceNode25_6 : (data.drop 25).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 25).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 25 3 3 sourceNode25_3 sourceNode28_3

theorem sourceNode32_2 : (data.drop 32).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 1 1 binding32 binding33

theorem sourceNode31_3 : (data.drop 31).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 31).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 31 1 2 binding31 sourceNode32_2

theorem sourceNode35_2 : (data.drop 35).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 35).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 35 1 1 binding35 binding36

theorem sourceNode34_3 : (data.drop 34).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 34).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 34 1 2 binding34 sourceNode35_2

theorem sourceNode31_6 : (data.drop 31).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 31).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 31 3 3 sourceNode31_3 sourceNode34_3

theorem sourceNode25_12 : (data.drop 25).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 25).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 25 6 6 sourceNode25_6 sourceNode31_6

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

theorem sourceNode44_2 : (data.drop 44).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 44).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 44 1 1 binding44 binding45

theorem sourceNode43_3 : (data.drop 43).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 43).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 43 1 2 binding43 sourceNode44_2

theorem sourceNode46_2 : (data.drop 46).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 46).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 46 1 1 binding46 binding47

theorem sourceNode48_2 : (data.drop 48).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 48).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 48 1 1 binding48 binding49

theorem sourceNode46_4 : (data.drop 46).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 46).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 46 2 2 sourceNode46_2 sourceNode48_2

theorem sourceNode43_7 : (data.drop 43).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 43).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 43 3 4 sourceNode43_3 sourceNode46_4

theorem sourceNode37_13 : (data.drop 37).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 37).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 37 6 7 sourceNode37_6 sourceNode43_7

theorem sourceNode25_25 : (data.drop 25).take 25 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 25).take 25 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 25 12 13 sourceNode25_12 sourceNode37_13

theorem sourceNode0_50 : (data.drop 0).take 50 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 50 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 25 25 sourceNode0_25 sourceNode25_25

theorem sourceNode51_2 : (data.drop 51).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 51).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 51 1 1 binding51 binding52

theorem sourceNode50_3 : (data.drop 50).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 50).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 50 1 2 binding50 sourceNode51_2

theorem sourceNode54_2 : (data.drop 54).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 54).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 54 1 1 binding54 binding55

theorem sourceNode53_3 : (data.drop 53).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 53).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 53 1 2 binding53 sourceNode54_2

theorem sourceNode50_6 : (data.drop 50).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 50).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 50 3 3 sourceNode50_3 sourceNode53_3

theorem sourceNode57_2 : (data.drop 57).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 57).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 57 1 1 binding57 binding58

theorem sourceNode56_3 : (data.drop 56).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 56).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 56 1 2 binding56 sourceNode57_2

theorem sourceNode60_2 : (data.drop 60).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 60).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 60 1 1 binding60 binding61

theorem sourceNode59_3 : (data.drop 59).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 59).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 59 1 2 binding59 sourceNode60_2

theorem sourceNode56_6 : (data.drop 56).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 56).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 56 3 3 sourceNode56_3 sourceNode59_3

theorem sourceNode50_12 : (data.drop 50).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 50).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 50 6 6 sourceNode50_6 sourceNode56_6

theorem sourceNode63_2 : (data.drop 63).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 63).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 63 1 1 binding63 binding64

theorem sourceNode62_3 : (data.drop 62).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 62).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 62 1 2 binding62 sourceNode63_2

theorem sourceNode66_2 : (data.drop 66).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 66).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 66 1 1 binding66 binding67

theorem sourceNode65_3 : (data.drop 65).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 65).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 65 1 2 binding65 sourceNode66_2

theorem sourceNode62_6 : (data.drop 62).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 62).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 62 3 3 sourceNode62_3 sourceNode65_3

theorem sourceNode69_2 : (data.drop 69).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 69).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 69 1 1 binding69 binding70

theorem sourceNode68_3 : (data.drop 68).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 68).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 68 1 2 binding68 sourceNode69_2

theorem sourceNode71_2 : (data.drop 71).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 71).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 71 1 1 binding71 binding72

theorem sourceNode73_2 : (data.drop 73).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 73).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 73 1 1 binding73 binding74

theorem sourceNode71_4 : (data.drop 71).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 71).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 71 2 2 sourceNode71_2 sourceNode73_2

theorem sourceNode68_7 : (data.drop 68).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 68).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 68 3 4 sourceNode68_3 sourceNode71_4

theorem sourceNode62_13 : (data.drop 62).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 62).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 62 6 7 sourceNode62_6 sourceNode68_7

theorem sourceNode50_25 : (data.drop 50).take 25 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 50).take 25 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 50 12 13 sourceNode50_12 sourceNode62_13

theorem sourceNode76_2 : (data.drop 76).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 76).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 76 1 1 binding76 binding77

theorem sourceNode75_3 : (data.drop 75).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 75).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 75 1 2 binding75 sourceNode76_2

theorem sourceNode79_2 : (data.drop 79).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 79).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 79 1 1 binding79 binding80

theorem sourceNode78_3 : (data.drop 78).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 78).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 78 1 2 binding78 sourceNode79_2

theorem sourceNode75_6 : (data.drop 75).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 75).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 75 3 3 sourceNode75_3 sourceNode78_3

theorem sourceNode82_2 : (data.drop 82).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 82).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 82 1 1 binding82 binding83

theorem sourceNode81_3 : (data.drop 81).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 81).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 81 1 2 binding81 sourceNode82_2

theorem sourceNode85_2 : (data.drop 85).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 85).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 85 1 1 binding85 binding86

theorem sourceNode84_3 : (data.drop 84).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 84).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 84 1 2 binding84 sourceNode85_2

theorem sourceNode81_6 : (data.drop 81).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 81).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 81 3 3 sourceNode81_3 sourceNode84_3

theorem sourceNode75_12 : (data.drop 75).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 75).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 75 6 6 sourceNode75_6 sourceNode81_6

theorem sourceNode88_2 : (data.drop 88).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 88).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 88 1 1 binding88 binding89

theorem sourceNode87_3 : (data.drop 87).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 87).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 87 1 2 binding87 sourceNode88_2

theorem sourceNode91_2 : (data.drop 91).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 91).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 91 1 1 binding91 binding92

theorem sourceNode90_3 : (data.drop 90).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 90).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 90 1 2 binding90 sourceNode91_2

theorem sourceNode87_6 : (data.drop 87).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 87).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 87 3 3 sourceNode87_3 sourceNode90_3

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

theorem sourceNode87_13 : (data.drop 87).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 87).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 87 6 7 sourceNode87_6 sourceNode93_7

theorem sourceNode75_25 : (data.drop 75).take 25 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 75).take 25 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 75 12 13 sourceNode75_12 sourceNode87_13

theorem sourceNode50_50 : (data.drop 50).take 50 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 50).take 50 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 50 25 25 sourceNode50_25 sourceNode75_25

theorem sourceNode0_100 : (data.drop 0).take 100 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 100 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 50 50 sourceNode0_50 sourceNode50_50

theorem sourceNode101_2 : (data.drop 101).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 101).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 101 1 1 binding101 binding102

theorem sourceNode100_3 : (data.drop 100).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 100).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 100 1 2 binding100 sourceNode101_2

theorem sourceNode104_2 : (data.drop 104).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 104).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 104 1 1 binding104 binding105

theorem sourceNode103_3 : (data.drop 103).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 103).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 103 1 2 binding103 sourceNode104_2

theorem sourceNode100_6 : (data.drop 100).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 100).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 100 3 3 sourceNode100_3 sourceNode103_3

theorem sourceNode107_2 : (data.drop 107).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 107).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 107 1 1 binding107 binding108

theorem sourceNode106_3 : (data.drop 106).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 106).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 106 1 2 binding106 sourceNode107_2

theorem sourceNode110_2 : (data.drop 110).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 110).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 110 1 1 binding110 binding111

theorem sourceNode109_3 : (data.drop 109).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 109).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 109 1 2 binding109 sourceNode110_2

theorem sourceNode106_6 : (data.drop 106).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 106).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 106 3 3 sourceNode106_3 sourceNode109_3

theorem sourceNode100_12 : (data.drop 100).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 100).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 100 6 6 sourceNode100_6 sourceNode106_6

theorem sourceNode113_2 : (data.drop 113).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 113).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 113 1 1 binding113 binding114

theorem sourceNode112_3 : (data.drop 112).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 112).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 112 1 2 binding112 sourceNode113_2

theorem sourceNode116_2 : (data.drop 116).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 116).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 116 1 1 binding116 binding117

theorem sourceNode115_3 : (data.drop 115).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 115).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 115 1 2 binding115 sourceNode116_2

theorem sourceNode112_6 : (data.drop 112).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 112).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 112 3 3 sourceNode112_3 sourceNode115_3

theorem sourceNode119_2 : (data.drop 119).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 119).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 119 1 1 binding119 binding120

theorem sourceNode118_3 : (data.drop 118).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 118).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 118 1 2 binding118 sourceNode119_2

theorem sourceNode121_2 : (data.drop 121).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 121).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 121 1 1 binding121 binding122

theorem sourceNode123_2 : (data.drop 123).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 123).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 123 1 1 binding123 binding124

theorem sourceNode121_4 : (data.drop 121).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 121).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 121 2 2 sourceNode121_2 sourceNode123_2

theorem sourceNode118_7 : (data.drop 118).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 118).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 118 3 4 sourceNode118_3 sourceNode121_4

theorem sourceNode112_13 : (data.drop 112).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 112).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 112 6 7 sourceNode112_6 sourceNode118_7

theorem sourceNode100_25 : (data.drop 100).take 25 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 100).take 25 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 100 12 13 sourceNode100_12 sourceNode112_13

theorem sourceNode126_2 : (data.drop 126).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 126).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 126 1 1 binding126 binding127

theorem sourceNode125_3 : (data.drop 125).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 125).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 125 1 2 binding125 sourceNode126_2

theorem sourceNode129_2 : (data.drop 129).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 129).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 129 1 1 binding129 binding130

theorem sourceNode128_3 : (data.drop 128).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 128).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 128 1 2 binding128 sourceNode129_2

theorem sourceNode125_6 : (data.drop 125).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 125).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 125 3 3 sourceNode125_3 sourceNode128_3

theorem sourceNode132_2 : (data.drop 132).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 132).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 132 1 1 binding132 binding133

theorem sourceNode131_3 : (data.drop 131).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 131).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 131 1 2 binding131 sourceNode132_2

theorem sourceNode135_2 : (data.drop 135).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 135).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 135 1 1 binding135 binding136

theorem sourceNode134_3 : (data.drop 134).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 134).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 134 1 2 binding134 sourceNode135_2

theorem sourceNode131_6 : (data.drop 131).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 131).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 131 3 3 sourceNode131_3 sourceNode134_3

theorem sourceNode125_12 : (data.drop 125).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 125).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 125 6 6 sourceNode125_6 sourceNode131_6

theorem sourceNode138_2 : (data.drop 138).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 138).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 138 1 1 binding138 binding139

theorem sourceNode137_3 : (data.drop 137).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 137).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 137 1 2 binding137 sourceNode138_2

theorem sourceNode141_2 : (data.drop 141).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 141).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 141 1 1 binding141 binding142

theorem sourceNode140_3 : (data.drop 140).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 140).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 140 1 2 binding140 sourceNode141_2

theorem sourceNode137_6 : (data.drop 137).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 137).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 137 3 3 sourceNode137_3 sourceNode140_3

theorem sourceNode144_2 : (data.drop 144).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 144).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 144 1 1 binding144 binding145

theorem sourceNode143_3 : (data.drop 143).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 143).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 143 1 2 binding143 sourceNode144_2

theorem sourceNode146_2 : (data.drop 146).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 146).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 146 1 1 binding146 binding147

theorem sourceNode148_2 : (data.drop 148).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 148).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 148 1 1 binding148 binding149

theorem sourceNode146_4 : (data.drop 146).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 146).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 146 2 2 sourceNode146_2 sourceNode148_2

theorem sourceNode143_7 : (data.drop 143).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 143).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 143 3 4 sourceNode143_3 sourceNode146_4

theorem sourceNode137_13 : (data.drop 137).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 137).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 137 6 7 sourceNode137_6 sourceNode143_7

theorem sourceNode125_25 : (data.drop 125).take 25 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 125).take 25 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 125 12 13 sourceNode125_12 sourceNode137_13

theorem sourceNode100_50 : (data.drop 100).take 50 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 100).take 50 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 100 25 25 sourceNode100_25 sourceNode125_25

theorem sourceNode151_2 : (data.drop 151).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 151).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 151 1 1 binding151 binding152

theorem sourceNode150_3 : (data.drop 150).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 150).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 150 1 2 binding150 sourceNode151_2

theorem sourceNode154_2 : (data.drop 154).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 154).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 154 1 1 binding154 binding155

theorem sourceNode153_3 : (data.drop 153).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 153).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 153 1 2 binding153 sourceNode154_2

theorem sourceNode150_6 : (data.drop 150).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 150).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 150 3 3 sourceNode150_3 sourceNode153_3

theorem sourceNode157_2 : (data.drop 157).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 157).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 157 1 1 binding157 binding158

theorem sourceNode156_3 : (data.drop 156).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 156).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 156 1 2 binding156 sourceNode157_2

theorem sourceNode160_2 : (data.drop 160).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 160).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 160 1 1 binding160 binding161

theorem sourceNode159_3 : (data.drop 159).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 159).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 159 1 2 binding159 sourceNode160_2

theorem sourceNode156_6 : (data.drop 156).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 156).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 156 3 3 sourceNode156_3 sourceNode159_3

theorem sourceNode150_12 : (data.drop 150).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 150).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 150 6 6 sourceNode150_6 sourceNode156_6

theorem sourceNode163_2 : (data.drop 163).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 163).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 163 1 1 binding163 binding164

theorem sourceNode162_3 : (data.drop 162).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 162).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 162 1 2 binding162 sourceNode163_2

theorem sourceNode166_2 : (data.drop 166).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 166).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 166 1 1 binding166 binding167

theorem sourceNode165_3 : (data.drop 165).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 165).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 165 1 2 binding165 sourceNode166_2

theorem sourceNode162_6 : (data.drop 162).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 162).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 162 3 3 sourceNode162_3 sourceNode165_3

theorem sourceNode169_2 : (data.drop 169).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 169).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 169 1 1 binding169 binding170

theorem sourceNode168_3 : (data.drop 168).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 168).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 168 1 2 binding168 sourceNode169_2

theorem sourceNode171_2 : (data.drop 171).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 171).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 171 1 1 binding171 binding172

theorem sourceNode173_2 : (data.drop 173).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 173).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 173 1 1 binding173 binding174

theorem sourceNode171_4 : (data.drop 171).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 171).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 171 2 2 sourceNode171_2 sourceNode173_2

theorem sourceNode168_7 : (data.drop 168).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 168).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 168 3 4 sourceNode168_3 sourceNode171_4

theorem sourceNode162_13 : (data.drop 162).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 162).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 162 6 7 sourceNode162_6 sourceNode168_7

theorem sourceNode150_25 : (data.drop 150).take 25 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 150).take 25 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 150 12 13 sourceNode150_12 sourceNode162_13

theorem sourceNode176_2 : (data.drop 176).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 176).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 176 1 1 binding176 binding177

theorem sourceNode175_3 : (data.drop 175).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 175).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 175 1 2 binding175 sourceNode176_2

theorem sourceNode179_2 : (data.drop 179).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 179).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 179 1 1 binding179 binding180

theorem sourceNode178_3 : (data.drop 178).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 178).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 178 1 2 binding178 sourceNode179_2

theorem sourceNode175_6 : (data.drop 175).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 175).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 175 3 3 sourceNode175_3 sourceNode178_3

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

theorem sourceNode175_13 : (data.drop 175).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 175).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 175 6 7 sourceNode175_6 sourceNode181_7

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

theorem sourceNode175_26 : (data.drop 175).take 26 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 175).take 26 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 175 13 13 sourceNode175_13 sourceNode188_13

theorem sourceNode150_51 : (data.drop 150).take 51 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 150).take 51 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 150 25 26 sourceNode150_25 sourceNode175_26

theorem sourceNode100_101 : (data.drop 100).take 101 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 100).take 101 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 100 50 51 sourceNode100_50 sourceNode150_51

theorem sourceNode0_201 : (data.drop 0).take 201 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 201 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 100 101 sourceNode0_100 sourceNode100_101

theorem sourceNode202_2 : (data.drop 202).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 202).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 202 1 1 binding202 binding203

theorem sourceNode201_3 : (data.drop 201).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 201).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 201 1 2 binding201 sourceNode202_2

theorem sourceNode205_2 : (data.drop 205).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 205).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 205 1 1 binding205 binding206

theorem sourceNode204_3 : (data.drop 204).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 204).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 204 1 2 binding204 sourceNode205_2

theorem sourceNode201_6 : (data.drop 201).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 201).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 201 3 3 sourceNode201_3 sourceNode204_3

theorem sourceNode208_2 : (data.drop 208).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 208).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 208 1 1 binding208 binding209

theorem sourceNode207_3 : (data.drop 207).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 207).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 207 1 2 binding207 sourceNode208_2

theorem sourceNode211_2 : (data.drop 211).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 211).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 211 1 1 binding211 binding212

theorem sourceNode210_3 : (data.drop 210).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 210).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 210 1 2 binding210 sourceNode211_2

theorem sourceNode207_6 : (data.drop 207).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 207).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 207 3 3 sourceNode207_3 sourceNode210_3

theorem sourceNode201_12 : (data.drop 201).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 201).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 201 6 6 sourceNode201_6 sourceNode207_6

theorem sourceNode214_2 : (data.drop 214).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 214).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 214 1 1 binding214 binding215

theorem sourceNode213_3 : (data.drop 213).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 213).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 213 1 2 binding213 sourceNode214_2

theorem sourceNode217_2 : (data.drop 217).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 217).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 217 1 1 binding217 binding218

theorem sourceNode216_3 : (data.drop 216).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 216).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 216 1 2 binding216 sourceNode217_2

theorem sourceNode213_6 : (data.drop 213).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 213).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 213 3 3 sourceNode213_3 sourceNode216_3

theorem sourceNode220_2 : (data.drop 220).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 220).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 220 1 1 binding220 binding221

theorem sourceNode219_3 : (data.drop 219).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 219).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 219 1 2 binding219 sourceNode220_2

theorem sourceNode222_2 : (data.drop 222).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 222).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 222 1 1 binding222 binding223

theorem sourceNode224_2 : (data.drop 224).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 224).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 224 1 1 binding224 binding225

theorem sourceNode222_4 : (data.drop 222).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 222).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 222 2 2 sourceNode222_2 sourceNode224_2

theorem sourceNode219_7 : (data.drop 219).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 219).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 219 3 4 sourceNode219_3 sourceNode222_4

theorem sourceNode213_13 : (data.drop 213).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 213).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 213 6 7 sourceNode213_6 sourceNode219_7

theorem sourceNode201_25 : (data.drop 201).take 25 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 201).take 25 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 201 12 13 sourceNode201_12 sourceNode213_13

theorem sourceNode227_2 : (data.drop 227).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 227).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 227 1 1 binding227 binding228

theorem sourceNode226_3 : (data.drop 226).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 226).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 226 1 2 binding226 sourceNode227_2

theorem sourceNode230_2 : (data.drop 230).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 230).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 230 1 1 binding230 binding231

theorem sourceNode229_3 : (data.drop 229).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 229).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 229 1 2 binding229 sourceNode230_2

theorem sourceNode226_6 : (data.drop 226).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 226).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 226 3 3 sourceNode226_3 sourceNode229_3

theorem sourceNode233_2 : (data.drop 233).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 233).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 233 1 1 binding233 binding234

theorem sourceNode232_3 : (data.drop 232).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 232).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 232 1 2 binding232 sourceNode233_2

theorem sourceNode236_2 : (data.drop 236).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 236).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 236 1 1 binding236 binding237

theorem sourceNode235_3 : (data.drop 235).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 235).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 235 1 2 binding235 sourceNode236_2

theorem sourceNode232_6 : (data.drop 232).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 232).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 232 3 3 sourceNode232_3 sourceNode235_3

theorem sourceNode226_12 : (data.drop 226).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 226).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 226 6 6 sourceNode226_6 sourceNode232_6

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

theorem sourceNode245_2 : (data.drop 245).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 245).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 245 1 1 binding245 binding246

theorem sourceNode244_3 : (data.drop 244).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 244).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 244 1 2 binding244 sourceNode245_2

theorem sourceNode247_2 : (data.drop 247).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 247).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 247 1 1 binding247 binding248

theorem sourceNode249_2 : (data.drop 249).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 249).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 249 1 1 binding249 binding250

theorem sourceNode247_4 : (data.drop 247).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 247).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 247 2 2 sourceNode247_2 sourceNode249_2

theorem sourceNode244_7 : (data.drop 244).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 244).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 244 3 4 sourceNode244_3 sourceNode247_4

theorem sourceNode238_13 : (data.drop 238).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 238).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 238 6 7 sourceNode238_6 sourceNode244_7

theorem sourceNode226_25 : (data.drop 226).take 25 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 226).take 25 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 226 12 13 sourceNode226_12 sourceNode238_13

theorem sourceNode201_50 : (data.drop 201).take 50 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 201).take 50 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 201 25 25 sourceNode201_25 sourceNode226_25

theorem sourceNode252_2 : (data.drop 252).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 252).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 252 1 1 binding252 binding253

theorem sourceNode251_3 : (data.drop 251).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 251).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 251 1 2 binding251 sourceNode252_2

theorem sourceNode255_2 : (data.drop 255).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 255).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 255 1 1 binding255 binding256

theorem sourceNode254_3 : (data.drop 254).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 254).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 254 1 2 binding254 sourceNode255_2

theorem sourceNode251_6 : (data.drop 251).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 251).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 251 3 3 sourceNode251_3 sourceNode254_3

theorem sourceNode258_2 : (data.drop 258).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 258).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 258 1 1 binding258 binding259

theorem sourceNode257_3 : (data.drop 257).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 257).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 257 1 2 binding257 sourceNode258_2

theorem sourceNode261_2 : (data.drop 261).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 261).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 261 1 1 binding261 binding262

theorem sourceNode260_3 : (data.drop 260).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 260).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 260 1 2 binding260 sourceNode261_2

theorem sourceNode257_6 : (data.drop 257).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 257).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 257 3 3 sourceNode257_3 sourceNode260_3

theorem sourceNode251_12 : (data.drop 251).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 251).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 251 6 6 sourceNode251_6 sourceNode257_6

theorem sourceNode264_2 : (data.drop 264).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 264).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 264 1 1 binding264 binding265

theorem sourceNode263_3 : (data.drop 263).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 263).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 263 1 2 binding263 sourceNode264_2

theorem sourceNode267_2 : (data.drop 267).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 267).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 267 1 1 binding267 binding268

theorem sourceNode266_3 : (data.drop 266).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 266).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 266 1 2 binding266 sourceNode267_2

theorem sourceNode263_6 : (data.drop 263).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 263).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 263 3 3 sourceNode263_3 sourceNode266_3

theorem sourceNode270_2 : (data.drop 270).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 270).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 270 1 1 binding270 binding271

theorem sourceNode269_3 : (data.drop 269).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 269).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 269 1 2 binding269 sourceNode270_2

theorem sourceNode272_2 : (data.drop 272).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 272).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 272 1 1 binding272 binding273

theorem sourceNode274_2 : (data.drop 274).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 274).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 274 1 1 binding274 binding275

theorem sourceNode272_4 : (data.drop 272).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 272).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 272 2 2 sourceNode272_2 sourceNode274_2

theorem sourceNode269_7 : (data.drop 269).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 269).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 269 3 4 sourceNode269_3 sourceNode272_4

theorem sourceNode263_13 : (data.drop 263).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 263).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 263 6 7 sourceNode263_6 sourceNode269_7

theorem sourceNode251_25 : (data.drop 251).take 25 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 251).take 25 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 251 12 13 sourceNode251_12 sourceNode263_13

theorem sourceNode277_2 : (data.drop 277).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 277).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 277 1 1 binding277 binding278

theorem sourceNode276_3 : (data.drop 276).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 276).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 276 1 2 binding276 sourceNode277_2

theorem sourceNode280_2 : (data.drop 280).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 280).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 280 1 1 binding280 binding281

theorem sourceNode279_3 : (data.drop 279).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 279).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 279 1 2 binding279 sourceNode280_2

theorem sourceNode276_6 : (data.drop 276).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 276).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 276 3 3 sourceNode276_3 sourceNode279_3

theorem sourceNode283_2 : (data.drop 283).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 283).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 283 1 1 binding283 binding284

theorem sourceNode282_3 : (data.drop 282).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 282).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 282 1 2 binding282 sourceNode283_2

theorem sourceNode285_2 : (data.drop 285).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 285).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 285 1 1 binding285 binding286

theorem sourceNode287_2 : (data.drop 287).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 287).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 287 1 1 binding287 binding288

theorem sourceNode285_4 : (data.drop 285).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 285).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 285 2 2 sourceNode285_2 sourceNode287_2

theorem sourceNode282_7 : (data.drop 282).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 282).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 282 3 4 sourceNode282_3 sourceNode285_4

theorem sourceNode276_13 : (data.drop 276).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 276).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 276 6 7 sourceNode276_6 sourceNode282_7

theorem sourceNode290_2 : (data.drop 290).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 290).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 290 1 1 binding290 binding291

theorem sourceNode289_3 : (data.drop 289).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 289).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 289 1 2 binding289 sourceNode290_2

theorem sourceNode293_2 : (data.drop 293).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 293).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 293 1 1 binding293 binding294

theorem sourceNode292_3 : (data.drop 292).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 292).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 292 1 2 binding292 sourceNode293_2

theorem sourceNode289_6 : (data.drop 289).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 289).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 289 3 3 sourceNode289_3 sourceNode292_3

theorem sourceNode296_2 : (data.drop 296).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 296).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 296 1 1 binding296 binding297

theorem sourceNode295_3 : (data.drop 295).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 295).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 295 1 2 binding295 sourceNode296_2

theorem sourceNode298_2 : (data.drop 298).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 298).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 298 1 1 binding298 binding299

theorem sourceNode300_2 : (data.drop 300).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 300).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 300 1 1 binding300 binding301

theorem sourceNode298_4 : (data.drop 298).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 298).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 298 2 2 sourceNode298_2 sourceNode300_2

theorem sourceNode295_7 : (data.drop 295).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 295).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 295 3 4 sourceNode295_3 sourceNode298_4

theorem sourceNode289_13 : (data.drop 289).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 289).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 289 6 7 sourceNode289_6 sourceNode295_7

theorem sourceNode276_26 : (data.drop 276).take 26 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 276).take 26 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 276 13 13 sourceNode276_13 sourceNode289_13

theorem sourceNode251_51 : (data.drop 251).take 51 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 251).take 51 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 251 25 26 sourceNode251_25 sourceNode276_26

theorem sourceNode201_101 : (data.drop 201).take 101 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 201).take 101 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 201 50 51 sourceNode201_50 sourceNode251_51

theorem sourceNode303_2 : (data.drop 303).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 303).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 303 1 1 binding303 binding304

theorem sourceNode302_3 : (data.drop 302).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 302).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 302 1 2 binding302 sourceNode303_2

theorem sourceNode306_2 : (data.drop 306).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 306).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 306 1 1 binding306 binding307

theorem sourceNode305_3 : (data.drop 305).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 305).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 305 1 2 binding305 sourceNode306_2

theorem sourceNode302_6 : (data.drop 302).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 302).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 302 3 3 sourceNode302_3 sourceNode305_3

theorem sourceNode309_2 : (data.drop 309).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 309).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 309 1 1 binding309 binding310

theorem sourceNode308_3 : (data.drop 308).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 308).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 308 1 2 binding308 sourceNode309_2

theorem sourceNode312_2 : (data.drop 312).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 312).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 312 1 1 binding312 binding313

theorem sourceNode311_3 : (data.drop 311).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 311).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 311 1 2 binding311 sourceNode312_2

theorem sourceNode308_6 : (data.drop 308).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 308).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 308 3 3 sourceNode308_3 sourceNode311_3

theorem sourceNode302_12 : (data.drop 302).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 302).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 302 6 6 sourceNode302_6 sourceNode308_6

theorem sourceNode315_2 : (data.drop 315).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 315).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 315 1 1 binding315 binding316

theorem sourceNode314_3 : (data.drop 314).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 314).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 314 1 2 binding314 sourceNode315_2

theorem sourceNode318_2 : (data.drop 318).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 318).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 318 1 1 binding318 binding319

theorem sourceNode317_3 : (data.drop 317).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 317).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 317 1 2 binding317 sourceNode318_2

theorem sourceNode314_6 : (data.drop 314).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 314).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 314 3 3 sourceNode314_3 sourceNode317_3

theorem sourceNode321_2 : (data.drop 321).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 321).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 321 1 1 binding321 binding322

theorem sourceNode320_3 : (data.drop 320).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 320).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 320 1 2 binding320 sourceNode321_2

theorem sourceNode323_2 : (data.drop 323).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 323).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 323 1 1 binding323 binding324

theorem sourceNode325_2 : (data.drop 325).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 325).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 325 1 1 binding325 binding326

theorem sourceNode323_4 : (data.drop 323).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 323).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 323 2 2 sourceNode323_2 sourceNode325_2

theorem sourceNode320_7 : (data.drop 320).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 320).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 320 3 4 sourceNode320_3 sourceNode323_4

theorem sourceNode314_13 : (data.drop 314).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 314).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 314 6 7 sourceNode314_6 sourceNode320_7

theorem sourceNode302_25 : (data.drop 302).take 25 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 302).take 25 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 302 12 13 sourceNode302_12 sourceNode314_13

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

theorem sourceNode334_2 : (data.drop 334).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 334).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 334 1 1 binding334 binding335

theorem sourceNode333_3 : (data.drop 333).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 333).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 333 1 2 binding333 sourceNode334_2

theorem sourceNode337_2 : (data.drop 337).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 337).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 337 1 1 binding337 binding338

theorem sourceNode336_3 : (data.drop 336).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 336).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 336 1 2 binding336 sourceNode337_2

theorem sourceNode333_6 : (data.drop 333).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 333).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 333 3 3 sourceNode333_3 sourceNode336_3

theorem sourceNode327_12 : (data.drop 327).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 327).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 327 6 6 sourceNode327_6 sourceNode333_6

theorem sourceNode340_2 : (data.drop 340).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 340).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 340 1 1 binding340 binding341

theorem sourceNode339_3 : (data.drop 339).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 339).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 339 1 2 binding339 sourceNode340_2

theorem sourceNode343_2 : (data.drop 343).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 343).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 343 1 1 binding343 binding344

theorem sourceNode342_3 : (data.drop 342).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 342).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 342 1 2 binding342 sourceNode343_2

theorem sourceNode339_6 : (data.drop 339).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 339).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 339 3 3 sourceNode339_3 sourceNode342_3

theorem sourceNode346_2 : (data.drop 346).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 346).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 346 1 1 binding346 binding347

theorem sourceNode345_3 : (data.drop 345).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 345).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 345 1 2 binding345 sourceNode346_2

theorem sourceNode348_2 : (data.drop 348).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 348).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 348 1 1 binding348 binding349

theorem sourceNode350_2 : (data.drop 350).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 350).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 350 1 1 binding350 binding351

theorem sourceNode348_4 : (data.drop 348).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 348).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 348 2 2 sourceNode348_2 sourceNode350_2

theorem sourceNode345_7 : (data.drop 345).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 345).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 345 3 4 sourceNode345_3 sourceNode348_4

theorem sourceNode339_13 : (data.drop 339).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 339).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 339 6 7 sourceNode339_6 sourceNode345_7

theorem sourceNode327_25 : (data.drop 327).take 25 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 327).take 25 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 327 12 13 sourceNode327_12 sourceNode339_13

theorem sourceNode302_50 : (data.drop 302).take 50 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 302).take 50 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 302 25 25 sourceNode302_25 sourceNode327_25

theorem sourceNode353_2 : (data.drop 353).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 353).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 353 1 1 binding353 binding354

theorem sourceNode352_3 : (data.drop 352).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 352).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 352 1 2 binding352 sourceNode353_2

theorem sourceNode356_2 : (data.drop 356).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 356).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 356 1 1 binding356 binding357

theorem sourceNode355_3 : (data.drop 355).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 355).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 355 1 2 binding355 sourceNode356_2

theorem sourceNode352_6 : (data.drop 352).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 352).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 352 3 3 sourceNode352_3 sourceNode355_3

theorem sourceNode359_2 : (data.drop 359).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 359).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 359 1 1 binding359 binding360

theorem sourceNode358_3 : (data.drop 358).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 358).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 358 1 2 binding358 sourceNode359_2

theorem sourceNode362_2 : (data.drop 362).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 362).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 362 1 1 binding362 binding363

theorem sourceNode361_3 : (data.drop 361).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 361).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 361 1 2 binding361 sourceNode362_2

theorem sourceNode358_6 : (data.drop 358).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 358).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 358 3 3 sourceNode358_3 sourceNode361_3

theorem sourceNode352_12 : (data.drop 352).take 12 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 352).take 12 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 352 6 6 sourceNode352_6 sourceNode358_6

theorem sourceNode365_2 : (data.drop 365).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 365).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 365 1 1 binding365 binding366

theorem sourceNode364_3 : (data.drop 364).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 364).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 364 1 2 binding364 sourceNode365_2

theorem sourceNode368_2 : (data.drop 368).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 368).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 368 1 1 binding368 binding369

theorem sourceNode367_3 : (data.drop 367).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 367).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 367 1 2 binding367 sourceNode368_2

theorem sourceNode364_6 : (data.drop 364).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 364).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 364 3 3 sourceNode364_3 sourceNode367_3

theorem sourceNode371_2 : (data.drop 371).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 371).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 371 1 1 binding371 binding372

theorem sourceNode370_3 : (data.drop 370).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 370).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 370 1 2 binding370 sourceNode371_2

theorem sourceNode373_2 : (data.drop 373).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 373).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 373 1 1 binding373 binding374

theorem sourceNode375_2 : (data.drop 375).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 375).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 375 1 1 binding375 binding376

theorem sourceNode373_4 : (data.drop 373).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 373).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 373 2 2 sourceNode373_2 sourceNode375_2

theorem sourceNode370_7 : (data.drop 370).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 370).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 370 3 4 sourceNode370_3 sourceNode373_4

theorem sourceNode364_13 : (data.drop 364).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 364).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 364 6 7 sourceNode364_6 sourceNode370_7

theorem sourceNode352_25 : (data.drop 352).take 25 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 352).take 25 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 352 12 13 sourceNode352_12 sourceNode364_13

theorem sourceNode378_2 : (data.drop 378).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 378).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 378 1 1 binding378 binding379

theorem sourceNode377_3 : (data.drop 377).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 377).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 377 1 2 binding377 sourceNode378_2

theorem sourceNode381_2 : (data.drop 381).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 381).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 381 1 1 binding381 binding382

theorem sourceNode380_3 : (data.drop 380).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 380).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 380 1 2 binding380 sourceNode381_2

theorem sourceNode377_6 : (data.drop 377).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 377).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 377 3 3 sourceNode377_3 sourceNode380_3

theorem sourceNode384_2 : (data.drop 384).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 384).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 384 1 1 binding384 binding385

theorem sourceNode383_3 : (data.drop 383).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 383).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 383 1 2 binding383 sourceNode384_2

theorem sourceNode386_2 : (data.drop 386).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 386).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 386 1 1 binding386 binding387

theorem sourceNode388_2 : (data.drop 388).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 388).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 388 1 1 binding388 binding389

theorem sourceNode386_4 : (data.drop 386).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 386).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 386 2 2 sourceNode386_2 sourceNode388_2

theorem sourceNode383_7 : (data.drop 383).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 383).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 383 3 4 sourceNode383_3 sourceNode386_4

theorem sourceNode377_13 : (data.drop 377).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 377).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 377 6 7 sourceNode377_6 sourceNode383_7

theorem sourceNode391_2 : (data.drop 391).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 391).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 391 1 1 binding391 binding392

theorem sourceNode390_3 : (data.drop 390).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 390).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 390 1 2 binding390 sourceNode391_2

theorem sourceNode394_2 : (data.drop 394).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 394).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 394 1 1 binding394 binding395

theorem sourceNode393_3 : (data.drop 393).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 393).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 393 1 2 binding393 sourceNode394_2

theorem sourceNode390_6 : (data.drop 390).take 6 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 390).take 6 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 390 3 3 sourceNode390_3 sourceNode393_3

theorem sourceNode397_2 : (data.drop 397).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 397).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 397 1 1 binding397 binding398

theorem sourceNode396_3 : (data.drop 396).take 3 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 396).take 3 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 396 1 2 binding396 sourceNode397_2

theorem sourceNode399_2 : (data.drop 399).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 399).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 399 1 1 binding399 binding400

theorem sourceNode401_2 : (data.drop 401).take 2 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 401).take 2 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 401 1 1 binding401 binding402

theorem sourceNode399_4 : (data.drop 399).take 4 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 399).take 4 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 399 2 2 sourceNode399_2 sourceNode401_2

theorem sourceNode396_7 : (data.drop 396).take 7 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 396).take 7 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 396 3 4 sourceNode396_3 sourceNode399_4

theorem sourceNode390_13 : (data.drop 390).take 13 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 390).take 13 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 390 6 7 sourceNode390_6 sourceNode396_7

theorem sourceNode377_26 : (data.drop 377).take 26 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 377).take 26 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 377 13 13 sourceNode377_13 sourceNode390_13

theorem sourceNode352_51 : (data.drop 352).take 51 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 352).take 51 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 352 25 26 sourceNode352_25 sourceNode377_26

theorem sourceNode302_101 : (data.drop 302).take 101 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 302).take 101 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 302 50 51 sourceNode302_50 sourceNode352_51

theorem sourceNode201_202 : (data.drop 201).take 202 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 201).take 202 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 201 101 101 sourceNode201_101 sourceNode302_101

theorem sourceNode0_403 : (data.drop 0).take 403 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 403 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 201 202 sourceNode0_201 sourceNode201_202

theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 403
    (by decide +kernel) (by decide +kernel) sourceNode0_403

end Airbender.Compiler.LookupSourceChecks.KeccakUncached
