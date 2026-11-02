import Airbender.Proofs.GKRProtocol.WorkerPortChecks.BlakeGUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.WorkerPortChecks.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

attribute [local irreducible] original data

numeric_data_binding columns0_view : (data.columns.drop 0).take 4 = (columns0.columns.drop 0).take 4

numeric_data_binding columns0_piece : (columns0.columns.drop 0).take 4 = ((original.columns.drop 0).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns0_binding : (data.columns.drop 0).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 0).take 4 :=
  columns0_view.trans (columns0_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 0 4))

numeric_data_binding columns4_view : (data.columns.drop 4).take 4 = (columns0.columns.drop 4).take 4

numeric_data_binding columns4_piece : (columns0.columns.drop 4).take 4 = ((original.columns.drop 4).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns4_binding : (data.columns.drop 4).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 4).take 4 :=
  columns4_view.trans (columns4_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 4 4))

numeric_data_binding columns8_view : (data.columns.drop 8).take 4 = (columns0.columns.drop 8).take 4

numeric_data_binding columns8_piece : (columns0.columns.drop 8).take 4 = ((original.columns.drop 8).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns8_binding : (data.columns.drop 8).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 8).take 4 :=
  columns8_view.trans (columns8_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 8 4))

numeric_data_binding columns12_view : (data.columns.drop 12).take 4 = (columns0.columns.drop 12).take 4

numeric_data_binding columns12_piece : (columns0.columns.drop 12).take 4 = ((original.columns.drop 12).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns12_binding : (data.columns.drop 12).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 12).take 4 :=
  columns12_view.trans (columns12_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 12 4))

numeric_data_binding columns16_view : (data.columns.drop 16).take 4 = (columns16.columns.drop 0).take 4

numeric_data_binding columns16_piece : (columns16.columns.drop 0).take 4 = ((original.columns.drop 16).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns16_binding : (data.columns.drop 16).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 16).take 4 :=
  columns16_view.trans (columns16_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 16 4))

numeric_data_binding columns20_view : (data.columns.drop 20).take 4 = (columns16.columns.drop 4).take 4

numeric_data_binding columns20_piece : (columns16.columns.drop 4).take 4 = ((original.columns.drop 20).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns20_binding : (data.columns.drop 20).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 20).take 4 :=
  columns20_view.trans (columns20_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 20 4))

numeric_data_binding columns24_view : (data.columns.drop 24).take 4 = (columns16.columns.drop 8).take 4

numeric_data_binding columns24_piece : (columns16.columns.drop 8).take 4 = ((original.columns.drop 24).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns24_binding : (data.columns.drop 24).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 24).take 4 :=
  columns24_view.trans (columns24_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 24 4))

numeric_data_binding columns28_view : (data.columns.drop 28).take 4 = (columns16.columns.drop 12).take 4

numeric_data_binding columns28_piece : (columns16.columns.drop 12).take 4 = ((original.columns.drop 28).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns28_binding : (data.columns.drop 28).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 28).take 4 :=
  columns28_view.trans (columns28_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 28 4))

numeric_data_binding columns32_view : (data.columns.drop 32).take 4 = (columns32.columns.drop 0).take 4

numeric_data_binding columns32_piece : (columns32.columns.drop 0).take 4 = ((original.columns.drop 32).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns32_binding : (data.columns.drop 32).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 32).take 4 :=
  columns32_view.trans (columns32_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 32 4))

numeric_data_binding columns36_view : (data.columns.drop 36).take 4 = (columns32.columns.drop 4).take 4

numeric_data_binding columns36_piece : (columns32.columns.drop 4).take 4 = ((original.columns.drop 36).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns36_binding : (data.columns.drop 36).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 36).take 4 :=
  columns36_view.trans (columns36_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 36 4))

numeric_data_binding columns40_view : (data.columns.drop 40).take 4 = (columns32.columns.drop 8).take 4

numeric_data_binding columns40_piece : (columns32.columns.drop 8).take 4 = ((original.columns.drop 40).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns40_binding : (data.columns.drop 40).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 40).take 4 :=
  columns40_view.trans (columns40_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 40 4))

numeric_data_binding columns44_view : (data.columns.drop 44).take 4 = (columns32.columns.drop 12).take 4

numeric_data_binding columns44_piece : (columns32.columns.drop 12).take 4 = ((original.columns.drop 44).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns44_binding : (data.columns.drop 44).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 44).take 4 :=
  columns44_view.trans (columns44_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 44 4))

numeric_data_binding columns48_view : (data.columns.drop 48).take 4 = (columns48.columns.drop 0).take 4

numeric_data_binding columns48_piece : (columns48.columns.drop 0).take 4 = ((original.columns.drop 48).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns48_binding : (data.columns.drop 48).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 48).take 4 :=
  columns48_view.trans (columns48_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 48 4))

numeric_data_binding columns52_view : (data.columns.drop 52).take 4 = (columns48.columns.drop 4).take 4

numeric_data_binding columns52_piece : (columns48.columns.drop 4).take 4 = ((original.columns.drop 52).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns52_binding : (data.columns.drop 52).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 52).take 4 :=
  columns52_view.trans (columns52_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 52 4))

numeric_data_binding columns56_view : (data.columns.drop 56).take 4 = (columns48.columns.drop 8).take 4

numeric_data_binding columns56_piece : (columns48.columns.drop 8).take 4 = ((original.columns.drop 56).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns56_binding : (data.columns.drop 56).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 56).take 4 :=
  columns56_view.trans (columns56_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 56 4))

numeric_data_binding columns60_view : (data.columns.drop 60).take 4 = (columns48.columns.drop 12).take 4

numeric_data_binding columns60_piece : (columns48.columns.drop 12).take 4 = ((original.columns.drop 60).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns60_binding : (data.columns.drop 60).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 60).take 4 :=
  columns60_view.trans (columns60_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 60 4))

numeric_data_binding columns64_view : (data.columns.drop 64).take 4 = (columns64.columns.drop 0).take 4

numeric_data_binding columns64_piece : (columns64.columns.drop 0).take 4 = ((original.columns.drop 64).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns64_binding : (data.columns.drop 64).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 64).take 4 :=
  columns64_view.trans (columns64_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 64 4))

numeric_data_binding columns68_view : (data.columns.drop 68).take 4 = (columns64.columns.drop 4).take 4

numeric_data_binding columns68_piece : (columns64.columns.drop 4).take 4 = ((original.columns.drop 68).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns68_binding : (data.columns.drop 68).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 68).take 4 :=
  columns68_view.trans (columns68_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 68 4))

numeric_data_binding columns72_view : (data.columns.drop 72).take 4 = (columns64.columns.drop 8).take 4

numeric_data_binding columns72_piece : (columns64.columns.drop 8).take 4 = ((original.columns.drop 72).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns72_binding : (data.columns.drop 72).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 72).take 4 :=
  columns72_view.trans (columns72_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 72 4))

numeric_data_binding columns76_view : (data.columns.drop 76).take 4 = (columns64.columns.drop 12).take 4

numeric_data_binding columns76_piece : (columns64.columns.drop 12).take 4 = ((original.columns.drop 76).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns76_binding : (data.columns.drop 76).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 76).take 4 :=
  columns76_view.trans (columns76_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 76 4))

numeric_data_binding columns80_view : (data.columns.drop 80).take 4 = (columns80.columns.drop 0).take 4

numeric_data_binding columns80_piece : (columns80.columns.drop 0).take 4 = ((original.columns.drop 80).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns80_binding : (data.columns.drop 80).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 80).take 4 :=
  columns80_view.trans (columns80_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 80 4))

numeric_data_binding columns84_view : (data.columns.drop 84).take 4 = (columns80.columns.drop 4).take 4

numeric_data_binding columns84_piece : (columns80.columns.drop 4).take 4 = ((original.columns.drop 84).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns84_binding : (data.columns.drop 84).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 84).take 4 :=
  columns84_view.trans (columns84_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 84 4))

numeric_data_binding columns88_view : (data.columns.drop 88).take 4 = (columns80.columns.drop 8).take 4

numeric_data_binding columns88_piece : (columns80.columns.drop 8).take 4 = ((original.columns.drop 88).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns88_binding : (data.columns.drop 88).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 88).take 4 :=
  columns88_view.trans (columns88_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 88 4))

numeric_data_binding columns92_view : (data.columns.drop 92).take 4 = (columns80.columns.drop 12).take 4

numeric_data_binding columns92_piece : (columns80.columns.drop 12).take 4 = ((original.columns.drop 92).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns92_binding : (data.columns.drop 92).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 92).take 4 :=
  columns92_view.trans (columns92_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 92 4))

numeric_data_binding columns96_view : (data.columns.drop 96).take 4 = (columns96.columns.drop 0).take 4

numeric_data_binding columns96_piece : (columns96.columns.drop 0).take 4 = ((original.columns.drop 96).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns96_binding : (data.columns.drop 96).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 96).take 4 :=
  columns96_view.trans (columns96_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 96 4))

numeric_data_binding columns100_view : (data.columns.drop 100).take 4 = (columns96.columns.drop 4).take 4

numeric_data_binding columns100_piece : (columns96.columns.drop 4).take 4 = ((original.columns.drop 100).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns100_binding : (data.columns.drop 100).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 100).take 4 :=
  columns100_view.trans (columns100_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 100 4))

numeric_data_binding columns104_view : (data.columns.drop 104).take 4 = (columns96.columns.drop 8).take 4

numeric_data_binding columns104_piece : (columns96.columns.drop 8).take 4 = ((original.columns.drop 104).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns104_binding : (data.columns.drop 104).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 104).take 4 :=
  columns104_view.trans (columns104_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 104 4))

numeric_data_binding columns108_view : (data.columns.drop 108).take 3 = (columns96.columns.drop 12).take 3

numeric_data_binding columns108_piece : (columns96.columns.drop 12).take 3 = ((original.columns.drop 108).take 3).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns108_binding : (data.columns.drop 108).take 3 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 108).take 3 :=
  columns108_view.trans (columns108_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 108 3))

theorem columnsNode4_8 : (data.columns.drop 4).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 4).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 4 4 4 8 8 rfl rfl columns4_binding columns8_binding

theorem columnsNode0_12 : (data.columns.drop 0).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 0).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 0 4 8 4 12 rfl rfl columns0_binding columnsNode4_8

theorem columnsNode12_8 : (data.columns.drop 12).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 12).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 12 4 4 16 8 rfl rfl columns12_binding columns16_binding

theorem columnsNode20_8 : (data.columns.drop 20).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 20).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 20 4 4 24 8 rfl rfl columns20_binding columns24_binding

theorem columnsNode12_16 : (data.columns.drop 12).take 16 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 12).take 16 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 12 8 8 20 16 rfl rfl columnsNode12_8 columnsNode20_8

theorem columnsNode0_28 : (data.columns.drop 0).take 28 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 0).take 28 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 0 12 16 12 28 rfl rfl columnsNode0_12 columnsNode12_16

theorem columnsNode32_8 : (data.columns.drop 32).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 32).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 32 4 4 36 8 rfl rfl columns32_binding columns36_binding

theorem columnsNode28_12 : (data.columns.drop 28).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 28).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 28 4 8 32 12 rfl rfl columns28_binding columnsNode32_8

theorem columnsNode40_8 : (data.columns.drop 40).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 40).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 40 4 4 44 8 rfl rfl columns40_binding columns44_binding

theorem columnsNode48_8 : (data.columns.drop 48).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 48).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 48 4 4 52 8 rfl rfl columns48_binding columns52_binding

theorem columnsNode40_16 : (data.columns.drop 40).take 16 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 40).take 16 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 40 8 8 48 16 rfl rfl columnsNode40_8 columnsNode48_8

theorem columnsNode28_28 : (data.columns.drop 28).take 28 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 28).take 28 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 28 12 16 40 28 rfl rfl columnsNode28_12 columnsNode40_16

theorem columnsNode0_56 : (data.columns.drop 0).take 56 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 0).take 56 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 0 28 28 28 56 rfl rfl columnsNode0_28 columnsNode28_28

theorem columnsNode60_8 : (data.columns.drop 60).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 60).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 60 4 4 64 8 rfl rfl columns60_binding columns64_binding

theorem columnsNode56_12 : (data.columns.drop 56).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 56).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 56 4 8 60 12 rfl rfl columns56_binding columnsNode60_8

theorem columnsNode68_8 : (data.columns.drop 68).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 68).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 68 4 4 72 8 rfl rfl columns68_binding columns72_binding

theorem columnsNode76_8 : (data.columns.drop 76).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 76).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 76 4 4 80 8 rfl rfl columns76_binding columns80_binding

theorem columnsNode68_16 : (data.columns.drop 68).take 16 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 68).take 16 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 68 8 8 76 16 rfl rfl columnsNode68_8 columnsNode76_8

theorem columnsNode56_28 : (data.columns.drop 56).take 28 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 56).take 28 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 56 12 16 68 28 rfl rfl columnsNode56_12 columnsNode68_16

theorem columnsNode88_8 : (data.columns.drop 88).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 88).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 88 4 4 92 8 rfl rfl columns88_binding columns92_binding

theorem columnsNode84_12 : (data.columns.drop 84).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 84).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 84 4 8 88 12 rfl rfl columns84_binding columnsNode88_8

theorem columnsNode96_8 : (data.columns.drop 96).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 96).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 96 4 4 100 8 rfl rfl columns96_binding columns100_binding

theorem columnsNode104_7 : (data.columns.drop 104).take 7 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 104).take 7 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 104 4 3 108 7 rfl rfl columns104_binding columns108_binding

theorem columnsNode96_15 : (data.columns.drop 96).take 15 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 96).take 15 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 96 8 7 104 15 rfl rfl columnsNode96_8 columnsNode104_7

theorem columnsNode84_27 : (data.columns.drop 84).take 27 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 84).take 27 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 84 12 15 96 27 rfl rfl columnsNode84_12 columnsNode96_15

theorem columnsNode56_55 : (data.columns.drop 56).take 55 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 56).take 55 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 56 28 27 84 55 rfl rfl columnsNode56_28 columnsNode84_27

theorem columnsNode0_111 : (data.columns.drop 0).take 111 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 0).take 111 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 0 56 55 56 111 rfl rfl columnsNode0_56 columnsNode56_55

theorem columns_binding : data.columns = (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) :=
  NumericQueryFrameChecks.complete_binding data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 111
    (by decide +kernel) (by decide +kernel) columnsNode0_111

numeric_data_binding bounds0_view : (data.bounds.drop 0).take 16 = (bounds0.bounds.drop 0).take 16

numeric_data_binding bounds0_piece : (bounds0.bounds.drop 0).take 16 = (original.bounds.drop 0).take 16

theorem bounds0_binding : (data.bounds.drop 0).take 16 = (original.bounds.drop 0).take 16 :=
  bounds0_view.trans bounds0_piece

numeric_data_binding bounds16_view : (data.bounds.drop 16).take 2 = (bounds0.bounds.drop 16).take 2

numeric_data_binding bounds16_piece : (bounds0.bounds.drop 16).take 2 = (original.bounds.drop 16).take 2

theorem bounds16_binding : (data.bounds.drop 16).take 2 = (original.bounds.drop 16).take 2 :=
  bounds16_view.trans bounds16_piece

theorem boundsNode0_18 : (data.bounds.drop 0).take 18 = (original.bounds.drop 0).take 18 :=
  NumericWorkerPortChecks.merge_at data.bounds original.bounds 0 16 2 16 18 rfl rfl bounds0_binding bounds16_binding

theorem bounds_binding : data.bounds = original.bounds :=
  NumericQueryFrameChecks.complete_binding data.bounds original.bounds 18
    (by decide +kernel) (by decide +kernel) boundsNode0_18

theorem source_binding : data = NumericWorkerPortChecks.encode original := by
  simpa only [data, NumericWorkerPortChecks.encode] using
    congrArg₂ NumericWorkerPortChecks.Data.mk columns_binding bounds_binding

end Airbender.Compiler.WorkerPortChecks.BlakeGUncached
