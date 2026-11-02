import Airbender.Proofs.GKRProtocol.WorkerPortChecks.BigintUncached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.WorkerPortChecks.BigintUncached
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

numeric_data_binding columns108_view : (data.columns.drop 108).take 4 = (columns96.columns.drop 12).take 4

numeric_data_binding columns108_piece : (columns96.columns.drop 12).take 4 = ((original.columns.drop 108).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns108_binding : (data.columns.drop 108).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 108).take 4 :=
  columns108_view.trans (columns108_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 108 4))

numeric_data_binding columns112_view : (data.columns.drop 112).take 4 = (columns112.columns.drop 0).take 4

numeric_data_binding columns112_piece : (columns112.columns.drop 0).take 4 = ((original.columns.drop 112).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns112_binding : (data.columns.drop 112).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 112).take 4 :=
  columns112_view.trans (columns112_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 112 4))

numeric_data_binding columns116_view : (data.columns.drop 116).take 4 = (columns112.columns.drop 4).take 4

numeric_data_binding columns116_piece : (columns112.columns.drop 4).take 4 = ((original.columns.drop 116).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns116_binding : (data.columns.drop 116).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 116).take 4 :=
  columns116_view.trans (columns116_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 116 4))

numeric_data_binding columns120_view : (data.columns.drop 120).take 4 = (columns112.columns.drop 8).take 4

numeric_data_binding columns120_piece : (columns112.columns.drop 8).take 4 = ((original.columns.drop 120).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns120_binding : (data.columns.drop 120).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 120).take 4 :=
  columns120_view.trans (columns120_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 120 4))

numeric_data_binding columns124_view : (data.columns.drop 124).take 4 = (columns112.columns.drop 12).take 4

numeric_data_binding columns124_piece : (columns112.columns.drop 12).take 4 = ((original.columns.drop 124).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns124_binding : (data.columns.drop 124).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 124).take 4 :=
  columns124_view.trans (columns124_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 124 4))

numeric_data_binding columns128_view : (data.columns.drop 128).take 4 = (columns128.columns.drop 0).take 4

numeric_data_binding columns128_piece : (columns128.columns.drop 0).take 4 = ((original.columns.drop 128).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns128_binding : (data.columns.drop 128).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 128).take 4 :=
  columns128_view.trans (columns128_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 128 4))

numeric_data_binding columns132_view : (data.columns.drop 132).take 4 = (columns128.columns.drop 4).take 4

numeric_data_binding columns132_piece : (columns128.columns.drop 4).take 4 = ((original.columns.drop 132).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns132_binding : (data.columns.drop 132).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 132).take 4 :=
  columns132_view.trans (columns132_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 132 4))

numeric_data_binding columns136_view : (data.columns.drop 136).take 4 = (columns128.columns.drop 8).take 4

numeric_data_binding columns136_piece : (columns128.columns.drop 8).take 4 = ((original.columns.drop 136).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns136_binding : (data.columns.drop 136).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 136).take 4 :=
  columns136_view.trans (columns136_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 136 4))

numeric_data_binding columns140_view : (data.columns.drop 140).take 4 = (columns128.columns.drop 12).take 4

numeric_data_binding columns140_piece : (columns128.columns.drop 12).take 4 = ((original.columns.drop 140).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns140_binding : (data.columns.drop 140).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 140).take 4 :=
  columns140_view.trans (columns140_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 140 4))

numeric_data_binding columns144_view : (data.columns.drop 144).take 4 = (columns144.columns.drop 0).take 4

numeric_data_binding columns144_piece : (columns144.columns.drop 0).take 4 = ((original.columns.drop 144).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns144_binding : (data.columns.drop 144).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 144).take 4 :=
  columns144_view.trans (columns144_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 144 4))

numeric_data_binding columns148_view : (data.columns.drop 148).take 4 = (columns144.columns.drop 4).take 4

numeric_data_binding columns148_piece : (columns144.columns.drop 4).take 4 = ((original.columns.drop 148).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns148_binding : (data.columns.drop 148).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 148).take 4 :=
  columns148_view.trans (columns148_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 148 4))

numeric_data_binding columns152_view : (data.columns.drop 152).take 4 = (columns144.columns.drop 8).take 4

numeric_data_binding columns152_piece : (columns144.columns.drop 8).take 4 = ((original.columns.drop 152).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns152_binding : (data.columns.drop 152).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 152).take 4 :=
  columns152_view.trans (columns152_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 152 4))

numeric_data_binding columns156_view : (data.columns.drop 156).take 4 = (columns144.columns.drop 12).take 4

numeric_data_binding columns156_piece : (columns144.columns.drop 12).take 4 = ((original.columns.drop 156).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns156_binding : (data.columns.drop 156).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 156).take 4 :=
  columns156_view.trans (columns156_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 156 4))

numeric_data_binding columns160_view : (data.columns.drop 160).take 4 = (columns160.columns.drop 0).take 4

numeric_data_binding columns160_piece : (columns160.columns.drop 0).take 4 = ((original.columns.drop 160).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns160_binding : (data.columns.drop 160).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 160).take 4 :=
  columns160_view.trans (columns160_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 160 4))

numeric_data_binding columns164_view : (data.columns.drop 164).take 4 = (columns160.columns.drop 4).take 4

numeric_data_binding columns164_piece : (columns160.columns.drop 4).take 4 = ((original.columns.drop 164).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns164_binding : (data.columns.drop 164).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 164).take 4 :=
  columns164_view.trans (columns164_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 164 4))

numeric_data_binding columns168_view : (data.columns.drop 168).take 4 = (columns160.columns.drop 8).take 4

numeric_data_binding columns168_piece : (columns160.columns.drop 8).take 4 = ((original.columns.drop 168).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns168_binding : (data.columns.drop 168).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 168).take 4 :=
  columns168_view.trans (columns168_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 168 4))

numeric_data_binding columns172_view : (data.columns.drop 172).take 4 = (columns160.columns.drop 12).take 4

numeric_data_binding columns172_piece : (columns160.columns.drop 12).take 4 = ((original.columns.drop 172).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns172_binding : (data.columns.drop 172).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 172).take 4 :=
  columns172_view.trans (columns172_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 172 4))

numeric_data_binding columns176_view : (data.columns.drop 176).take 4 = (columns176.columns.drop 0).take 4

numeric_data_binding columns176_piece : (columns176.columns.drop 0).take 4 = ((original.columns.drop 176).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns176_binding : (data.columns.drop 176).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 176).take 4 :=
  columns176_view.trans (columns176_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 176 4))

numeric_data_binding columns180_view : (data.columns.drop 180).take 4 = (columns176.columns.drop 4).take 4

numeric_data_binding columns180_piece : (columns176.columns.drop 4).take 4 = ((original.columns.drop 180).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns180_binding : (data.columns.drop 180).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 180).take 4 :=
  columns180_view.trans (columns180_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 180 4))

numeric_data_binding columns184_view : (data.columns.drop 184).take 4 = (columns176.columns.drop 8).take 4

numeric_data_binding columns184_piece : (columns176.columns.drop 8).take 4 = ((original.columns.drop 184).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns184_binding : (data.columns.drop 184).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 184).take 4 :=
  columns184_view.trans (columns184_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 184 4))

numeric_data_binding columns188_view : (data.columns.drop 188).take 4 = (columns176.columns.drop 12).take 4

numeric_data_binding columns188_piece : (columns176.columns.drop 12).take 4 = ((original.columns.drop 188).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns188_binding : (data.columns.drop 188).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 188).take 4 :=
  columns188_view.trans (columns188_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 188 4))

numeric_data_binding columns192_view : (data.columns.drop 192).take 4 = (columns192.columns.drop 0).take 4

numeric_data_binding columns192_piece : (columns192.columns.drop 0).take 4 = ((original.columns.drop 192).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns192_binding : (data.columns.drop 192).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 192).take 4 :=
  columns192_view.trans (columns192_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 192 4))

numeric_data_binding columns196_view : (data.columns.drop 196).take 4 = (columns192.columns.drop 4).take 4

numeric_data_binding columns196_piece : (columns192.columns.drop 4).take 4 = ((original.columns.drop 196).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns196_binding : (data.columns.drop 196).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 196).take 4 :=
  columns196_view.trans (columns196_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 196 4))

numeric_data_binding columns200_view : (data.columns.drop 200).take 4 = (columns192.columns.drop 8).take 4

numeric_data_binding columns200_piece : (columns192.columns.drop 8).take 4 = ((original.columns.drop 200).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns200_binding : (data.columns.drop 200).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 200).take 4 :=
  columns200_view.trans (columns200_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 200 4))

numeric_data_binding columns204_view : (data.columns.drop 204).take 4 = (columns192.columns.drop 12).take 4

numeric_data_binding columns204_piece : (columns192.columns.drop 12).take 4 = ((original.columns.drop 204).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns204_binding : (data.columns.drop 204).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 204).take 4 :=
  columns204_view.trans (columns204_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 204 4))

numeric_data_binding columns208_view : (data.columns.drop 208).take 4 = (columns208.columns.drop 0).take 4

numeric_data_binding columns208_piece : (columns208.columns.drop 0).take 4 = ((original.columns.drop 208).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns208_binding : (data.columns.drop 208).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 208).take 4 :=
  columns208_view.trans (columns208_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 208 4))

numeric_data_binding columns212_view : (data.columns.drop 212).take 4 = (columns208.columns.drop 4).take 4

numeric_data_binding columns212_piece : (columns208.columns.drop 4).take 4 = ((original.columns.drop 212).take 4).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns212_binding : (data.columns.drop 212).take 4 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 212).take 4 :=
  columns212_view.trans (columns212_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 212 4))

numeric_data_binding columns216_view : (data.columns.drop 216).take 3 = (columns208.columns.drop 8).take 3

numeric_data_binding columns216_piece : (columns208.columns.drop 8).take 3 = ((original.columns.drop 216).take 3).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns216_binding : (data.columns.drop 216).take 3 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 216).take 3 :=
  columns216_view.trans (columns216_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 216 3))

theorem columnsNode4_8 : (data.columns.drop 4).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 4).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 4 4 4 8 8 rfl rfl columns4_binding columns8_binding

theorem columnsNode0_12 : (data.columns.drop 0).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 0).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 0 4 8 4 12 rfl rfl columns0_binding columnsNode4_8

theorem columnsNode16_8 : (data.columns.drop 16).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 16).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 16 4 4 20 8 rfl rfl columns16_binding columns20_binding

theorem columnsNode12_12 : (data.columns.drop 12).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 12).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 12 4 8 16 12 rfl rfl columns12_binding columnsNode16_8

theorem columnsNode0_24 : (data.columns.drop 0).take 24 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 0).take 24 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 0 12 12 12 24 rfl rfl columnsNode0_12 columnsNode12_12

theorem columnsNode28_8 : (data.columns.drop 28).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 28).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 28 4 4 32 8 rfl rfl columns28_binding columns32_binding

theorem columnsNode24_12 : (data.columns.drop 24).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 24).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 24 4 8 28 12 rfl rfl columns24_binding columnsNode28_8

theorem columnsNode36_8 : (data.columns.drop 36).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 36).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 36 4 4 40 8 rfl rfl columns36_binding columns40_binding

theorem columnsNode44_8 : (data.columns.drop 44).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 44).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 44 4 4 48 8 rfl rfl columns44_binding columns48_binding

theorem columnsNode36_16 : (data.columns.drop 36).take 16 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 36).take 16 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 36 8 8 44 16 rfl rfl columnsNode36_8 columnsNode44_8

theorem columnsNode24_28 : (data.columns.drop 24).take 28 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 24).take 28 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 24 12 16 36 28 rfl rfl columnsNode24_12 columnsNode36_16

theorem columnsNode0_52 : (data.columns.drop 0).take 52 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 0).take 52 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 0 24 28 24 52 rfl rfl columnsNode0_24 columnsNode24_28

theorem columnsNode56_8 : (data.columns.drop 56).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 56).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 56 4 4 60 8 rfl rfl columns56_binding columns60_binding

theorem columnsNode52_12 : (data.columns.drop 52).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 52).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 52 4 8 56 12 rfl rfl columns52_binding columnsNode56_8

theorem columnsNode64_8 : (data.columns.drop 64).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 64).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 64 4 4 68 8 rfl rfl columns64_binding columns68_binding

theorem columnsNode72_8 : (data.columns.drop 72).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 72).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 72 4 4 76 8 rfl rfl columns72_binding columns76_binding

theorem columnsNode64_16 : (data.columns.drop 64).take 16 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 64).take 16 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 64 8 8 72 16 rfl rfl columnsNode64_8 columnsNode72_8

theorem columnsNode52_28 : (data.columns.drop 52).take 28 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 52).take 28 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 52 12 16 64 28 rfl rfl columnsNode52_12 columnsNode64_16

theorem columnsNode84_8 : (data.columns.drop 84).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 84).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 84 4 4 88 8 rfl rfl columns84_binding columns88_binding

theorem columnsNode80_12 : (data.columns.drop 80).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 80).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 80 4 8 84 12 rfl rfl columns80_binding columnsNode84_8

theorem columnsNode92_8 : (data.columns.drop 92).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 92).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 92 4 4 96 8 rfl rfl columns92_binding columns96_binding

theorem columnsNode100_8 : (data.columns.drop 100).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 100).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 100 4 4 104 8 rfl rfl columns100_binding columns104_binding

theorem columnsNode92_16 : (data.columns.drop 92).take 16 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 92).take 16 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 92 8 8 100 16 rfl rfl columnsNode92_8 columnsNode100_8

theorem columnsNode80_28 : (data.columns.drop 80).take 28 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 80).take 28 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 80 12 16 92 28 rfl rfl columnsNode80_12 columnsNode92_16

theorem columnsNode52_56 : (data.columns.drop 52).take 56 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 52).take 56 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 52 28 28 80 56 rfl rfl columnsNode52_28 columnsNode80_28

theorem columnsNode0_108 : (data.columns.drop 0).take 108 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 0).take 108 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 0 52 56 52 108 rfl rfl columnsNode0_52 columnsNode52_56

theorem columnsNode112_8 : (data.columns.drop 112).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 112).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 112 4 4 116 8 rfl rfl columns112_binding columns116_binding

theorem columnsNode108_12 : (data.columns.drop 108).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 108).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 108 4 8 112 12 rfl rfl columns108_binding columnsNode112_8

theorem columnsNode120_8 : (data.columns.drop 120).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 120).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 120 4 4 124 8 rfl rfl columns120_binding columns124_binding

theorem columnsNode128_8 : (data.columns.drop 128).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 128).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 128 4 4 132 8 rfl rfl columns128_binding columns132_binding

theorem columnsNode120_16 : (data.columns.drop 120).take 16 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 120).take 16 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 120 8 8 128 16 rfl rfl columnsNode120_8 columnsNode128_8

theorem columnsNode108_28 : (data.columns.drop 108).take 28 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 108).take 28 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 108 12 16 120 28 rfl rfl columnsNode108_12 columnsNode120_16

theorem columnsNode140_8 : (data.columns.drop 140).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 140).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 140 4 4 144 8 rfl rfl columns140_binding columns144_binding

theorem columnsNode136_12 : (data.columns.drop 136).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 136).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 136 4 8 140 12 rfl rfl columns136_binding columnsNode140_8

theorem columnsNode148_8 : (data.columns.drop 148).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 148).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 148 4 4 152 8 rfl rfl columns148_binding columns152_binding

theorem columnsNode156_8 : (data.columns.drop 156).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 156).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 156 4 4 160 8 rfl rfl columns156_binding columns160_binding

theorem columnsNode148_16 : (data.columns.drop 148).take 16 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 148).take 16 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 148 8 8 156 16 rfl rfl columnsNode148_8 columnsNode156_8

theorem columnsNode136_28 : (data.columns.drop 136).take 28 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 136).take 28 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 136 12 16 148 28 rfl rfl columnsNode136_12 columnsNode148_16

theorem columnsNode108_56 : (data.columns.drop 108).take 56 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 108).take 56 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 108 28 28 136 56 rfl rfl columnsNode108_28 columnsNode136_28

theorem columnsNode168_8 : (data.columns.drop 168).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 168).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 168 4 4 172 8 rfl rfl columns168_binding columns172_binding

theorem columnsNode164_12 : (data.columns.drop 164).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 164).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 164 4 8 168 12 rfl rfl columns164_binding columnsNode168_8

theorem columnsNode176_8 : (data.columns.drop 176).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 176).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 176 4 4 180 8 rfl rfl columns176_binding columns180_binding

theorem columnsNode184_8 : (data.columns.drop 184).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 184).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 184 4 4 188 8 rfl rfl columns184_binding columns188_binding

theorem columnsNode176_16 : (data.columns.drop 176).take 16 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 176).take 16 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 176 8 8 184 16 rfl rfl columnsNode176_8 columnsNode184_8

theorem columnsNode164_28 : (data.columns.drop 164).take 28 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 164).take 28 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 164 12 16 176 28 rfl rfl columnsNode164_12 columnsNode176_16

theorem columnsNode196_8 : (data.columns.drop 196).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 196).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 196 4 4 200 8 rfl rfl columns196_binding columns200_binding

theorem columnsNode192_12 : (data.columns.drop 192).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 192).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 192 4 8 196 12 rfl rfl columns192_binding columnsNode196_8

theorem columnsNode204_8 : (data.columns.drop 204).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 204).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 204 4 4 208 8 rfl rfl columns204_binding columns208_binding

theorem columnsNode212_7 : (data.columns.drop 212).take 7 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 212).take 7 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 212 4 3 216 7 rfl rfl columns212_binding columns216_binding

theorem columnsNode204_15 : (data.columns.drop 204).take 15 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 204).take 15 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 204 8 7 212 15 rfl rfl columnsNode204_8 columnsNode212_7

theorem columnsNode192_27 : (data.columns.drop 192).take 27 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 192).take 27 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 192 12 15 204 27 rfl rfl columnsNode192_12 columnsNode204_15

theorem columnsNode164_55 : (data.columns.drop 164).take 55 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 164).take 55 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 164 28 27 192 55 rfl rfl columnsNode164_28 columnsNode192_27

theorem columnsNode108_111 : (data.columns.drop 108).take 111 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 108).take 111 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 108 56 55 164 111 rfl rfl columnsNode108_56 columnsNode164_55

theorem columnsNode0_219 : (data.columns.drop 0).take 219 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 0).take 219 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 0 108 111 108 219 rfl rfl columnsNode0_108 columnsNode108_111

theorem columns_binding : data.columns = (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) :=
  NumericQueryFrameChecks.complete_binding data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 219
    (by decide +kernel) (by decide +kernel) columnsNode0_219

numeric_data_binding bounds0_view : (data.bounds.drop 0).take 16 = (bounds0.bounds.drop 0).take 16

numeric_data_binding bounds0_piece : (bounds0.bounds.drop 0).take 16 = (original.bounds.drop 0).take 16

theorem bounds0_binding : (data.bounds.drop 0).take 16 = (original.bounds.drop 0).take 16 :=
  bounds0_view.trans bounds0_piece

numeric_data_binding bounds16_view : (data.bounds.drop 16).take 16 = (bounds0.bounds.drop 16).take 16

numeric_data_binding bounds16_piece : (bounds0.bounds.drop 16).take 16 = (original.bounds.drop 16).take 16

theorem bounds16_binding : (data.bounds.drop 16).take 16 = (original.bounds.drop 16).take 16 :=
  bounds16_view.trans bounds16_piece

numeric_data_binding bounds32_view : (data.bounds.drop 32).take 6 = (bounds32.bounds.drop 0).take 6

numeric_data_binding bounds32_piece : (bounds32.bounds.drop 0).take 6 = (original.bounds.drop 32).take 6

theorem bounds32_binding : (data.bounds.drop 32).take 6 = (original.bounds.drop 32).take 6 :=
  bounds32_view.trans bounds32_piece

theorem boundsNode16_22 : (data.bounds.drop 16).take 22 = (original.bounds.drop 16).take 22 :=
  NumericWorkerPortChecks.merge_at data.bounds original.bounds 16 16 6 32 22 rfl rfl bounds16_binding bounds32_binding

theorem boundsNode0_38 : (data.bounds.drop 0).take 38 = (original.bounds.drop 0).take 38 :=
  NumericWorkerPortChecks.merge_at data.bounds original.bounds 0 16 22 16 38 rfl rfl bounds0_binding boundsNode16_22

theorem bounds_binding : data.bounds = original.bounds :=
  NumericQueryFrameChecks.complete_binding data.bounds original.bounds 38
    (by decide +kernel) (by decide +kernel) boundsNode0_38

theorem source_binding : data = NumericWorkerPortChecks.encode original := by
  simpa only [data, NumericWorkerPortChecks.encode] using
    congrArg₂ NumericWorkerPortChecks.Data.mk columns_binding bounds_binding

end Airbender.Compiler.WorkerPortChecks.BigintUncached
