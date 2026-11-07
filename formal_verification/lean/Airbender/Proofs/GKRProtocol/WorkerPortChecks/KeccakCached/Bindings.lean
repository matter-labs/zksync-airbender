import Airbender.Proofs.GKRProtocol.WorkerPortChecks.KeccakCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.WorkerPortChecks.KeccakCached
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

numeric_data_binding columns184_view : (data.columns.drop 184).take 3 = (columns176.columns.drop 8).take 3

numeric_data_binding columns184_piece : (columns176.columns.drop 8).take 3 = ((original.columns.drop 184).take 3).map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))

theorem columns184_binding : (data.columns.drop 184).take 3 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 184).take 3 :=
  columns184_view.trans (columns184_piece.trans (NumericQueryFrameChecks.map_window original.columns (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2)) 184 3))

theorem columnsNode0_8 : (data.columns.drop 0).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 0).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 0 4 4 4 8 rfl rfl columns0_binding columns4_binding

theorem columnsNode12_8 : (data.columns.drop 12).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 12).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 12 4 4 16 8 rfl rfl columns12_binding columns16_binding

theorem columnsNode8_12 : (data.columns.drop 8).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 8).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 8 4 8 12 12 rfl rfl columns8_binding columnsNode12_8

theorem columnsNode0_20 : (data.columns.drop 0).take 20 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 0).take 20 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 0 8 12 8 20 rfl rfl columnsNode0_8 columnsNode8_12

theorem columnsNode24_8 : (data.columns.drop 24).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 24).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 24 4 4 28 8 rfl rfl columns24_binding columns28_binding

theorem columnsNode20_12 : (data.columns.drop 20).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 20).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 20 4 8 24 12 rfl rfl columns20_binding columnsNode24_8

theorem columnsNode36_8 : (data.columns.drop 36).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 36).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 36 4 4 40 8 rfl rfl columns36_binding columns40_binding

theorem columnsNode32_12 : (data.columns.drop 32).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 32).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 32 4 8 36 12 rfl rfl columns32_binding columnsNode36_8

theorem columnsNode20_24 : (data.columns.drop 20).take 24 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 20).take 24 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 20 12 12 32 24 rfl rfl columnsNode20_12 columnsNode32_12

theorem columnsNode0_44 : (data.columns.drop 0).take 44 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 0).take 44 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 0 20 24 20 44 rfl rfl columnsNode0_20 columnsNode20_24

theorem columnsNode48_8 : (data.columns.drop 48).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 48).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 48 4 4 52 8 rfl rfl columns48_binding columns52_binding

theorem columnsNode44_12 : (data.columns.drop 44).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 44).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 44 4 8 48 12 rfl rfl columns44_binding columnsNode48_8

theorem columnsNode60_8 : (data.columns.drop 60).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 60).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 60 4 4 64 8 rfl rfl columns60_binding columns64_binding

theorem columnsNode56_12 : (data.columns.drop 56).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 56).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 56 4 8 60 12 rfl rfl columns56_binding columnsNode60_8

theorem columnsNode44_24 : (data.columns.drop 44).take 24 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 44).take 24 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 44 12 12 56 24 rfl rfl columnsNode44_12 columnsNode56_12

theorem columnsNode72_8 : (data.columns.drop 72).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 72).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 72 4 4 76 8 rfl rfl columns72_binding columns76_binding

theorem columnsNode68_12 : (data.columns.drop 68).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 68).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 68 4 8 72 12 rfl rfl columns68_binding columnsNode72_8

theorem columnsNode84_8 : (data.columns.drop 84).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 84).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 84 4 4 88 8 rfl rfl columns84_binding columns88_binding

theorem columnsNode80_12 : (data.columns.drop 80).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 80).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 80 4 8 84 12 rfl rfl columns80_binding columnsNode84_8

theorem columnsNode68_24 : (data.columns.drop 68).take 24 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 68).take 24 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 68 12 12 80 24 rfl rfl columnsNode68_12 columnsNode80_12

theorem columnsNode44_48 : (data.columns.drop 44).take 48 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 44).take 48 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 44 24 24 68 48 rfl rfl columnsNode44_24 columnsNode68_24

theorem columnsNode0_92 : (data.columns.drop 0).take 92 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 0).take 92 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 0 44 48 44 92 rfl rfl columnsNode0_44 columnsNode44_48

theorem columnsNode96_8 : (data.columns.drop 96).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 96).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 96 4 4 100 8 rfl rfl columns96_binding columns100_binding

theorem columnsNode92_12 : (data.columns.drop 92).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 92).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 92 4 8 96 12 rfl rfl columns92_binding columnsNode96_8

theorem columnsNode108_8 : (data.columns.drop 108).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 108).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 108 4 4 112 8 rfl rfl columns108_binding columns112_binding

theorem columnsNode104_12 : (data.columns.drop 104).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 104).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 104 4 8 108 12 rfl rfl columns104_binding columnsNode108_8

theorem columnsNode92_24 : (data.columns.drop 92).take 24 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 92).take 24 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 92 12 12 104 24 rfl rfl columnsNode92_12 columnsNode104_12

theorem columnsNode120_8 : (data.columns.drop 120).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 120).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 120 4 4 124 8 rfl rfl columns120_binding columns124_binding

theorem columnsNode116_12 : (data.columns.drop 116).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 116).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 116 4 8 120 12 rfl rfl columns116_binding columnsNode120_8

theorem columnsNode132_8 : (data.columns.drop 132).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 132).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 132 4 4 136 8 rfl rfl columns132_binding columns136_binding

theorem columnsNode128_12 : (data.columns.drop 128).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 128).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 128 4 8 132 12 rfl rfl columns128_binding columnsNode132_8

theorem columnsNode116_24 : (data.columns.drop 116).take 24 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 116).take 24 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 116 12 12 128 24 rfl rfl columnsNode116_12 columnsNode128_12

theorem columnsNode92_48 : (data.columns.drop 92).take 48 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 92).take 48 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 92 24 24 116 48 rfl rfl columnsNode92_24 columnsNode116_24

theorem columnsNode144_8 : (data.columns.drop 144).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 144).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 144 4 4 148 8 rfl rfl columns144_binding columns148_binding

theorem columnsNode140_12 : (data.columns.drop 140).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 140).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 140 4 8 144 12 rfl rfl columns140_binding columnsNode144_8

theorem columnsNode156_8 : (data.columns.drop 156).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 156).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 156 4 4 160 8 rfl rfl columns156_binding columns160_binding

theorem columnsNode152_12 : (data.columns.drop 152).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 152).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 152 4 8 156 12 rfl rfl columns152_binding columnsNode156_8

theorem columnsNode140_24 : (data.columns.drop 140).take 24 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 140).take 24 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 140 12 12 152 24 rfl rfl columnsNode140_12 columnsNode152_12

theorem columnsNode168_8 : (data.columns.drop 168).take 8 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 168).take 8 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 168 4 4 172 8 rfl rfl columns168_binding columns172_binding

theorem columnsNode164_12 : (data.columns.drop 164).take 12 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 164).take 12 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 164 4 8 168 12 rfl rfl columns164_binding columnsNode168_8

theorem columnsNode180_7 : (data.columns.drop 180).take 7 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 180).take 7 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 180 4 3 184 7 rfl rfl columns180_binding columns184_binding

theorem columnsNode176_11 : (data.columns.drop 176).take 11 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 176).take 11 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 176 4 7 180 11 rfl rfl columns176_binding columnsNode180_7

theorem columnsNode164_23 : (data.columns.drop 164).take 23 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 164).take 23 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 164 12 11 176 23 rfl rfl columnsNode164_12 columnsNode176_11

theorem columnsNode140_47 : (data.columns.drop 140).take 47 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 140).take 47 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 140 24 23 164 47 rfl rfl columnsNode140_24 columnsNode164_23

theorem columnsNode92_95 : (data.columns.drop 92).take 95 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 92).take 95 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 92 48 47 140 95 rfl rfl columnsNode92_48 columnsNode140_47

theorem columnsNode0_187 : (data.columns.drop 0).take 187 = ((original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))).drop 0).take 187 :=
  NumericWorkerPortChecks.merge_at data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 0 92 95 92 187 rfl rfl columnsNode0_92 columnsNode92_95

theorem columns_binding : data.columns = (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) :=
  NumericQueryFrameChecks.complete_binding data.columns (original.columns.map (fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))) 187
    (by decide +kernel) (by decide +kernel) columnsNode0_187

numeric_data_binding bounds0_view : (data.bounds.drop 0).take 16 = (bounds0.bounds.drop 0).take 16

numeric_data_binding bounds0_piece : (bounds0.bounds.drop 0).take 16 = (original.bounds.drop 0).take 16

theorem bounds0_binding : (data.bounds.drop 0).take 16 = (original.bounds.drop 0).take 16 :=
  bounds0_view.trans bounds0_piece

numeric_data_binding bounds16_view : (data.bounds.drop 16).take 12 = (bounds0.bounds.drop 16).take 12

numeric_data_binding bounds16_piece : (bounds0.bounds.drop 16).take 12 = (original.bounds.drop 16).take 12

theorem bounds16_binding : (data.bounds.drop 16).take 12 = (original.bounds.drop 16).take 12 :=
  bounds16_view.trans bounds16_piece

theorem boundsNode0_28 : (data.bounds.drop 0).take 28 = (original.bounds.drop 0).take 28 :=
  NumericWorkerPortChecks.merge_at data.bounds original.bounds 0 16 12 16 28 rfl rfl bounds0_binding bounds16_binding

theorem bounds_binding : data.bounds = original.bounds :=
  NumericQueryFrameChecks.complete_binding data.bounds original.bounds 28
    (by decide +kernel) (by decide +kernel) boundsNode0_28

theorem source_binding : data = NumericWorkerPortChecks.encode original := by
  simpa only [data, NumericWorkerPortChecks.encode] using
    congrArg₂ NumericWorkerPortChecks.Data.mk columns_binding bounds_binding

end Airbender.Compiler.WorkerPortChecks.KeccakCached
