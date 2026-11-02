import Airbender.Proofs.GKRProtocol.HelperValidityChecks.BlakeRoundCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HelperValidityChecks.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

attribute [local irreducible] original data

numeric_data_binding coordinates_binding : data.coordinates = original.coordinates

numeric_data_binding borrowBound_binding : data.borrowBound = original.borrowBound

numeric_data_binding protectedFields0_view : (data.protectedFields.drop 0).take 4 = protectedFields0.protectedFields

numeric_data_binding protectedFields0_piece : protectedFields0.protectedFields = (original.protectedFields.drop 0).take 4

theorem protectedFields0_binding : (data.protectedFields.drop 0).take 4 = (original.protectedFields.drop 0).take 4 :=
  protectedFields0_view.trans protectedFields0_piece

numeric_data_binding protectedFields4_view : (data.protectedFields.drop 4).take 4 = protectedFields4.protectedFields

numeric_data_binding protectedFields4_piece : protectedFields4.protectedFields = (original.protectedFields.drop 4).take 4

theorem protectedFields4_binding : (data.protectedFields.drop 4).take 4 = (original.protectedFields.drop 4).take 4 :=
  protectedFields4_view.trans protectedFields4_piece

numeric_data_binding protectedFields8_view : (data.protectedFields.drop 8).take 4 = protectedFields8.protectedFields

numeric_data_binding protectedFields8_piece : protectedFields8.protectedFields = (original.protectedFields.drop 8).take 4

theorem protectedFields8_binding : (data.protectedFields.drop 8).take 4 = (original.protectedFields.drop 8).take 4 :=
  protectedFields8_view.trans protectedFields8_piece

numeric_data_binding protectedFields12_view : (data.protectedFields.drop 12).take 4 = protectedFields12.protectedFields

numeric_data_binding protectedFields12_piece : protectedFields12.protectedFields = (original.protectedFields.drop 12).take 4

theorem protectedFields12_binding : (data.protectedFields.drop 12).take 4 = (original.protectedFields.drop 12).take 4 :=
  protectedFields12_view.trans protectedFields12_piece

numeric_data_binding protectedFields16_view : (data.protectedFields.drop 16).take 4 = protectedFields16.protectedFields

numeric_data_binding protectedFields16_piece : protectedFields16.protectedFields = (original.protectedFields.drop 16).take 4

theorem protectedFields16_binding : (data.protectedFields.drop 16).take 4 = (original.protectedFields.drop 16).take 4 :=
  protectedFields16_view.trans protectedFields16_piece

numeric_data_binding protectedFields20_view : (data.protectedFields.drop 20).take 4 = protectedFields20.protectedFields

numeric_data_binding protectedFields20_piece : protectedFields20.protectedFields = (original.protectedFields.drop 20).take 4

theorem protectedFields20_binding : (data.protectedFields.drop 20).take 4 = (original.protectedFields.drop 20).take 4 :=
  protectedFields20_view.trans protectedFields20_piece

numeric_data_binding protectedFields24_view : (data.protectedFields.drop 24).take 4 = protectedFields24.protectedFields

numeric_data_binding protectedFields24_piece : protectedFields24.protectedFields = (original.protectedFields.drop 24).take 4

theorem protectedFields24_binding : (data.protectedFields.drop 24).take 4 = (original.protectedFields.drop 24).take 4 :=
  protectedFields24_view.trans protectedFields24_piece

numeric_data_binding protectedFields28_view : (data.protectedFields.drop 28).take 4 = protectedFields28.protectedFields

numeric_data_binding protectedFields28_piece : protectedFields28.protectedFields = (original.protectedFields.drop 28).take 4

theorem protectedFields28_binding : (data.protectedFields.drop 28).take 4 = (original.protectedFields.drop 28).take 4 :=
  protectedFields28_view.trans protectedFields28_piece

numeric_data_binding protectedFields32_view : (data.protectedFields.drop 32).take 4 = protectedFields32.protectedFields

numeric_data_binding protectedFields32_piece : protectedFields32.protectedFields = (original.protectedFields.drop 32).take 4

theorem protectedFields32_binding : (data.protectedFields.drop 32).take 4 = (original.protectedFields.drop 32).take 4 :=
  protectedFields32_view.trans protectedFields32_piece

numeric_data_binding protectedFields36_view : (data.protectedFields.drop 36).take 4 = protectedFields36.protectedFields

numeric_data_binding protectedFields36_piece : protectedFields36.protectedFields = (original.protectedFields.drop 36).take 4

theorem protectedFields36_binding : (data.protectedFields.drop 36).take 4 = (original.protectedFields.drop 36).take 4 :=
  protectedFields36_view.trans protectedFields36_piece

numeric_data_binding protectedFields40_view : (data.protectedFields.drop 40).take 4 = protectedFields40.protectedFields

numeric_data_binding protectedFields40_piece : protectedFields40.protectedFields = (original.protectedFields.drop 40).take 4

theorem protectedFields40_binding : (data.protectedFields.drop 40).take 4 = (original.protectedFields.drop 40).take 4 :=
  protectedFields40_view.trans protectedFields40_piece

numeric_data_binding protectedFields44_view : (data.protectedFields.drop 44).take 4 = protectedFields44.protectedFields

numeric_data_binding protectedFields44_piece : protectedFields44.protectedFields = (original.protectedFields.drop 44).take 4

theorem protectedFields44_binding : (data.protectedFields.drop 44).take 4 = (original.protectedFields.drop 44).take 4 :=
  protectedFields44_view.trans protectedFields44_piece

numeric_data_binding protectedFields48_view : (data.protectedFields.drop 48).take 4 = protectedFields48.protectedFields

numeric_data_binding protectedFields48_piece : protectedFields48.protectedFields = (original.protectedFields.drop 48).take 4

theorem protectedFields48_binding : (data.protectedFields.drop 48).take 4 = (original.protectedFields.drop 48).take 4 :=
  protectedFields48_view.trans protectedFields48_piece

numeric_data_binding protectedFields52_view : (data.protectedFields.drop 52).take 4 = protectedFields52.protectedFields

numeric_data_binding protectedFields52_piece : protectedFields52.protectedFields = (original.protectedFields.drop 52).take 4

theorem protectedFields52_binding : (data.protectedFields.drop 52).take 4 = (original.protectedFields.drop 52).take 4 :=
  protectedFields52_view.trans protectedFields52_piece

numeric_data_binding protectedFields56_view : (data.protectedFields.drop 56).take 4 = protectedFields56.protectedFields

numeric_data_binding protectedFields56_piece : protectedFields56.protectedFields = (original.protectedFields.drop 56).take 4

theorem protectedFields56_binding : (data.protectedFields.drop 56).take 4 = (original.protectedFields.drop 56).take 4 :=
  protectedFields56_view.trans protectedFields56_piece

numeric_data_binding protectedFields60_view : (data.protectedFields.drop 60).take 4 = protectedFields60.protectedFields

numeric_data_binding protectedFields60_piece : protectedFields60.protectedFields = (original.protectedFields.drop 60).take 4

theorem protectedFields60_binding : (data.protectedFields.drop 60).take 4 = (original.protectedFields.drop 60).take 4 :=
  protectedFields60_view.trans protectedFields60_piece

numeric_data_binding protectedFields64_view : (data.protectedFields.drop 64).take 4 = protectedFields64.protectedFields

numeric_data_binding protectedFields64_piece : protectedFields64.protectedFields = (original.protectedFields.drop 64).take 4

theorem protectedFields64_binding : (data.protectedFields.drop 64).take 4 = (original.protectedFields.drop 64).take 4 :=
  protectedFields64_view.trans protectedFields64_piece

numeric_data_binding protectedFields68_view : (data.protectedFields.drop 68).take 4 = protectedFields68.protectedFields

numeric_data_binding protectedFields68_piece : protectedFields68.protectedFields = (original.protectedFields.drop 68).take 4

theorem protectedFields68_binding : (data.protectedFields.drop 68).take 4 = (original.protectedFields.drop 68).take 4 :=
  protectedFields68_view.trans protectedFields68_piece

numeric_data_binding protectedFields72_view : (data.protectedFields.drop 72).take 4 = protectedFields72.protectedFields

numeric_data_binding protectedFields72_piece : protectedFields72.protectedFields = (original.protectedFields.drop 72).take 4

theorem protectedFields72_binding : (data.protectedFields.drop 72).take 4 = (original.protectedFields.drop 72).take 4 :=
  protectedFields72_view.trans protectedFields72_piece

numeric_data_binding protectedFields76_view : (data.protectedFields.drop 76).take 4 = protectedFields76.protectedFields

numeric_data_binding protectedFields76_piece : protectedFields76.protectedFields = (original.protectedFields.drop 76).take 4

theorem protectedFields76_binding : (data.protectedFields.drop 76).take 4 = (original.protectedFields.drop 76).take 4 :=
  protectedFields76_view.trans protectedFields76_piece

numeric_data_binding protectedFields80_view : (data.protectedFields.drop 80).take 4 = protectedFields80.protectedFields

numeric_data_binding protectedFields80_piece : protectedFields80.protectedFields = (original.protectedFields.drop 80).take 4

theorem protectedFields80_binding : (data.protectedFields.drop 80).take 4 = (original.protectedFields.drop 80).take 4 :=
  protectedFields80_view.trans protectedFields80_piece

numeric_data_binding protectedFields84_view : (data.protectedFields.drop 84).take 4 = protectedFields84.protectedFields

numeric_data_binding protectedFields84_piece : protectedFields84.protectedFields = (original.protectedFields.drop 84).take 4

theorem protectedFields84_binding : (data.protectedFields.drop 84).take 4 = (original.protectedFields.drop 84).take 4 :=
  protectedFields84_view.trans protectedFields84_piece

numeric_data_binding protectedFields88_view : (data.protectedFields.drop 88).take 2 = protectedFields88.protectedFields

numeric_data_binding protectedFields88_piece : protectedFields88.protectedFields = (original.protectedFields.drop 88).take 2

theorem protectedFields88_binding : (data.protectedFields.drop 88).take 2 = (original.protectedFields.drop 88).take 2 :=
  protectedFields88_view.trans protectedFields88_piece

theorem protectedFieldsNode0_8 : (data.protectedFields.drop 0).take 8 = (original.protectedFields.drop 0).take 8 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 0 4 4 4 8 rfl rfl protectedFields0_binding protectedFields4_binding

theorem protectedFieldsNode12_8 : (data.protectedFields.drop 12).take 8 = (original.protectedFields.drop 12).take 8 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 12 4 4 16 8 rfl rfl protectedFields12_binding protectedFields16_binding

theorem protectedFieldsNode8_12 : (data.protectedFields.drop 8).take 12 = (original.protectedFields.drop 8).take 12 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 8 4 8 12 12 rfl rfl protectedFields8_binding protectedFieldsNode12_8

theorem protectedFieldsNode0_20 : (data.protectedFields.drop 0).take 20 = (original.protectedFields.drop 0).take 20 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 0 8 12 8 20 rfl rfl protectedFieldsNode0_8 protectedFieldsNode8_12

theorem protectedFieldsNode24_8 : (data.protectedFields.drop 24).take 8 = (original.protectedFields.drop 24).take 8 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 24 4 4 28 8 rfl rfl protectedFields24_binding protectedFields28_binding

theorem protectedFieldsNode20_12 : (data.protectedFields.drop 20).take 12 = (original.protectedFields.drop 20).take 12 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 20 4 8 24 12 rfl rfl protectedFields20_binding protectedFieldsNode24_8

theorem protectedFieldsNode36_8 : (data.protectedFields.drop 36).take 8 = (original.protectedFields.drop 36).take 8 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 36 4 4 40 8 rfl rfl protectedFields36_binding protectedFields40_binding

theorem protectedFieldsNode32_12 : (data.protectedFields.drop 32).take 12 = (original.protectedFields.drop 32).take 12 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 32 4 8 36 12 rfl rfl protectedFields32_binding protectedFieldsNode36_8

theorem protectedFieldsNode20_24 : (data.protectedFields.drop 20).take 24 = (original.protectedFields.drop 20).take 24 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 20 12 12 32 24 rfl rfl protectedFieldsNode20_12 protectedFieldsNode32_12

theorem protectedFieldsNode0_44 : (data.protectedFields.drop 0).take 44 = (original.protectedFields.drop 0).take 44 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 0 20 24 20 44 rfl rfl protectedFieldsNode0_20 protectedFieldsNode20_24

theorem protectedFieldsNode48_8 : (data.protectedFields.drop 48).take 8 = (original.protectedFields.drop 48).take 8 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 48 4 4 52 8 rfl rfl protectedFields48_binding protectedFields52_binding

theorem protectedFieldsNode44_12 : (data.protectedFields.drop 44).take 12 = (original.protectedFields.drop 44).take 12 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 44 4 8 48 12 rfl rfl protectedFields44_binding protectedFieldsNode48_8

theorem protectedFieldsNode60_8 : (data.protectedFields.drop 60).take 8 = (original.protectedFields.drop 60).take 8 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 60 4 4 64 8 rfl rfl protectedFields60_binding protectedFields64_binding

theorem protectedFieldsNode56_12 : (data.protectedFields.drop 56).take 12 = (original.protectedFields.drop 56).take 12 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 56 4 8 60 12 rfl rfl protectedFields56_binding protectedFieldsNode60_8

theorem protectedFieldsNode44_24 : (data.protectedFields.drop 44).take 24 = (original.protectedFields.drop 44).take 24 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 44 12 12 56 24 rfl rfl protectedFieldsNode44_12 protectedFieldsNode56_12

theorem protectedFieldsNode72_8 : (data.protectedFields.drop 72).take 8 = (original.protectedFields.drop 72).take 8 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 72 4 4 76 8 rfl rfl protectedFields72_binding protectedFields76_binding

theorem protectedFieldsNode68_12 : (data.protectedFields.drop 68).take 12 = (original.protectedFields.drop 68).take 12 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 68 4 8 72 12 rfl rfl protectedFields68_binding protectedFieldsNode72_8

theorem protectedFieldsNode84_6 : (data.protectedFields.drop 84).take 6 = (original.protectedFields.drop 84).take 6 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 84 4 2 88 6 rfl rfl protectedFields84_binding protectedFields88_binding

theorem protectedFieldsNode80_10 : (data.protectedFields.drop 80).take 10 = (original.protectedFields.drop 80).take 10 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 80 4 6 84 10 rfl rfl protectedFields80_binding protectedFieldsNode84_6

theorem protectedFieldsNode68_22 : (data.protectedFields.drop 68).take 22 = (original.protectedFields.drop 68).take 22 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 68 12 10 80 22 rfl rfl protectedFieldsNode68_12 protectedFieldsNode80_10

theorem protectedFieldsNode44_46 : (data.protectedFields.drop 44).take 46 = (original.protectedFields.drop 44).take 46 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 44 24 22 68 46 rfl rfl protectedFieldsNode44_24 protectedFieldsNode68_22

theorem protectedFieldsNode0_90 : (data.protectedFields.drop 0).take 90 = (original.protectedFields.drop 0).take 90 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 0 44 46 44 90 rfl rfl protectedFieldsNode0_44 protectedFieldsNode44_46

theorem protectedFields_binding : data.protectedFields = original.protectedFields :=
  NumericQueryFrameChecks.complete_binding data.protectedFields original.protectedFields 90
    (by decide +kernel) (by decide +kernel) protectedFieldsNode0_90

numeric_data_binding borrows0_view : (data.borrows.drop 0).take 4 = borrows0.borrows

numeric_data_binding borrows0_piece : borrows0.borrows = (original.borrows.drop 0).take 4

theorem borrows0_binding : (data.borrows.drop 0).take 4 = (original.borrows.drop 0).take 4 :=
  borrows0_view.trans borrows0_piece

numeric_data_binding borrows4_view : (data.borrows.drop 4).take 4 = borrows4.borrows

numeric_data_binding borrows4_piece : borrows4.borrows = (original.borrows.drop 4).take 4

theorem borrows4_binding : (data.borrows.drop 4).take 4 = (original.borrows.drop 4).take 4 :=
  borrows4_view.trans borrows4_piece

numeric_data_binding borrows8_view : (data.borrows.drop 8).take 4 = borrows8.borrows

numeric_data_binding borrows8_piece : borrows8.borrows = (original.borrows.drop 8).take 4

theorem borrows8_binding : (data.borrows.drop 8).take 4 = (original.borrows.drop 8).take 4 :=
  borrows8_view.trans borrows8_piece

numeric_data_binding borrows12_view : (data.borrows.drop 12).take 4 = borrows12.borrows

numeric_data_binding borrows12_piece : borrows12.borrows = (original.borrows.drop 12).take 4

theorem borrows12_binding : (data.borrows.drop 12).take 4 = (original.borrows.drop 12).take 4 :=
  borrows12_view.trans borrows12_piece

numeric_data_binding borrows16_view : (data.borrows.drop 16).take 4 = borrows16.borrows

numeric_data_binding borrows16_piece : borrows16.borrows = (original.borrows.drop 16).take 4

theorem borrows16_binding : (data.borrows.drop 16).take 4 = (original.borrows.drop 16).take 4 :=
  borrows16_view.trans borrows16_piece

numeric_data_binding borrows20_view : (data.borrows.drop 20).take 4 = borrows20.borrows

numeric_data_binding borrows20_piece : borrows20.borrows = (original.borrows.drop 20).take 4

theorem borrows20_binding : (data.borrows.drop 20).take 4 = (original.borrows.drop 20).take 4 :=
  borrows20_view.trans borrows20_piece

numeric_data_binding borrows24_view : (data.borrows.drop 24).take 4 = borrows24.borrows

numeric_data_binding borrows24_piece : borrows24.borrows = (original.borrows.drop 24).take 4

theorem borrows24_binding : (data.borrows.drop 24).take 4 = (original.borrows.drop 24).take 4 :=
  borrows24_view.trans borrows24_piece

numeric_data_binding borrows28_view : (data.borrows.drop 28).take 4 = borrows28.borrows

numeric_data_binding borrows28_piece : borrows28.borrows = (original.borrows.drop 28).take 4

theorem borrows28_binding : (data.borrows.drop 28).take 4 = (original.borrows.drop 28).take 4 :=
  borrows28_view.trans borrows28_piece

numeric_data_binding borrows32_view : (data.borrows.drop 32).take 4 = borrows32.borrows

numeric_data_binding borrows32_piece : borrows32.borrows = (original.borrows.drop 32).take 4

theorem borrows32_binding : (data.borrows.drop 32).take 4 = (original.borrows.drop 32).take 4 :=
  borrows32_view.trans borrows32_piece

numeric_data_binding borrows36_view : (data.borrows.drop 36).take 4 = borrows36.borrows

numeric_data_binding borrows36_piece : borrows36.borrows = (original.borrows.drop 36).take 4

theorem borrows36_binding : (data.borrows.drop 36).take 4 = (original.borrows.drop 36).take 4 :=
  borrows36_view.trans borrows36_piece

numeric_data_binding borrows40_view : (data.borrows.drop 40).take 4 = borrows40.borrows

numeric_data_binding borrows40_piece : borrows40.borrows = (original.borrows.drop 40).take 4

theorem borrows40_binding : (data.borrows.drop 40).take 4 = (original.borrows.drop 40).take 4 :=
  borrows40_view.trans borrows40_piece

numeric_data_binding borrows44_view : (data.borrows.drop 44).take 4 = borrows44.borrows

numeric_data_binding borrows44_piece : borrows44.borrows = (original.borrows.drop 44).take 4

theorem borrows44_binding : (data.borrows.drop 44).take 4 = (original.borrows.drop 44).take 4 :=
  borrows44_view.trans borrows44_piece

numeric_data_binding borrows48_view : (data.borrows.drop 48).take 4 = borrows48.borrows

numeric_data_binding borrows48_piece : borrows48.borrows = (original.borrows.drop 48).take 4

theorem borrows48_binding : (data.borrows.drop 48).take 4 = (original.borrows.drop 48).take 4 :=
  borrows48_view.trans borrows48_piece

numeric_data_binding borrows52_view : (data.borrows.drop 52).take 4 = borrows52.borrows

numeric_data_binding borrows52_piece : borrows52.borrows = (original.borrows.drop 52).take 4

theorem borrows52_binding : (data.borrows.drop 52).take 4 = (original.borrows.drop 52).take 4 :=
  borrows52_view.trans borrows52_piece

numeric_data_binding borrows56_view : (data.borrows.drop 56).take 4 = borrows56.borrows

numeric_data_binding borrows56_piece : borrows56.borrows = (original.borrows.drop 56).take 4

theorem borrows56_binding : (data.borrows.drop 56).take 4 = (original.borrows.drop 56).take 4 :=
  borrows56_view.trans borrows56_piece

numeric_data_binding borrows60_view : (data.borrows.drop 60).take 4 = borrows60.borrows

numeric_data_binding borrows60_piece : borrows60.borrows = (original.borrows.drop 60).take 4

theorem borrows60_binding : (data.borrows.drop 60).take 4 = (original.borrows.drop 60).take 4 :=
  borrows60_view.trans borrows60_piece

numeric_data_binding borrows64_view : (data.borrows.drop 64).take 4 = borrows64.borrows

numeric_data_binding borrows64_piece : borrows64.borrows = (original.borrows.drop 64).take 4

theorem borrows64_binding : (data.borrows.drop 64).take 4 = (original.borrows.drop 64).take 4 :=
  borrows64_view.trans borrows64_piece

numeric_data_binding borrows68_view : (data.borrows.drop 68).take 4 = borrows68.borrows

numeric_data_binding borrows68_piece : borrows68.borrows = (original.borrows.drop 68).take 4

theorem borrows68_binding : (data.borrows.drop 68).take 4 = (original.borrows.drop 68).take 4 :=
  borrows68_view.trans borrows68_piece

numeric_data_binding borrows72_view : (data.borrows.drop 72).take 4 = borrows72.borrows

numeric_data_binding borrows72_piece : borrows72.borrows = (original.borrows.drop 72).take 4

theorem borrows72_binding : (data.borrows.drop 72).take 4 = (original.borrows.drop 72).take 4 :=
  borrows72_view.trans borrows72_piece

numeric_data_binding borrows76_view : (data.borrows.drop 76).take 4 = borrows76.borrows

numeric_data_binding borrows76_piece : borrows76.borrows = (original.borrows.drop 76).take 4

theorem borrows76_binding : (data.borrows.drop 76).take 4 = (original.borrows.drop 76).take 4 :=
  borrows76_view.trans borrows76_piece

numeric_data_binding borrows80_view : (data.borrows.drop 80).take 4 = borrows80.borrows

numeric_data_binding borrows80_piece : borrows80.borrows = (original.borrows.drop 80).take 4

theorem borrows80_binding : (data.borrows.drop 80).take 4 = (original.borrows.drop 80).take 4 :=
  borrows80_view.trans borrows80_piece

numeric_data_binding borrows84_view : (data.borrows.drop 84).take 4 = borrows84.borrows

numeric_data_binding borrows84_piece : borrows84.borrows = (original.borrows.drop 84).take 4

theorem borrows84_binding : (data.borrows.drop 84).take 4 = (original.borrows.drop 84).take 4 :=
  borrows84_view.trans borrows84_piece

numeric_data_binding borrows88_view : (data.borrows.drop 88).take 1 = borrows88.borrows

numeric_data_binding borrows88_piece : borrows88.borrows = (original.borrows.drop 88).take 1

theorem borrows88_binding : (data.borrows.drop 88).take 1 = (original.borrows.drop 88).take 1 :=
  borrows88_view.trans borrows88_piece

theorem borrowsNode0_8 : (data.borrows.drop 0).take 8 = (original.borrows.drop 0).take 8 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 0 4 4 4 8 rfl rfl borrows0_binding borrows4_binding

theorem borrowsNode12_8 : (data.borrows.drop 12).take 8 = (original.borrows.drop 12).take 8 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 12 4 4 16 8 rfl rfl borrows12_binding borrows16_binding

theorem borrowsNode8_12 : (data.borrows.drop 8).take 12 = (original.borrows.drop 8).take 12 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 8 4 8 12 12 rfl rfl borrows8_binding borrowsNode12_8

theorem borrowsNode0_20 : (data.borrows.drop 0).take 20 = (original.borrows.drop 0).take 20 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 0 8 12 8 20 rfl rfl borrowsNode0_8 borrowsNode8_12

theorem borrowsNode24_8 : (data.borrows.drop 24).take 8 = (original.borrows.drop 24).take 8 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 24 4 4 28 8 rfl rfl borrows24_binding borrows28_binding

theorem borrowsNode20_12 : (data.borrows.drop 20).take 12 = (original.borrows.drop 20).take 12 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 20 4 8 24 12 rfl rfl borrows20_binding borrowsNode24_8

theorem borrowsNode36_8 : (data.borrows.drop 36).take 8 = (original.borrows.drop 36).take 8 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 36 4 4 40 8 rfl rfl borrows36_binding borrows40_binding

theorem borrowsNode32_12 : (data.borrows.drop 32).take 12 = (original.borrows.drop 32).take 12 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 32 4 8 36 12 rfl rfl borrows32_binding borrowsNode36_8

theorem borrowsNode20_24 : (data.borrows.drop 20).take 24 = (original.borrows.drop 20).take 24 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 20 12 12 32 24 rfl rfl borrowsNode20_12 borrowsNode32_12

theorem borrowsNode0_44 : (data.borrows.drop 0).take 44 = (original.borrows.drop 0).take 44 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 0 20 24 20 44 rfl rfl borrowsNode0_20 borrowsNode20_24

theorem borrowsNode48_8 : (data.borrows.drop 48).take 8 = (original.borrows.drop 48).take 8 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 48 4 4 52 8 rfl rfl borrows48_binding borrows52_binding

theorem borrowsNode44_12 : (data.borrows.drop 44).take 12 = (original.borrows.drop 44).take 12 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 44 4 8 48 12 rfl rfl borrows44_binding borrowsNode48_8

theorem borrowsNode60_8 : (data.borrows.drop 60).take 8 = (original.borrows.drop 60).take 8 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 60 4 4 64 8 rfl rfl borrows60_binding borrows64_binding

theorem borrowsNode56_12 : (data.borrows.drop 56).take 12 = (original.borrows.drop 56).take 12 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 56 4 8 60 12 rfl rfl borrows56_binding borrowsNode60_8

theorem borrowsNode44_24 : (data.borrows.drop 44).take 24 = (original.borrows.drop 44).take 24 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 44 12 12 56 24 rfl rfl borrowsNode44_12 borrowsNode56_12

theorem borrowsNode72_8 : (data.borrows.drop 72).take 8 = (original.borrows.drop 72).take 8 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 72 4 4 76 8 rfl rfl borrows72_binding borrows76_binding

theorem borrowsNode68_12 : (data.borrows.drop 68).take 12 = (original.borrows.drop 68).take 12 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 68 4 8 72 12 rfl rfl borrows68_binding borrowsNode72_8

theorem borrowsNode84_5 : (data.borrows.drop 84).take 5 = (original.borrows.drop 84).take 5 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 84 4 1 88 5 rfl rfl borrows84_binding borrows88_binding

theorem borrowsNode80_9 : (data.borrows.drop 80).take 9 = (original.borrows.drop 80).take 9 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 80 4 5 84 9 rfl rfl borrows80_binding borrowsNode84_5

theorem borrowsNode68_21 : (data.borrows.drop 68).take 21 = (original.borrows.drop 68).take 21 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 68 12 9 80 21 rfl rfl borrowsNode68_12 borrowsNode80_9

theorem borrowsNode44_45 : (data.borrows.drop 44).take 45 = (original.borrows.drop 44).take 45 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 44 24 21 68 45 rfl rfl borrowsNode44_24 borrowsNode68_21

theorem borrowsNode0_89 : (data.borrows.drop 0).take 89 = (original.borrows.drop 0).take 89 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 0 44 45 44 89 rfl rfl borrowsNode0_44 borrowsNode44_45

theorem borrows_binding : data.borrows = original.borrows :=
  NumericQueryFrameChecks.complete_binding data.borrows original.borrows 89
    (by decide +kernel) (by decide +kernel) borrowsNode0_89

numeric_data_binding transports0_view : (data.transports.drop 0).take 4 = transports0.transports

numeric_data_binding transports0_piece : transports0.transports = (original.transports.drop 0).take 4

theorem transports0_binding : (data.transports.drop 0).take 4 = (original.transports.drop 0).take 4 :=
  transports0_view.trans transports0_piece

numeric_data_binding transports4_view : (data.transports.drop 4).take 4 = transports4.transports

numeric_data_binding transports4_piece : transports4.transports = (original.transports.drop 4).take 4

theorem transports4_binding : (data.transports.drop 4).take 4 = (original.transports.drop 4).take 4 :=
  transports4_view.trans transports4_piece

numeric_data_binding transports8_view : (data.transports.drop 8).take 4 = transports8.transports

numeric_data_binding transports8_piece : transports8.transports = (original.transports.drop 8).take 4

theorem transports8_binding : (data.transports.drop 8).take 4 = (original.transports.drop 8).take 4 :=
  transports8_view.trans transports8_piece

numeric_data_binding transports12_view : (data.transports.drop 12).take 4 = transports12.transports

numeric_data_binding transports12_piece : transports12.transports = (original.transports.drop 12).take 4

theorem transports12_binding : (data.transports.drop 12).take 4 = (original.transports.drop 12).take 4 :=
  transports12_view.trans transports12_piece

numeric_data_binding transports16_view : (data.transports.drop 16).take 4 = transports16.transports

numeric_data_binding transports16_piece : transports16.transports = (original.transports.drop 16).take 4

theorem transports16_binding : (data.transports.drop 16).take 4 = (original.transports.drop 16).take 4 :=
  transports16_view.trans transports16_piece

numeric_data_binding transports20_view : (data.transports.drop 20).take 4 = transports20.transports

numeric_data_binding transports20_piece : transports20.transports = (original.transports.drop 20).take 4

theorem transports20_binding : (data.transports.drop 20).take 4 = (original.transports.drop 20).take 4 :=
  transports20_view.trans transports20_piece

numeric_data_binding transports24_view : (data.transports.drop 24).take 4 = transports24.transports

numeric_data_binding transports24_piece : transports24.transports = (original.transports.drop 24).take 4

theorem transports24_binding : (data.transports.drop 24).take 4 = (original.transports.drop 24).take 4 :=
  transports24_view.trans transports24_piece

numeric_data_binding transports28_view : (data.transports.drop 28).take 4 = transports28.transports

numeric_data_binding transports28_piece : transports28.transports = (original.transports.drop 28).take 4

theorem transports28_binding : (data.transports.drop 28).take 4 = (original.transports.drop 28).take 4 :=
  transports28_view.trans transports28_piece

numeric_data_binding transports32_view : (data.transports.drop 32).take 4 = transports32.transports

numeric_data_binding transports32_piece : transports32.transports = (original.transports.drop 32).take 4

theorem transports32_binding : (data.transports.drop 32).take 4 = (original.transports.drop 32).take 4 :=
  transports32_view.trans transports32_piece

numeric_data_binding transports36_view : (data.transports.drop 36).take 4 = transports36.transports

numeric_data_binding transports36_piece : transports36.transports = (original.transports.drop 36).take 4

theorem transports36_binding : (data.transports.drop 36).take 4 = (original.transports.drop 36).take 4 :=
  transports36_view.trans transports36_piece

numeric_data_binding transports40_view : (data.transports.drop 40).take 4 = transports40.transports

numeric_data_binding transports40_piece : transports40.transports = (original.transports.drop 40).take 4

theorem transports40_binding : (data.transports.drop 40).take 4 = (original.transports.drop 40).take 4 :=
  transports40_view.trans transports40_piece

numeric_data_binding transports44_view : (data.transports.drop 44).take 4 = transports44.transports

numeric_data_binding transports44_piece : transports44.transports = (original.transports.drop 44).take 4

theorem transports44_binding : (data.transports.drop 44).take 4 = (original.transports.drop 44).take 4 :=
  transports44_view.trans transports44_piece

numeric_data_binding transports48_view : (data.transports.drop 48).take 4 = transports48.transports

numeric_data_binding transports48_piece : transports48.transports = (original.transports.drop 48).take 4

theorem transports48_binding : (data.transports.drop 48).take 4 = (original.transports.drop 48).take 4 :=
  transports48_view.trans transports48_piece

numeric_data_binding transports52_view : (data.transports.drop 52).take 4 = transports52.transports

numeric_data_binding transports52_piece : transports52.transports = (original.transports.drop 52).take 4

theorem transports52_binding : (data.transports.drop 52).take 4 = (original.transports.drop 52).take 4 :=
  transports52_view.trans transports52_piece

numeric_data_binding transports56_view : (data.transports.drop 56).take 4 = transports56.transports

numeric_data_binding transports56_piece : transports56.transports = (original.transports.drop 56).take 4

theorem transports56_binding : (data.transports.drop 56).take 4 = (original.transports.drop 56).take 4 :=
  transports56_view.trans transports56_piece

numeric_data_binding transports60_view : (data.transports.drop 60).take 4 = transports60.transports

numeric_data_binding transports60_piece : transports60.transports = (original.transports.drop 60).take 4

theorem transports60_binding : (data.transports.drop 60).take 4 = (original.transports.drop 60).take 4 :=
  transports60_view.trans transports60_piece

numeric_data_binding transports64_view : (data.transports.drop 64).take 4 = transports64.transports

numeric_data_binding transports64_piece : transports64.transports = (original.transports.drop 64).take 4

theorem transports64_binding : (data.transports.drop 64).take 4 = (original.transports.drop 64).take 4 :=
  transports64_view.trans transports64_piece

numeric_data_binding transports68_view : (data.transports.drop 68).take 4 = transports68.transports

numeric_data_binding transports68_piece : transports68.transports = (original.transports.drop 68).take 4

theorem transports68_binding : (data.transports.drop 68).take 4 = (original.transports.drop 68).take 4 :=
  transports68_view.trans transports68_piece

numeric_data_binding transports72_view : (data.transports.drop 72).take 4 = transports72.transports

numeric_data_binding transports72_piece : transports72.transports = (original.transports.drop 72).take 4

theorem transports72_binding : (data.transports.drop 72).take 4 = (original.transports.drop 72).take 4 :=
  transports72_view.trans transports72_piece

numeric_data_binding transports76_view : (data.transports.drop 76).take 4 = transports76.transports

numeric_data_binding transports76_piece : transports76.transports = (original.transports.drop 76).take 4

theorem transports76_binding : (data.transports.drop 76).take 4 = (original.transports.drop 76).take 4 :=
  transports76_view.trans transports76_piece

numeric_data_binding transports80_view : (data.transports.drop 80).take 4 = transports80.transports

numeric_data_binding transports80_piece : transports80.transports = (original.transports.drop 80).take 4

theorem transports80_binding : (data.transports.drop 80).take 4 = (original.transports.drop 80).take 4 :=
  transports80_view.trans transports80_piece

numeric_data_binding transports84_view : (data.transports.drop 84).take 4 = transports84.transports

numeric_data_binding transports84_piece : transports84.transports = (original.transports.drop 84).take 4

theorem transports84_binding : (data.transports.drop 84).take 4 = (original.transports.drop 84).take 4 :=
  transports84_view.trans transports84_piece

numeric_data_binding transports88_view : (data.transports.drop 88).take 1 = transports88.transports

numeric_data_binding transports88_piece : transports88.transports = (original.transports.drop 88).take 1

theorem transports88_binding : (data.transports.drop 88).take 1 = (original.transports.drop 88).take 1 :=
  transports88_view.trans transports88_piece

theorem transportsNode0_8 : (data.transports.drop 0).take 8 = (original.transports.drop 0).take 8 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 0 4 4 4 8 rfl rfl transports0_binding transports4_binding

theorem transportsNode12_8 : (data.transports.drop 12).take 8 = (original.transports.drop 12).take 8 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 12 4 4 16 8 rfl rfl transports12_binding transports16_binding

theorem transportsNode8_12 : (data.transports.drop 8).take 12 = (original.transports.drop 8).take 12 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 8 4 8 12 12 rfl rfl transports8_binding transportsNode12_8

theorem transportsNode0_20 : (data.transports.drop 0).take 20 = (original.transports.drop 0).take 20 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 0 8 12 8 20 rfl rfl transportsNode0_8 transportsNode8_12

theorem transportsNode24_8 : (data.transports.drop 24).take 8 = (original.transports.drop 24).take 8 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 24 4 4 28 8 rfl rfl transports24_binding transports28_binding

theorem transportsNode20_12 : (data.transports.drop 20).take 12 = (original.transports.drop 20).take 12 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 20 4 8 24 12 rfl rfl transports20_binding transportsNode24_8

theorem transportsNode36_8 : (data.transports.drop 36).take 8 = (original.transports.drop 36).take 8 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 36 4 4 40 8 rfl rfl transports36_binding transports40_binding

theorem transportsNode32_12 : (data.transports.drop 32).take 12 = (original.transports.drop 32).take 12 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 32 4 8 36 12 rfl rfl transports32_binding transportsNode36_8

theorem transportsNode20_24 : (data.transports.drop 20).take 24 = (original.transports.drop 20).take 24 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 20 12 12 32 24 rfl rfl transportsNode20_12 transportsNode32_12

theorem transportsNode0_44 : (data.transports.drop 0).take 44 = (original.transports.drop 0).take 44 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 0 20 24 20 44 rfl rfl transportsNode0_20 transportsNode20_24

theorem transportsNode48_8 : (data.transports.drop 48).take 8 = (original.transports.drop 48).take 8 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 48 4 4 52 8 rfl rfl transports48_binding transports52_binding

theorem transportsNode44_12 : (data.transports.drop 44).take 12 = (original.transports.drop 44).take 12 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 44 4 8 48 12 rfl rfl transports44_binding transportsNode48_8

theorem transportsNode60_8 : (data.transports.drop 60).take 8 = (original.transports.drop 60).take 8 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 60 4 4 64 8 rfl rfl transports60_binding transports64_binding

theorem transportsNode56_12 : (data.transports.drop 56).take 12 = (original.transports.drop 56).take 12 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 56 4 8 60 12 rfl rfl transports56_binding transportsNode60_8

theorem transportsNode44_24 : (data.transports.drop 44).take 24 = (original.transports.drop 44).take 24 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 44 12 12 56 24 rfl rfl transportsNode44_12 transportsNode56_12

theorem transportsNode72_8 : (data.transports.drop 72).take 8 = (original.transports.drop 72).take 8 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 72 4 4 76 8 rfl rfl transports72_binding transports76_binding

theorem transportsNode68_12 : (data.transports.drop 68).take 12 = (original.transports.drop 68).take 12 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 68 4 8 72 12 rfl rfl transports68_binding transportsNode72_8

theorem transportsNode84_5 : (data.transports.drop 84).take 5 = (original.transports.drop 84).take 5 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 84 4 1 88 5 rfl rfl transports84_binding transports88_binding

theorem transportsNode80_9 : (data.transports.drop 80).take 9 = (original.transports.drop 80).take 9 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 80 4 5 84 9 rfl rfl transports80_binding transportsNode84_5

theorem transportsNode68_21 : (data.transports.drop 68).take 21 = (original.transports.drop 68).take 21 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 68 12 9 80 21 rfl rfl transportsNode68_12 transportsNode80_9

theorem transportsNode44_45 : (data.transports.drop 44).take 45 = (original.transports.drop 44).take 45 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 44 24 21 68 45 rfl rfl transportsNode44_24 transportsNode68_21

theorem transportsNode0_89 : (data.transports.drop 0).take 89 = (original.transports.drop 0).take 89 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 0 44 45 44 89 rfl rfl transportsNode0_44 transportsNode44_45

theorem transports_binding : data.transports = original.transports :=
  NumericQueryFrameChecks.complete_binding data.transports original.transports 89
    (by decide +kernel) (by decide +kernel) transportsNode0_89

theorem source_binding : data = original :=
  NumericHelperValidityChecks.capture_eq data original coordinates_binding borrowBound_binding
    protectedFields_binding borrows_binding transports_binding

end Airbender.Compiler.HelperValidityChecks.BlakeRoundCached
