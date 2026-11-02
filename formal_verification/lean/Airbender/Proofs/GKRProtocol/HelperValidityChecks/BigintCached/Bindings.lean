import Airbender.Proofs.GKRProtocol.HelperValidityChecks.BigintCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HelperValidityChecks.BigintCached
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

numeric_data_binding protectedFields40_view : (data.protectedFields.drop 40).take 2 = protectedFields40.protectedFields

numeric_data_binding protectedFields40_piece : protectedFields40.protectedFields = (original.protectedFields.drop 40).take 2

theorem protectedFields40_binding : (data.protectedFields.drop 40).take 2 = (original.protectedFields.drop 40).take 2 :=
  protectedFields40_view.trans protectedFields40_piece

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

theorem protectedFieldsNode36_6 : (data.protectedFields.drop 36).take 6 = (original.protectedFields.drop 36).take 6 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 36 4 2 40 6 rfl rfl protectedFields36_binding protectedFields40_binding

theorem protectedFieldsNode32_10 : (data.protectedFields.drop 32).take 10 = (original.protectedFields.drop 32).take 10 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 32 4 6 36 10 rfl rfl protectedFields32_binding protectedFieldsNode36_6

theorem protectedFieldsNode20_22 : (data.protectedFields.drop 20).take 22 = (original.protectedFields.drop 20).take 22 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 20 12 10 32 22 rfl rfl protectedFieldsNode20_12 protectedFieldsNode32_10

theorem protectedFieldsNode0_42 : (data.protectedFields.drop 0).take 42 = (original.protectedFields.drop 0).take 42 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 0 20 22 20 42 rfl rfl protectedFieldsNode0_20 protectedFieldsNode20_22

theorem protectedFields_binding : data.protectedFields = original.protectedFields :=
  NumericQueryFrameChecks.complete_binding data.protectedFields original.protectedFields 42
    (by decide +kernel) (by decide +kernel) protectedFieldsNode0_42

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

numeric_data_binding borrows40_view : (data.borrows.drop 40).take 1 = borrows40.borrows

numeric_data_binding borrows40_piece : borrows40.borrows = (original.borrows.drop 40).take 1

theorem borrows40_binding : (data.borrows.drop 40).take 1 = (original.borrows.drop 40).take 1 :=
  borrows40_view.trans borrows40_piece

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

theorem borrowsNode36_5 : (data.borrows.drop 36).take 5 = (original.borrows.drop 36).take 5 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 36 4 1 40 5 rfl rfl borrows36_binding borrows40_binding

theorem borrowsNode32_9 : (data.borrows.drop 32).take 9 = (original.borrows.drop 32).take 9 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 32 4 5 36 9 rfl rfl borrows32_binding borrowsNode36_5

theorem borrowsNode20_21 : (data.borrows.drop 20).take 21 = (original.borrows.drop 20).take 21 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 20 12 9 32 21 rfl rfl borrowsNode20_12 borrowsNode32_9

theorem borrowsNode0_41 : (data.borrows.drop 0).take 41 = (original.borrows.drop 0).take 41 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 0 20 21 20 41 rfl rfl borrowsNode0_20 borrowsNode20_21

theorem borrows_binding : data.borrows = original.borrows :=
  NumericQueryFrameChecks.complete_binding data.borrows original.borrows 41
    (by decide +kernel) (by decide +kernel) borrowsNode0_41

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

numeric_data_binding transports40_view : (data.transports.drop 40).take 1 = transports40.transports

numeric_data_binding transports40_piece : transports40.transports = (original.transports.drop 40).take 1

theorem transports40_binding : (data.transports.drop 40).take 1 = (original.transports.drop 40).take 1 :=
  transports40_view.trans transports40_piece

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

theorem transportsNode36_5 : (data.transports.drop 36).take 5 = (original.transports.drop 36).take 5 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 36 4 1 40 5 rfl rfl transports36_binding transports40_binding

theorem transportsNode32_9 : (data.transports.drop 32).take 9 = (original.transports.drop 32).take 9 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 32 4 5 36 9 rfl rfl transports32_binding transportsNode36_5

theorem transportsNode20_21 : (data.transports.drop 20).take 21 = (original.transports.drop 20).take 21 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 20 12 9 32 21 rfl rfl transportsNode20_12 transportsNode32_9

theorem transportsNode0_41 : (data.transports.drop 0).take 41 = (original.transports.drop 0).take 41 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 0 20 21 20 41 rfl rfl transportsNode0_20 transportsNode20_21

theorem transports_binding : data.transports = original.transports :=
  NumericQueryFrameChecks.complete_binding data.transports original.transports 41
    (by decide +kernel) (by decide +kernel) transportsNode0_41

theorem source_binding : data = original :=
  NumericHelperValidityChecks.capture_eq data original coordinates_binding borrowBound_binding
    protectedFields_binding borrows_binding transports_binding

end Airbender.Compiler.HelperValidityChecks.BigintCached
