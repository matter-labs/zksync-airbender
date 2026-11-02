import Airbender.Proofs.GKRProtocol.HelperValidityChecks.KeccakUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HelperValidityChecks.KeccakUncached
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

numeric_data_binding protectedFields28_view : (data.protectedFields.drop 28).take 3 = protectedFields28.protectedFields

numeric_data_binding protectedFields28_piece : protectedFields28.protectedFields = (original.protectedFields.drop 28).take 3

theorem protectedFields28_binding : (data.protectedFields.drop 28).take 3 = (original.protectedFields.drop 28).take 3 :=
  protectedFields28_view.trans protectedFields28_piece

theorem protectedFieldsNode0_8 : (data.protectedFields.drop 0).take 8 = (original.protectedFields.drop 0).take 8 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 0 4 4 4 8 rfl rfl protectedFields0_binding protectedFields4_binding

theorem protectedFieldsNode8_8 : (data.protectedFields.drop 8).take 8 = (original.protectedFields.drop 8).take 8 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 8 4 4 12 8 rfl rfl protectedFields8_binding protectedFields12_binding

theorem protectedFieldsNode0_16 : (data.protectedFields.drop 0).take 16 = (original.protectedFields.drop 0).take 16 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 0 8 8 8 16 rfl rfl protectedFieldsNode0_8 protectedFieldsNode8_8

theorem protectedFieldsNode16_8 : (data.protectedFields.drop 16).take 8 = (original.protectedFields.drop 16).take 8 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 16 4 4 20 8 rfl rfl protectedFields16_binding protectedFields20_binding

theorem protectedFieldsNode24_7 : (data.protectedFields.drop 24).take 7 = (original.protectedFields.drop 24).take 7 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 24 4 3 28 7 rfl rfl protectedFields24_binding protectedFields28_binding

theorem protectedFieldsNode16_15 : (data.protectedFields.drop 16).take 15 = (original.protectedFields.drop 16).take 15 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 16 8 7 24 15 rfl rfl protectedFieldsNode16_8 protectedFieldsNode24_7

theorem protectedFieldsNode0_31 : (data.protectedFields.drop 0).take 31 = (original.protectedFields.drop 0).take 31 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 0 16 15 16 31 rfl rfl protectedFieldsNode0_16 protectedFieldsNode16_15

theorem protectedFields_binding : data.protectedFields = original.protectedFields :=
  NumericQueryFrameChecks.complete_binding data.protectedFields original.protectedFields 31
    (by decide +kernel) (by decide +kernel) protectedFieldsNode0_31

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

numeric_data_binding borrows28_view : (data.borrows.drop 28).take 2 = borrows28.borrows

numeric_data_binding borrows28_piece : borrows28.borrows = (original.borrows.drop 28).take 2

theorem borrows28_binding : (data.borrows.drop 28).take 2 = (original.borrows.drop 28).take 2 :=
  borrows28_view.trans borrows28_piece

theorem borrowsNode0_8 : (data.borrows.drop 0).take 8 = (original.borrows.drop 0).take 8 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 0 4 4 4 8 rfl rfl borrows0_binding borrows4_binding

theorem borrowsNode8_8 : (data.borrows.drop 8).take 8 = (original.borrows.drop 8).take 8 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 8 4 4 12 8 rfl rfl borrows8_binding borrows12_binding

theorem borrowsNode0_16 : (data.borrows.drop 0).take 16 = (original.borrows.drop 0).take 16 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 0 8 8 8 16 rfl rfl borrowsNode0_8 borrowsNode8_8

theorem borrowsNode16_8 : (data.borrows.drop 16).take 8 = (original.borrows.drop 16).take 8 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 16 4 4 20 8 rfl rfl borrows16_binding borrows20_binding

theorem borrowsNode24_6 : (data.borrows.drop 24).take 6 = (original.borrows.drop 24).take 6 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 24 4 2 28 6 rfl rfl borrows24_binding borrows28_binding

theorem borrowsNode16_14 : (data.borrows.drop 16).take 14 = (original.borrows.drop 16).take 14 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 16 8 6 24 14 rfl rfl borrowsNode16_8 borrowsNode24_6

theorem borrowsNode0_30 : (data.borrows.drop 0).take 30 = (original.borrows.drop 0).take 30 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 0 16 14 16 30 rfl rfl borrowsNode0_16 borrowsNode16_14

theorem borrows_binding : data.borrows = original.borrows :=
  NumericQueryFrameChecks.complete_binding data.borrows original.borrows 30
    (by decide +kernel) (by decide +kernel) borrowsNode0_30

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

numeric_data_binding transports28_view : (data.transports.drop 28).take 2 = transports28.transports

numeric_data_binding transports28_piece : transports28.transports = (original.transports.drop 28).take 2

theorem transports28_binding : (data.transports.drop 28).take 2 = (original.transports.drop 28).take 2 :=
  transports28_view.trans transports28_piece

theorem transportsNode0_8 : (data.transports.drop 0).take 8 = (original.transports.drop 0).take 8 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 0 4 4 4 8 rfl rfl transports0_binding transports4_binding

theorem transportsNode8_8 : (data.transports.drop 8).take 8 = (original.transports.drop 8).take 8 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 8 4 4 12 8 rfl rfl transports8_binding transports12_binding

theorem transportsNode0_16 : (data.transports.drop 0).take 16 = (original.transports.drop 0).take 16 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 0 8 8 8 16 rfl rfl transportsNode0_8 transportsNode8_8

theorem transportsNode16_8 : (data.transports.drop 16).take 8 = (original.transports.drop 16).take 8 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 16 4 4 20 8 rfl rfl transports16_binding transports20_binding

theorem transportsNode24_6 : (data.transports.drop 24).take 6 = (original.transports.drop 24).take 6 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 24 4 2 28 6 rfl rfl transports24_binding transports28_binding

theorem transportsNode16_14 : (data.transports.drop 16).take 14 = (original.transports.drop 16).take 14 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 16 8 6 24 14 rfl rfl transportsNode16_8 transportsNode24_6

theorem transportsNode0_30 : (data.transports.drop 0).take 30 = (original.transports.drop 0).take 30 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 0 16 14 16 30 rfl rfl transportsNode0_16 transportsNode16_14

theorem transports_binding : data.transports = original.transports :=
  NumericQueryFrameChecks.complete_binding data.transports original.transports 30
    (by decide +kernel) (by decide +kernel) transportsNode0_30

theorem source_binding : data = original :=
  NumericHelperValidityChecks.capture_eq data original coordinates_binding borrowBound_binding
    protectedFields_binding borrows_binding transports_binding

end Airbender.Compiler.HelperValidityChecks.KeccakUncached
