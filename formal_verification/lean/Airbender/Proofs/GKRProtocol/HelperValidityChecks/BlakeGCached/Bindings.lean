import Airbender.Proofs.GKRProtocol.HelperValidityChecks.BlakeGCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HelperValidityChecks.BlakeGCached
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

numeric_data_binding protectedFields20_view : (data.protectedFields.drop 20).take 2 = protectedFields20.protectedFields

numeric_data_binding protectedFields20_piece : protectedFields20.protectedFields = (original.protectedFields.drop 20).take 2

theorem protectedFields20_binding : (data.protectedFields.drop 20).take 2 = (original.protectedFields.drop 20).take 2 :=
  protectedFields20_view.trans protectedFields20_piece

theorem protectedFieldsNode4_8 : (data.protectedFields.drop 4).take 8 = (original.protectedFields.drop 4).take 8 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 4 4 4 8 8 rfl rfl protectedFields4_binding protectedFields8_binding

theorem protectedFieldsNode0_12 : (data.protectedFields.drop 0).take 12 = (original.protectedFields.drop 0).take 12 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 0 4 8 4 12 rfl rfl protectedFields0_binding protectedFieldsNode4_8

theorem protectedFieldsNode16_6 : (data.protectedFields.drop 16).take 6 = (original.protectedFields.drop 16).take 6 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 16 4 2 20 6 rfl rfl protectedFields16_binding protectedFields20_binding

theorem protectedFieldsNode12_10 : (data.protectedFields.drop 12).take 10 = (original.protectedFields.drop 12).take 10 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 12 4 6 16 10 rfl rfl protectedFields12_binding protectedFieldsNode16_6

theorem protectedFieldsNode0_22 : (data.protectedFields.drop 0).take 22 = (original.protectedFields.drop 0).take 22 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 0 12 10 12 22 rfl rfl protectedFieldsNode0_12 protectedFieldsNode12_10

theorem protectedFields_binding : data.protectedFields = original.protectedFields :=
  NumericQueryFrameChecks.complete_binding data.protectedFields original.protectedFields 22
    (by decide +kernel) (by decide +kernel) protectedFieldsNode0_22

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

numeric_data_binding borrows20_view : (data.borrows.drop 20).take 1 = borrows20.borrows

numeric_data_binding borrows20_piece : borrows20.borrows = (original.borrows.drop 20).take 1

theorem borrows20_binding : (data.borrows.drop 20).take 1 = (original.borrows.drop 20).take 1 :=
  borrows20_view.trans borrows20_piece

theorem borrowsNode4_8 : (data.borrows.drop 4).take 8 = (original.borrows.drop 4).take 8 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 4 4 4 8 8 rfl rfl borrows4_binding borrows8_binding

theorem borrowsNode0_12 : (data.borrows.drop 0).take 12 = (original.borrows.drop 0).take 12 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 0 4 8 4 12 rfl rfl borrows0_binding borrowsNode4_8

theorem borrowsNode16_5 : (data.borrows.drop 16).take 5 = (original.borrows.drop 16).take 5 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 16 4 1 20 5 rfl rfl borrows16_binding borrows20_binding

theorem borrowsNode12_9 : (data.borrows.drop 12).take 9 = (original.borrows.drop 12).take 9 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 12 4 5 16 9 rfl rfl borrows12_binding borrowsNode16_5

theorem borrowsNode0_21 : (data.borrows.drop 0).take 21 = (original.borrows.drop 0).take 21 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 0 12 9 12 21 rfl rfl borrowsNode0_12 borrowsNode12_9

theorem borrows_binding : data.borrows = original.borrows :=
  NumericQueryFrameChecks.complete_binding data.borrows original.borrows 21
    (by decide +kernel) (by decide +kernel) borrowsNode0_21

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

numeric_data_binding transports20_view : (data.transports.drop 20).take 1 = transports20.transports

numeric_data_binding transports20_piece : transports20.transports = (original.transports.drop 20).take 1

theorem transports20_binding : (data.transports.drop 20).take 1 = (original.transports.drop 20).take 1 :=
  transports20_view.trans transports20_piece

theorem transportsNode4_8 : (data.transports.drop 4).take 8 = (original.transports.drop 4).take 8 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 4 4 4 8 8 rfl rfl transports4_binding transports8_binding

theorem transportsNode0_12 : (data.transports.drop 0).take 12 = (original.transports.drop 0).take 12 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 0 4 8 4 12 rfl rfl transports0_binding transportsNode4_8

theorem transportsNode16_5 : (data.transports.drop 16).take 5 = (original.transports.drop 16).take 5 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 16 4 1 20 5 rfl rfl transports16_binding transports20_binding

theorem transportsNode12_9 : (data.transports.drop 12).take 9 = (original.transports.drop 12).take 9 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 12 4 5 16 9 rfl rfl transports12_binding transportsNode16_5

theorem transportsNode0_21 : (data.transports.drop 0).take 21 = (original.transports.drop 0).take 21 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 0 12 9 12 21 rfl rfl transportsNode0_12 transportsNode12_9

theorem transports_binding : data.transports = original.transports :=
  NumericQueryFrameChecks.complete_binding data.transports original.transports 21
    (by decide +kernel) (by decide +kernel) transportsNode0_21

theorem source_binding : data = original :=
  NumericHelperValidityChecks.capture_eq data original coordinates_binding borrowBound_binding
    protectedFields_binding borrows_binding transports_binding

end Airbender.Compiler.HelperValidityChecks.BlakeGCached
