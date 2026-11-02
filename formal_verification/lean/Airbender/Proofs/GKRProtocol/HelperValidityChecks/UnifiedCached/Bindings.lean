import Airbender.Proofs.GKRProtocol.HelperValidityChecks.UnifiedCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.HelperValidityChecks.UnifiedCached
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

theorem protectedFieldsNode0_8 : (data.protectedFields.drop 0).take 8 = (original.protectedFields.drop 0).take 8 :=
  NumericWorkerPortChecks.merge_at data.protectedFields original.protectedFields 0 4 4 4 8 rfl rfl protectedFields0_binding protectedFields4_binding

theorem protectedFields_binding : data.protectedFields = original.protectedFields :=
  NumericQueryFrameChecks.complete_binding data.protectedFields original.protectedFields 8
    (by decide +kernel) (by decide +kernel) protectedFieldsNode0_8

numeric_data_binding borrows0_view : (data.borrows.drop 0).take 4 = borrows0.borrows

numeric_data_binding borrows0_piece : borrows0.borrows = (original.borrows.drop 0).take 4

theorem borrows0_binding : (data.borrows.drop 0).take 4 = (original.borrows.drop 0).take 4 :=
  borrows0_view.trans borrows0_piece

numeric_data_binding borrows4_view : (data.borrows.drop 4).take 4 = borrows4.borrows

numeric_data_binding borrows4_piece : borrows4.borrows = (original.borrows.drop 4).take 4

theorem borrows4_binding : (data.borrows.drop 4).take 4 = (original.borrows.drop 4).take 4 :=
  borrows4_view.trans borrows4_piece

theorem borrowsNode0_8 : (data.borrows.drop 0).take 8 = (original.borrows.drop 0).take 8 :=
  NumericWorkerPortChecks.merge_at data.borrows original.borrows 0 4 4 4 8 rfl rfl borrows0_binding borrows4_binding

theorem borrows_binding : data.borrows = original.borrows :=
  NumericQueryFrameChecks.complete_binding data.borrows original.borrows 8
    (by decide +kernel) (by decide +kernel) borrowsNode0_8

numeric_data_binding transports0_view : (data.transports.drop 0).take 4 = transports0.transports

numeric_data_binding transports0_piece : transports0.transports = (original.transports.drop 0).take 4

theorem transports0_binding : (data.transports.drop 0).take 4 = (original.transports.drop 0).take 4 :=
  transports0_view.trans transports0_piece

numeric_data_binding transports4_view : (data.transports.drop 4).take 4 = transports4.transports

numeric_data_binding transports4_piece : transports4.transports = (original.transports.drop 4).take 4

theorem transports4_binding : (data.transports.drop 4).take 4 = (original.transports.drop 4).take 4 :=
  transports4_view.trans transports4_piece

theorem transportsNode0_8 : (data.transports.drop 0).take 8 = (original.transports.drop 0).take 8 :=
  NumericWorkerPortChecks.merge_at data.transports original.transports 0 4 4 4 8 rfl rfl transports0_binding transports4_binding

theorem transports_binding : data.transports = original.transports :=
  NumericQueryFrameChecks.complete_binding data.transports original.transports 8
    (by decide +kernel) (by decide +kernel) transportsNode0_8

theorem source_binding : data = original :=
  NumericHelperValidityChecks.capture_eq data original coordinates_binding borrowBound_binding
    protectedFields_binding borrows_binding transports_binding

end Airbender.Compiler.HelperValidityChecks.UnifiedCached
