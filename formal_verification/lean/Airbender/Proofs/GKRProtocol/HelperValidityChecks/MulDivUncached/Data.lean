import Airbender.Proofs.GKRProtocol.HelperValidityChecks.MulDivUncached.Typed
import Airbender.Import.GKRProtocol.NumericHelperValidityImport

namespace Airbender.Compiler.HelperValidityChecks.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_helper_validity_capture metadata := ⟨original.coordinates, original.borrowBound, [], [], []⟩

numeric_helper_validity_capture protectedFields0 := ⟨[], 0, (original.protectedFields.drop 0).take 4, [], []⟩

numeric_helper_validity_capture protectedFields4 := ⟨[], 0, (original.protectedFields.drop 4).take 4, [], []⟩

numeric_helper_validity_capture borrows0 := ⟨[], 0, [], (original.borrows.drop 0).take 4, []⟩

numeric_helper_validity_capture borrows4 := ⟨[], 0, [], (original.borrows.drop 4).take 4, []⟩

numeric_helper_validity_capture transports0 := ⟨[], 0, [], [], (original.transports.drop 0).take 4⟩

numeric_helper_validity_capture transports4 := ⟨[], 0, [], [], (original.transports.drop 4).take 4⟩

noncomputable def data : NumericHelperValidityChecks.Capture :=
  ⟨metadata.coordinates, metadata.borrowBound, (protectedFields0.protectedFields ++ protectedFields4.protectedFields), (borrows0.borrows ++ borrows4.borrows), (transports0.transports ++ transports4.transports)⟩

end Airbender.Compiler.HelperValidityChecks.MulDivUncached
