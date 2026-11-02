import Airbender.Proofs.GKRProtocol.HelperValidityChecks.BigintCached.Typed
import Airbender.Import.GKRProtocol.NumericHelperValidityImport

namespace Airbender.Compiler.HelperValidityChecks.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_helper_validity_capture metadata := ⟨original.coordinates, original.borrowBound, [], [], []⟩

numeric_helper_validity_capture protectedFields0 := ⟨[], 0, (original.protectedFields.drop 0).take 4, [], []⟩

numeric_helper_validity_capture protectedFields4 := ⟨[], 0, (original.protectedFields.drop 4).take 4, [], []⟩

numeric_helper_validity_capture protectedFields8 := ⟨[], 0, (original.protectedFields.drop 8).take 4, [], []⟩

numeric_helper_validity_capture protectedFields12 := ⟨[], 0, (original.protectedFields.drop 12).take 4, [], []⟩

numeric_helper_validity_capture protectedFields16 := ⟨[], 0, (original.protectedFields.drop 16).take 4, [], []⟩

numeric_helper_validity_capture protectedFields20 := ⟨[], 0, (original.protectedFields.drop 20).take 4, [], []⟩

numeric_helper_validity_capture protectedFields24 := ⟨[], 0, (original.protectedFields.drop 24).take 4, [], []⟩

numeric_helper_validity_capture protectedFields28 := ⟨[], 0, (original.protectedFields.drop 28).take 4, [], []⟩

numeric_helper_validity_capture protectedFields32 := ⟨[], 0, (original.protectedFields.drop 32).take 4, [], []⟩

numeric_helper_validity_capture protectedFields36 := ⟨[], 0, (original.protectedFields.drop 36).take 4, [], []⟩

numeric_helper_validity_capture protectedFields40 := ⟨[], 0, (original.protectedFields.drop 40).take 2, [], []⟩

numeric_helper_validity_capture borrows0 := ⟨[], 0, [], (original.borrows.drop 0).take 4, []⟩

numeric_helper_validity_capture borrows4 := ⟨[], 0, [], (original.borrows.drop 4).take 4, []⟩

numeric_helper_validity_capture borrows8 := ⟨[], 0, [], (original.borrows.drop 8).take 4, []⟩

numeric_helper_validity_capture borrows12 := ⟨[], 0, [], (original.borrows.drop 12).take 4, []⟩

numeric_helper_validity_capture borrows16 := ⟨[], 0, [], (original.borrows.drop 16).take 4, []⟩

numeric_helper_validity_capture borrows20 := ⟨[], 0, [], (original.borrows.drop 20).take 4, []⟩

numeric_helper_validity_capture borrows24 := ⟨[], 0, [], (original.borrows.drop 24).take 4, []⟩

numeric_helper_validity_capture borrows28 := ⟨[], 0, [], (original.borrows.drop 28).take 4, []⟩

numeric_helper_validity_capture borrows32 := ⟨[], 0, [], (original.borrows.drop 32).take 4, []⟩

numeric_helper_validity_capture borrows36 := ⟨[], 0, [], (original.borrows.drop 36).take 4, []⟩

numeric_helper_validity_capture borrows40 := ⟨[], 0, [], (original.borrows.drop 40).take 1, []⟩

numeric_helper_validity_capture transports0 := ⟨[], 0, [], [], (original.transports.drop 0).take 4⟩

numeric_helper_validity_capture transports4 := ⟨[], 0, [], [], (original.transports.drop 4).take 4⟩

numeric_helper_validity_capture transports8 := ⟨[], 0, [], [], (original.transports.drop 8).take 4⟩

numeric_helper_validity_capture transports12 := ⟨[], 0, [], [], (original.transports.drop 12).take 4⟩

numeric_helper_validity_capture transports16 := ⟨[], 0, [], [], (original.transports.drop 16).take 4⟩

numeric_helper_validity_capture transports20 := ⟨[], 0, [], [], (original.transports.drop 20).take 4⟩

numeric_helper_validity_capture transports24 := ⟨[], 0, [], [], (original.transports.drop 24).take 4⟩

numeric_helper_validity_capture transports28 := ⟨[], 0, [], [], (original.transports.drop 28).take 4⟩

numeric_helper_validity_capture transports32 := ⟨[], 0, [], [], (original.transports.drop 32).take 4⟩

numeric_helper_validity_capture transports36 := ⟨[], 0, [], [], (original.transports.drop 36).take 4⟩

numeric_helper_validity_capture transports40 := ⟨[], 0, [], [], (original.transports.drop 40).take 1⟩

noncomputable def data : NumericHelperValidityChecks.Capture :=
  ⟨metadata.coordinates, metadata.borrowBound, (((protectedFields0.protectedFields ++ protectedFields4.protectedFields) ++ (protectedFields8.protectedFields ++ (protectedFields12.protectedFields ++ protectedFields16.protectedFields))) ++ ((protectedFields20.protectedFields ++ (protectedFields24.protectedFields ++ protectedFields28.protectedFields)) ++ (protectedFields32.protectedFields ++ (protectedFields36.protectedFields ++ protectedFields40.protectedFields)))), (((borrows0.borrows ++ borrows4.borrows) ++ (borrows8.borrows ++ (borrows12.borrows ++ borrows16.borrows))) ++ ((borrows20.borrows ++ (borrows24.borrows ++ borrows28.borrows)) ++ (borrows32.borrows ++ (borrows36.borrows ++ borrows40.borrows)))), (((transports0.transports ++ transports4.transports) ++ (transports8.transports ++ (transports12.transports ++ transports16.transports))) ++ ((transports20.transports ++ (transports24.transports ++ transports28.transports)) ++ (transports32.transports ++ (transports36.transports ++ transports40.transports))))⟩

end Airbender.Compiler.HelperValidityChecks.BigintCached
