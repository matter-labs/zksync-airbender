import Airbender.Proofs.GKRProtocol.HelperValidityChecks.BlakeRoundCached.Typed
import Airbender.Import.GKRProtocol.NumericHelperValidityImport

namespace Airbender.Compiler.HelperValidityChecks.BlakeRoundCached
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

numeric_helper_validity_capture protectedFields40 := ⟨[], 0, (original.protectedFields.drop 40).take 4, [], []⟩

numeric_helper_validity_capture protectedFields44 := ⟨[], 0, (original.protectedFields.drop 44).take 4, [], []⟩

numeric_helper_validity_capture protectedFields48 := ⟨[], 0, (original.protectedFields.drop 48).take 4, [], []⟩

numeric_helper_validity_capture protectedFields52 := ⟨[], 0, (original.protectedFields.drop 52).take 4, [], []⟩

numeric_helper_validity_capture protectedFields56 := ⟨[], 0, (original.protectedFields.drop 56).take 4, [], []⟩

numeric_helper_validity_capture protectedFields60 := ⟨[], 0, (original.protectedFields.drop 60).take 4, [], []⟩

numeric_helper_validity_capture protectedFields64 := ⟨[], 0, (original.protectedFields.drop 64).take 4, [], []⟩

numeric_helper_validity_capture protectedFields68 := ⟨[], 0, (original.protectedFields.drop 68).take 4, [], []⟩

numeric_helper_validity_capture protectedFields72 := ⟨[], 0, (original.protectedFields.drop 72).take 4, [], []⟩

numeric_helper_validity_capture protectedFields76 := ⟨[], 0, (original.protectedFields.drop 76).take 4, [], []⟩

numeric_helper_validity_capture protectedFields80 := ⟨[], 0, (original.protectedFields.drop 80).take 4, [], []⟩

numeric_helper_validity_capture protectedFields84 := ⟨[], 0, (original.protectedFields.drop 84).take 4, [], []⟩

numeric_helper_validity_capture protectedFields88 := ⟨[], 0, (original.protectedFields.drop 88).take 2, [], []⟩

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

numeric_helper_validity_capture borrows40 := ⟨[], 0, [], (original.borrows.drop 40).take 4, []⟩

numeric_helper_validity_capture borrows44 := ⟨[], 0, [], (original.borrows.drop 44).take 4, []⟩

numeric_helper_validity_capture borrows48 := ⟨[], 0, [], (original.borrows.drop 48).take 4, []⟩

numeric_helper_validity_capture borrows52 := ⟨[], 0, [], (original.borrows.drop 52).take 4, []⟩

numeric_helper_validity_capture borrows56 := ⟨[], 0, [], (original.borrows.drop 56).take 4, []⟩

numeric_helper_validity_capture borrows60 := ⟨[], 0, [], (original.borrows.drop 60).take 4, []⟩

numeric_helper_validity_capture borrows64 := ⟨[], 0, [], (original.borrows.drop 64).take 4, []⟩

numeric_helper_validity_capture borrows68 := ⟨[], 0, [], (original.borrows.drop 68).take 4, []⟩

numeric_helper_validity_capture borrows72 := ⟨[], 0, [], (original.borrows.drop 72).take 4, []⟩

numeric_helper_validity_capture borrows76 := ⟨[], 0, [], (original.borrows.drop 76).take 4, []⟩

numeric_helper_validity_capture borrows80 := ⟨[], 0, [], (original.borrows.drop 80).take 4, []⟩

numeric_helper_validity_capture borrows84 := ⟨[], 0, [], (original.borrows.drop 84).take 4, []⟩

numeric_helper_validity_capture borrows88 := ⟨[], 0, [], (original.borrows.drop 88).take 1, []⟩

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

numeric_helper_validity_capture transports40 := ⟨[], 0, [], [], (original.transports.drop 40).take 4⟩

numeric_helper_validity_capture transports44 := ⟨[], 0, [], [], (original.transports.drop 44).take 4⟩

numeric_helper_validity_capture transports48 := ⟨[], 0, [], [], (original.transports.drop 48).take 4⟩

numeric_helper_validity_capture transports52 := ⟨[], 0, [], [], (original.transports.drop 52).take 4⟩

numeric_helper_validity_capture transports56 := ⟨[], 0, [], [], (original.transports.drop 56).take 4⟩

numeric_helper_validity_capture transports60 := ⟨[], 0, [], [], (original.transports.drop 60).take 4⟩

numeric_helper_validity_capture transports64 := ⟨[], 0, [], [], (original.transports.drop 64).take 4⟩

numeric_helper_validity_capture transports68 := ⟨[], 0, [], [], (original.transports.drop 68).take 4⟩

numeric_helper_validity_capture transports72 := ⟨[], 0, [], [], (original.transports.drop 72).take 4⟩

numeric_helper_validity_capture transports76 := ⟨[], 0, [], [], (original.transports.drop 76).take 4⟩

numeric_helper_validity_capture transports80 := ⟨[], 0, [], [], (original.transports.drop 80).take 4⟩

numeric_helper_validity_capture transports84 := ⟨[], 0, [], [], (original.transports.drop 84).take 4⟩

numeric_helper_validity_capture transports88 := ⟨[], 0, [], [], (original.transports.drop 88).take 1⟩

noncomputable def data : NumericHelperValidityChecks.Capture :=
  ⟨metadata.coordinates, metadata.borrowBound, ((((protectedFields0.protectedFields ++ protectedFields4.protectedFields) ++ (protectedFields8.protectedFields ++ (protectedFields12.protectedFields ++ protectedFields16.protectedFields))) ++ ((protectedFields20.protectedFields ++ (protectedFields24.protectedFields ++ protectedFields28.protectedFields)) ++ (protectedFields32.protectedFields ++ (protectedFields36.protectedFields ++ protectedFields40.protectedFields)))) ++ (((protectedFields44.protectedFields ++ (protectedFields48.protectedFields ++ protectedFields52.protectedFields)) ++ (protectedFields56.protectedFields ++ (protectedFields60.protectedFields ++ protectedFields64.protectedFields))) ++ ((protectedFields68.protectedFields ++ (protectedFields72.protectedFields ++ protectedFields76.protectedFields)) ++ (protectedFields80.protectedFields ++ (protectedFields84.protectedFields ++ protectedFields88.protectedFields))))), ((((borrows0.borrows ++ borrows4.borrows) ++ (borrows8.borrows ++ (borrows12.borrows ++ borrows16.borrows))) ++ ((borrows20.borrows ++ (borrows24.borrows ++ borrows28.borrows)) ++ (borrows32.borrows ++ (borrows36.borrows ++ borrows40.borrows)))) ++ (((borrows44.borrows ++ (borrows48.borrows ++ borrows52.borrows)) ++ (borrows56.borrows ++ (borrows60.borrows ++ borrows64.borrows))) ++ ((borrows68.borrows ++ (borrows72.borrows ++ borrows76.borrows)) ++ (borrows80.borrows ++ (borrows84.borrows ++ borrows88.borrows))))), ((((transports0.transports ++ transports4.transports) ++ (transports8.transports ++ (transports12.transports ++ transports16.transports))) ++ ((transports20.transports ++ (transports24.transports ++ transports28.transports)) ++ (transports32.transports ++ (transports36.transports ++ transports40.transports)))) ++ (((transports44.transports ++ (transports48.transports ++ transports52.transports)) ++ (transports56.transports ++ (transports60.transports ++ transports64.transports))) ++ ((transports68.transports ++ (transports72.transports ++ transports76.transports)) ++ (transports80.transports ++ (transports84.transports ++ transports88.transports)))))⟩

end Airbender.Compiler.HelperValidityChecks.BlakeRoundCached
