import Airbender.Import.GKRProtocol.NumericExpressionDataImport

namespace Tests.NumericExpressionChecks
open Airbender.Compiler
set_option warningAsError true

numeric_expressions importedCodes from "Tests/fixtures/numeric-expressions.json" ["expressions"]
def original : Expression 2 (ZMod 7) :=
  .mul (.add (.atom 0) (.constant (-1))) (.add (.atom 1) (.constant 1))
numeric_data_binding expressions_bound : [Airbender.Compiler.NumericExpressionChecks.encode original] = importedCodes

theorem expanded_terms : importedCodes.map (Airbender.Compiler.NumericExpressionChecks.Code.polynomial 7) =
    [[(1, [0, 1]), (1, [0]), (6, [1]), (6, [])]] := by decide +kernel

theorem original_terms : NumericPolynomialChecks.encode original.polynomial =
    Airbender.Compiler.NumericExpressionChecks.Code.polynomial 7
      (Airbender.Compiler.NumericExpressionChecks.encode original) :=
  Airbender.Compiler.NumericExpressionChecks.encode_polynomial original

theorem zero_terms_retained :
    Airbender.Compiler.NumericExpressionChecks.Code.polynomial 7
      (.mul (.constant 0) (.add (.atom 0) (.atom 1))) = [(0, [0]), (0, [1])] := by decide +kernel

theorem variable_order_retained :
    Airbender.Compiler.NumericExpressionChecks.Code.polynomial 7
      (.mul (.atom 1) (.atom 0)) = [(1, [1, 0])] := by decide +kernel

end Tests.NumericExpressionChecks
