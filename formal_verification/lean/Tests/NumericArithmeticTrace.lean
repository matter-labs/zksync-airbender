import Tests.PackedNormalizationTrace
import Airbender.Import.GKRProtocol.NumericTraceDataImport
import Airbender.Proofs.GKRProtocol.ArithmeticNormalizationTrace

namespace Tests.NumericArithmeticTrace
open Airbender.Compiler
open NumericPolynomialChecks
set_option warningAsError true

packed_normalization_rows importedRows from "Tests/fixtures/normalization-traces.json" ["rows"]

theorem bindings_checked : NumericArithmeticTrace.bindingCheck
    [(Tests.PackedNormalizationTrace.expected, Tests.PackedNormalizationTrace.input)] importedRows = true := by decide +kernel

theorem imported_checked : PackedNormalization.check 7 importedRows = true := by decide +kernel

theorem original_normalization_checked :
    [(Tests.PackedNormalizationTrace.expected, Tests.PackedNormalizationTrace.input)].all
      (fun (expected, input) => NumericPolynomialChecks.normalize 7 input == expected) = true :=
  NumericArithmeticTrace.checked_pairs 7 _ _ bindings_checked imported_checked

end Tests.NumericArithmeticTrace
