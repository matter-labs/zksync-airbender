import Airbender.Proofs.GKRProtocol.CleanIdealTrace
import Tests.PackedNormalizationTrace

namespace Tests.CleanIdealTrace
open Airbender.Compiler
open NumericPolynomialChecks
set_option warningAsError true

def ideals : CleanIdealChecks.Capture := ⟨
  .leaf [.add (.add (.mul (.constant 3) (.mul (.atom 1) (.atom 0)))
    (.mul (.constant 5) (.mul (.atom 0) (.atom 1)))) (.add (.constant 6) (.atom 2))],
  .leaf [Tests.PackedNormalizationTrace.input], .leaf [[([(1, [])], 0)]],
  .leaf [[1, 0, 0, 1, 2]], 3⟩

def capture : Airbender.Compiler.CleanIdealTrace.Capture := ⟨ideals,
  .leaf [Tests.PackedNormalizationTrace.expected],
  .leaf [Tests.PackedNormalizationTrace.input], .leaf [Tests.PackedNormalizationTrace.input],
  [Tests.PackedNormalizationTrace.row, Tests.PackedNormalizationTrace.row]⟩

theorem sources : Airbender.Compiler.CleanIdealTrace.Bindings 7 capture := ⟨rfl, rfl⟩
theorem bindings : Airbender.Compiler.CleanIdealTrace.bindingCheck 7 capture = true := by decide +kernel
theorem checked : Airbender.Compiler.CleanIdealTrace.check 7 capture = true := by decide +kernel
theorem original_check : CleanIdealChecks.check 7 ideals = true :=
  Airbender.Compiler.CleanIdealTrace.check_sound 7 capture sources bindings checked

def missingRows : Airbender.Compiler.CleanIdealTrace.Capture := {capture with rows := []}
def missingNormal : Airbender.Compiler.CleanIdealTrace.Capture := {capture with normalized := .leaf []}
def wrongNormal : Airbender.Compiler.CleanIdealTrace.Capture := {capture with normalized := .leaf [[]]}
def wrongTrace : Airbender.Compiler.CleanIdealTrace.Capture :=
  {capture with rows := [Tests.PackedNormalizationTrace.wrongPosition, Tests.PackedNormalizationTrace.row]}

theorem missing_rows_rejected : Airbender.Compiler.CleanIdealTrace.bindingCheck 7 missingRows = false := by decide +kernel
theorem missing_normal_rejected : Airbender.Compiler.CleanIdealTrace.check 7 missingNormal = false := by decide +kernel
theorem wrong_normal_rejected : Airbender.Compiler.CleanIdealTrace.bindingCheck 7 wrongNormal = false := by decide +kernel
theorem wrong_trace_rejected : Airbender.Compiler.CleanIdealTrace.check 7 wrongTrace = false := by decide +kernel

end Tests.CleanIdealTrace
