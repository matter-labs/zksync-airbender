import Airbender.Proofs.GKRProtocol.CleanIdealRows
import Tests.CleanIdealTrace

namespace Tests.CleanIdealRows
open Airbender.Compiler
open NumericPolynomialChecks
set_option warningAsError true

def capture : Airbender.Compiler.CleanIdealRows.Capture :=
  ⟨Tests.CleanIdealTrace.ideals, .leaf [Tests.PackedNormalizationTrace.input],
    .leaf [Tests.PackedNormalizationTrace.input]⟩

theorem sources : Airbender.Compiler.CleanIdealRows.Bindings 7 capture := ⟨rfl, rfl⟩
theorem checked : Airbender.Compiler.CleanIdealRows.check 7 capture = true := by decide +kernel
theorem original_check : CleanIdealChecks.check 7 capture.ideals = true :=
  Airbender.Compiler.CleanIdealRows.check_sound 7 capture sources checked

def wrongExpanded : Airbender.Compiler.CleanIdealRows.Capture := {capture with expanded := .leaf [[]]}
def wrongCombination : Airbender.Compiler.CleanIdealRows.Capture := {capture with combinations := .leaf [[]]}

theorem wrong_expanded_rejected : Airbender.Compiler.CleanIdealRows.check 7 wrongExpanded = false := by decide +kernel
theorem wrong_combination_rejected : Airbender.Compiler.CleanIdealRows.check 7 wrongCombination = false := by decide +kernel

end Tests.CleanIdealRows
