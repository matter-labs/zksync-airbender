import Airbender.Data.Compiler.NativeProgramSetup
import Airbender.Proofs.GKRProtocol.ProgramSetupRows

namespace Airbender.Compiler.NativeProgramSetup
open Airbender.Reference.Compiler
set_option warningAsError true
set_option Elab.async false

theorem geometry_valid (configuration : Configuration) : ValidGeometry configuration := by
  cases configuration <;> simp only [ValidGeometry, layouts] <;> decide +kernel

theorem rows_fixed_group (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (configuration : Configuration) (group : Fin 3)
    (index : Nat) (other : group.val ≠ 0) :
    rows decoder wordAt configuration group index = retainedRows configuration group index := by
  cases selected : layouts configuration with
  | none => simp [rows, selected]
  | some layout =>
    simpa [rows, selected] using
      ProgramSetup.fixed_group layout (retainedRows configuration) (decoder configuration)
        wordAt group index other

end Airbender.Compiler.NativeProgramSetup
