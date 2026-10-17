import Airbender.Review.Helpers.Memory.NativeProgramData
import Airbender.Review.Helpers.Memory.ProgramData.AddSub
import Airbender.Review.Helpers.Memory.ProgramData.JumpBranch
import Airbender.Review.Helpers.Memory.ProgramData.MulDiv
import Airbender.Review.Helpers.Memory.ProgramData.ShiftBinop
import Airbender.Review.Helpers.Memory.ProgramData.Subword
import Airbender.Review.Helpers.Memory.ProgramData.Unified
import Mathlib.Tactic.FinCases

namespace Airbender.Trace.ROM.Proofs
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

def selectedProgram (kind : Fin 6) : Program :=
  #v[addSubProgramData, jumpBranchProgramData, mulDivProgramData,
    shiftProgramData, subwordProgramData, unifiedProgramData][kind]

/-- All independently exported circuit families carry the same complete selected inputs. -/
theorem selected_program_agreement (kind : Fin 6) :
    selectedProgram kind = nativeProgramData := by
  fin_cases kind <;> rfl

end Airbender.Trace.ROM.Proofs
