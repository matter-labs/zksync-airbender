import Airbender.Review.Helpers.Decoder.Instruction

namespace Airbender.Compiler.ProgramProfile
open Airbender.Trace
set_option warningAsError true

/-- A finite instruction-shape check, independent of operand values. -/
def discardedLoad : SailRV32.instruction → Bool
  | .LOAD (_, _, .Regidx 0, false, 4) => true
  | _ => false

theorem no_discarded_loads {Kind : Type} (program : List (ProgramEntry Kind))
    (safe : ∀ entry ∈ program, discardedLoad entry.instruction = false) :
    NoDiscardedLoads program := by
  intro entry member immediate register wrong
  have clean := safe entry member
  rw [wrong] at clean
  simp [discardedLoad] at clean

end Airbender.Compiler.ProgramProfile
