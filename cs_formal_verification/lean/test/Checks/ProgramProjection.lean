module
public import Human.Helpers.Decoder.RVMachineProgram
public import Mathlib.Tactic.IntervalCases

open Airbender Airbender.Trace

-- The native program projection preserves each ordinary model's complete nine-column query.
example {Kind : Type} (family : Kind → RVMachineDecoderFamily) (entry : RVProgramEntry Kind) :
    ((RVMachineDecoderData.ofOrdinary (family := family) entry.data).row entry.pc).map
      (fun (value : Nat) => (value : ZMod babyBearModulus)) = entry.query := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [RVMachineDecoderData.ofOrdinary, RVMachineDecoderData.row,
      RVProgramEntry.query, Arithmetic.Word.ofBitVec, Arithmetic.limbBase]
