import Airbender.Review.Trace.UnifiedReduced.Paths.ControllerDataflow

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic Reference.RiscV.Sail

/-- A public decoded instruction at one actual occurrence frames a selected
    GPR. Caller cases compare only the static family control-register number;
    native pointer/other-port refreshes are theorem conclusions. -/
inductive PathRegisterCodeFrame [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (cut : Nat) (register : BitVec 5) : Prop where
  | ordinary {instruction : SailRV32.instruction}
      (scope : PathInstructionPreparation data program cut instruction)
      (form : PathRegisterFrame register instruction)
  | caller {family : Delegation.Family}
      (scope : PathCallerPreparation data cut family)
      (different : register ≠ callerControlRegister family)

/-- Public code frames every actual occurrence in a bounded clock interval.
    PCs may branch, jump or repeat. No native value, effect equality, worker
    mask, inert gap or successful execution is supplied. -/
structure PathRegisterGapFrames [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (lower upper : Nat) (register : BitVec 5) : Prop where
  lowerAligned : lower % 4 = 0
  upperAligned : upper % 4 = 0
  ordered : lower ≤ upper
  afterInitial : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ lower
  beforeTerminal : upper ≤ (timeOfPair data.machine.terminal.timestamp).value
  code : ∀ cut, lower + 4 ≤ cut → cut ≤ upper → cut % 4 = 0 →
    PathRegisterCodeFrame data program cut register

end Airbender.UnifiedReduced.Caller
