import Human.Helpers.UnifiedReduced.RVExecutionInputs

-- The statement proven in slop/Slop/Final/Trace/UnifiedReduced/RVTheorems.lean (checked by verify.sh).

namespace Airbender.UnifiedReduced

/-- Every admitted unified row (standard instructions, TRIADD and XORROT), in its history-derived order, is one
    `RV.step` of our RV32 spec from the public starting state `initial`; the final PC and every tracked cell (registers
    and RAM, shadow RAM included) match the trace's terminal tokens. `RVExecutionInputs` lists only public
    boot/profile conditions; row reads, bounds and results are derived. -/
def RVExecutionSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (byteInverse : 256 * (-7864320 : ZMod p) = 1) {trace : Trace.UnifiedTrace p} {initial : RV.State} {cells : List Trace.Cell} {program : List RVProgramEntry} (inputs : RVExecutionInputs trace initial cells program) (accepted : Trace.Accepted trace) (decoded : RVDecoded trace program),
    Trace.RVRealizes trace initial cells

end Airbender.UnifiedReduced
