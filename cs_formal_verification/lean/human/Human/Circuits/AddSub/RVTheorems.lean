module
public import Human.Circuits.AddSub.RVModel
public import Human.Helpers.Core.BabyBearPrime
public import Human.Helpers.Context.RVRowModel

@[expose] public section

/-! RV32 claims (B2 pilot). The AddSub claims (first block) are stated against our spec (`RV.step`, `Human/ISA/RV32.lean`),
    not Sail: the row's pre-state is `input.before : RV.State`, which carries the input stream (`RV.State.input`), so there is
    no stream binder. `RV.Same` (`ISA/State.lean`) compares two `RV.State`s. Proven in
    `slop/Slop/Final/Circuits/AddSub/RVTheorems.lean` (checked in `test/Checks/Claims.lean`).
    Resolved: PC in ROM and 4-byte aligned is the decoder table's guard (`rvProgramEntryWith`); the word at the row's PC is
    the table's encoding (`Trace.RVRowMapping.instruction`).
    The delegation caller rows' RV claims are in `RVCallerTheorems.lean`. -/

namespace Airbender.AddSub
open Reference.RiscV Trace

/-- Every accepted ADD/ADDI/SUB/LUI/AUIPC row is one step of our spec: from the row's pre-state (`input.before`), the
    step exists and gives the row's post-state: `rd` := the row's result (x0: discarded), PC := the row's final PC,
    nothing else changed. Its assumptions can be met: some accepted, decoded trace meeting `RVInterfaceAssumptions`
    has such a row (`Trace.RVRowClaim`). -/
def RVSoundnessClaim : Prop :=
  Trace.RVRowClaim .addSub RVInput.before rvInstruction RVWordMapping RVInterfaceAssumptions fun input output =>
    ∃ s', RV.step input.before = some s' ∧
      RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

end Airbender.AddSub
