module
public import Proven.Trace.Machine.Fetch
public import Proven.ISA.RV.Input
public import Proven.ISA.RV.Same

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Observable agreement survives replacement of both states' remaining input streams. -/
theorem same_with_input {first last : RV.State} (same : RV.Same first last) (stream : List RV.Word) :
    RV.Same (first.withInput stream) (last.withInput stream) :=
  ⟨same.1, same.2.1, same.2.2.1, same.2.2.2.1, rfl⟩

/-- The public machine entry fixes the instruction fetched at its PC in every ROM-preserving cut. -/
theorem fetch_decoded {config : RVMachineConfig} {initial state : RV.State}
    {addresses : List (BitVec 32)} {program : List RVMachineProgramEntry} {entry : RVMachineProgramEntry} {instruction : RV.Instr}
    (image : rvMachineProgramImage config initial addresses = some program) (present : entry ∈ program)
    (decoded : RV.decode entry.bits = some instruction) (rom : state.rom = initial.rom) (pc : state.pc = entry.pc) :
    RV.step state = RV.exec state instruction := by
  obtain ⟨fetched, source, _, same⟩ := machine_current_fetch image present rom pc
  have equal : fetched = instruction := Option.some.inj (source.symm.trans decoded)
  subst fetched
  exact same

/-- Every non-read native cycle executes with the independent stream left by earlier reads. -/
theorem cycle_step_with_input {config : RVMachineConfig} {initial before after : RV.State}
    {addresses : List (BitVec 32)} {program : List RVMachineProgramEntry} {entry : RVMachineProgramEntry} {instruction : RV.Instr}
    (image : rvMachineProgramImage config initial addresses = some program) (present : entry ∈ program)
    (decoded : RV.decode entry.bits = some instruction) (rom : before.rom = initial.rom)
    (noRead : instruction.readsInput = false) (pc : RV.Word)
    (step : ∃ next, RV.step (before.setPC entry.pc) = some next ∧ RV.Same next (after.setPC pc))
    (stream : List RV.Word) :
    ∃ next, RV.step ((before.setPC entry.pc).withInput stream) = some next ∧
      RV.Same next ((after.setPC pc).withInput stream) := by
  have original := fetch_decoded image present decoded rom (state := before.setPC entry.pc) rfl
  have current := fetch_decoded image present decoded rom (state := (before.setPC entry.pc).withInput stream) rfl
  obtain ⟨next, stepped, same⟩ := step
  rw [original] at stepped
  refine ⟨next.withInput stream, ?_, same_with_input same stream⟩
  rw [current, RV.exec_input_irrel _ instruction noRead stream, stepped]
  rfl

end Airbender.Trace.Machine.Proofs
