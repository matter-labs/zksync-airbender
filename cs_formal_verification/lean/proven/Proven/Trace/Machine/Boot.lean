module
public import Human.Trace.Machine.Model
public import Proven.Trace.RVBootSeed
public import Proven.Trace.ROMView
public import Proven.VerifierBoundary

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
variable {Kind : Type} [CircuitLayout Kind]

/-- The complete list of checked initialization instances gives the existing zero boot image. -/
theorem boot_seed {trace : Data babyBearModulus Kind} {initial : RV.State} {cells : List Cell}
    {program : List RVMachineProgramEntry} {config : RVMachineConfig} {layout : InitsTeardowns.Layout}
    {inits : List (InitsTeardowns.Witness babyBearModulus layout)}
    (properties : InitsTeardowns.Claims layout)
    (inputs : BootInputs config trace initial cells program layout inits) :
    trace.initialMemory = ROMView.nativeBootImage cells :=
  Trace.Proofs.boot_seed_image properties inputs.topBits inputs.seeds inputs.domain

/-- Native clock inputs follow from the public boot tuple and all initialization instances. -/
theorem boot_clocks {trace : Data babyBearModulus Kind} {initial : RV.State} {cells : List Cell}
    {program : List RVMachineProgramEntry} {config : RVMachineConfig} {layout : InitsTeardowns.Layout}
    {inits : List (InitsTeardowns.Witness babyBearModulus layout)}
    (properties : InitsTeardowns.Claims layout)
    (inputs : BootInputs config trace initial cells program layout inits) : ClockBoundary trace :=
  ROMView.native_clocks (by decide) (boot_seed properties inputs) inputs.initialBoundary

/-- Typed verifier closure supplies the terminal PC bounds of every machine target. -/
theorem boot_terminal_bound {trace : Data babyBearModulus Kind} {initial : RV.State} {cells : List Cell}
    {program : List RVMachineProgramEntry} {config : RVMachineConfig} {layout : InitsTeardowns.Layout}
    {inits : List (InitsTeardowns.Witness babyBearModulus layout)}
    (inputs : BootInputs config trace initial cells program layout inits)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start)) : trace.terminal.word.Bounded := by
  obtain ⟨terminal, binding⟩ := inputs.stateClosure
  exact VerifierBoundary.Proofs.terminal_bound (by decide) states ⟨_, binding⟩

/-- The public RV PC is the initial native PC. -/
theorem boot_start {trace : Data babyBearModulus Kind} {initial : RV.State} {cells : List Cell}
    {program : List RVMachineProgramEntry} {config : RVMachineConfig} {layout : InitsTeardowns.Layout}
    {inits : List (InitsTeardowns.Witness babyBearModulus layout)}
    (inputs : BootInputs config trace initial cells program layout inits) :
    initial.pc = trace.initial.word.toBitVec := by
  rw [inputs.initialBoundary, inputs.pc]
  simp [PCState.boundary, PCState.encode, PCState.State.word, Arithmetic.Word.toBitVec, Arithmetic.Word.value]

end Airbender.Trace.Machine.Proofs
