module
public import Proven.Compiler.CPUWitnesses.AddSub
public import Proven.Compiler.NativeSatisfiable.AddSub

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.AddSub.Fixture
open NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 32768

/-- The public program retains each instruction address, bits and decoder fields. -/
def program : List Trace.RVMachineProgramEntry :=
  ([Airbender.AddSub.Witness.entry]).map fun entry =>
    ⟨entry.pc, entry.bits, Trace.RVMachineDecoderData.ofOrdinary (fun family => .pooled family) entry.data⟩

/-- Every retained native tuple equals the selected canonical public setup row. -/
theorem lookup_check : canonicalCheck Airbender.AddSub.Witness.initial program Airbender.AddSub.Witness.assignment = true := by
  kernel_rfl

/-- The active honest row supplies a complete cached native CPU certificate. -/
noncomputable def rowCertificate : ProgramLogicalRowCertificate (NativePublicSetup.rows Airbender.AddSub.Witness.initial program) :=
  of_checked Airbender.AddSub.Witness.initial program Airbender.AddSub.Witness.assignment
    NativeSatisfiable.AddSub.source_satisfied lookup_check (by kernel_rfl)

/-- The native certificate retains the supplied CPU family and complete logical assignment. -/
theorem rowCertificate_row : rowCertificate.row =
    (⟨.addSub, Airbender.AddSub.Witness.assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := rfl

end Airbender.Compiler.CPUWitnesses.AddSub.Fixture
