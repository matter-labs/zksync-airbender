module
public import Proven.Compiler.CPUWitnesses.JumpBranch
public import Proven.Compiler.NativeSatisfiable.JumpBranch

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.JumpBranch.Fixture
open NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 32768

/-- The public program retains each instruction address, bits and decoder fields. -/
def program : List Trace.RVMachineProgramEntry :=
  ([Airbender.JumpBranchSlt.Comparison.NonVacuous.entry]).map fun entry =>
    ⟨entry.pc, entry.bits, Trace.RVMachineDecoderData.ofOrdinary (fun family => .pooled family) entry.data⟩

/-- Every retained native tuple equals the selected canonical public setup row. -/
theorem lookup_check : canonicalCheck Airbender.JumpBranchSlt.Comparison.NonVacuous.initial program Airbender.JumpBranchSlt.Comparison.NonVacuous.assignment = true := by
  kernel_rfl

/-- The active honest row supplies a complete cached native CPU certificate. -/
noncomputable def rowCertificate : ProgramLogicalRowCertificate (NativePublicSetup.rows Airbender.JumpBranchSlt.Comparison.NonVacuous.initial program) :=
  of_checked Airbender.JumpBranchSlt.Comparison.NonVacuous.initial program Airbender.JumpBranchSlt.Comparison.NonVacuous.assignment
    NativeSatisfiable.JumpBranch.source_satisfied lookup_check (by kernel_rfl)

/-- The native certificate retains the supplied CPU family and complete logical assignment. -/
theorem rowCertificate_row : rowCertificate.row =
    (⟨.jumpBranchSlt, Airbender.JumpBranchSlt.Comparison.NonVacuous.assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := rfl

end Airbender.Compiler.CPUWitnesses.JumpBranch.Fixture
