module
public import Proven.Compiler.CPUWitnesses.Unified
public import Proven.Compiler.NativeSatisfiable.Unified

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.Unified.Fixture
open NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 32768

/-- The public program retains each instruction address, bits and decoder fields. -/
def program : List Trace.RVMachineProgramEntry :=
  (Airbender.NonVacuous.UnifiedBoot.program).map fun entry =>
    ⟨entry.pc, entry.bits, Trace.RVMachineDecoderData.ofOrdinary (fun _ => .unified) entry.data⟩

/-- Every retained native tuple equals the selected canonical public setup row. -/
theorem lookup_check : canonicalCheck Airbender.NonVacuous.UnifiedBoot.initial program Airbender.NonVacuous.UnifiedBoot.assignment = true := by
  kernel_rfl

/-- The active honest row supplies a complete cached native CPU certificate. -/
noncomputable def rowCertificate : UnifiedLogicalRowCertificate (NativePublicSetup.rows Airbender.NonVacuous.UnifiedBoot.initial program) :=
  of_checked Airbender.NonVacuous.UnifiedBoot.initial program Airbender.NonVacuous.UnifiedBoot.assignment
    NativeSatisfiable.Unified.source_satisfied lookup_check (by kernel_rfl)

/-- The native certificate retains the supplied CPU family and complete logical assignment. -/
theorem rowCertificate_row : rowCertificate.row =
    (⟨.machine, Airbender.NonVacuous.UnifiedBoot.assignment⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) := rfl

end Airbender.Compiler.CPUWitnesses.Unified.Fixture
