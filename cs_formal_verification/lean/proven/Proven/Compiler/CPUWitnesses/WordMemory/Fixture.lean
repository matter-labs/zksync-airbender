module
public import Proven.Compiler.CPUWitnesses.WordMemory
public import Proven.Compiler.NativeSatisfiable.WordMemory

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.WordMemory.Fixture
open NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 32768

/-- The public program retains each instruction address, bits and decoder fields. -/
def program : List Trace.RVMachineProgramEntry :=
  ([Airbender.WordMemory.NonVacuous.entry]).map fun entry =>
    ⟨entry.pc, entry.bits, Trace.RVMachineDecoderData.ofOrdinary (fun family => .pooled family) entry.data⟩

/-- Every retained native tuple equals the selected canonical public setup row. -/
theorem lookup_check : canonicalCheck Airbender.WordMemory.NonVacuous.initial program Airbender.WordMemory.NonVacuous.assignment = true := by
  kernel_rfl

/-- The active honest row supplies a complete cached native CPU certificate. -/
noncomputable def rowCertificate : ProgramLogicalRowCertificate (NativePublicSetup.rows Airbender.WordMemory.NonVacuous.initial program) :=
  of_checked Airbender.WordMemory.NonVacuous.initial program Airbender.WordMemory.NonVacuous.assignment
    NativeSatisfiable.WordMemory.source_satisfied lookup_check (by kernel_rfl)

/-- The native certificate retains the supplied CPU family and complete logical assignment. -/
theorem rowCertificate_row : rowCertificate.row =
    (⟨.wordMemory, Airbender.WordMemory.NonVacuous.assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := rfl

end Airbender.Compiler.CPUWitnesses.WordMemory.Fixture
