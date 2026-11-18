module
public import Proven.Compiler.CPUWitnesses.ShiftBinop
public import Proven.Compiler.NativeSatisfiable.ShiftBinop

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.ShiftBinop.Fixture
open NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 32768

/-- The public program retains each instruction address, bits and decoder fields. -/
def program : List Trace.RVMachineProgramEntry :=
  (Airbender.NonVacuous.ShiftBinopTrace.program).map fun entry =>
    ⟨entry.pc, entry.bits, Trace.RVMachineDecoderData.ofOrdinary (fun _ => .pooled .shiftBinop) entry.data⟩

/-- Every retained native tuple equals the selected canonical public setup row. -/
theorem lookup_check : canonicalCheck Airbender.NonVacuous.ShiftBinopTrace.initial program Airbender.NonVacuous.ShiftBinopTrace.assignment = true := by
  kernel_rfl

/-- The active honest row supplies a complete cached native CPU certificate. -/
noncomputable def rowCertificate : ProgramLogicalRowCertificate (NativePublicSetup.rows Airbender.NonVacuous.ShiftBinopTrace.initial program) :=
  of_checked Airbender.NonVacuous.ShiftBinopTrace.initial program Airbender.NonVacuous.ShiftBinopTrace.assignment
    NativeSatisfiable.ShiftBinop.source_satisfied lookup_check (by kernel_rfl)

/-- The native certificate retains the supplied CPU family and complete logical assignment. -/
theorem rowCertificate_row : rowCertificate.row =
    (⟨.shiftBinop, Airbender.NonVacuous.ShiftBinopTrace.assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := rfl

end Airbender.Compiler.CPUWitnesses.ShiftBinop.Fixture
