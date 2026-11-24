module
public import Proven.Compiler.CPUWitnesses.AddSub.Fixture
public import Proven.Compiler.CPUWitnesses.JumpBranch.Fixture
public import Proven.Compiler.CPUWitnesses.MulDiv.Fixture
public import Proven.Compiler.CPUWitnesses.ShiftBinop.Fixture
public import Proven.Compiler.CPUWitnesses.WordMemory.Fixture
public import Proven.Compiler.CPUWitnesses.SubwordMemory.Fixture
public import Proven.Compiler.CPUWitnesses.Unified.Fixture

@[expose] public section
namespace Airbender.Compiler
open NativeArithmetic
set_option warningAsError true

/-- The add sub CPU family has a full active native certificate with public lookup matching. -/
theorem cached_add_sub_certificate_satisfiable :
    ∃ entry : ProgramLogicalRowCertificate (NativePublicSetup.rows Airbender.AddSub.Witness.initial CPUWitnesses.AddSub.Fixture.program),
      entry.row = (⟨.addSub, Airbender.AddSub.Witness.assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) :=
  ⟨CPUWitnesses.AddSub.Fixture.rowCertificate, CPUWitnesses.AddSub.Fixture.rowCertificate_row⟩

/-- The jump branch CPU family has a full active native certificate with public lookup matching. -/
theorem cached_jump_branch_certificate_satisfiable :
    ∃ entry : ProgramLogicalRowCertificate (NativePublicSetup.rows Airbender.JumpBranchSlt.Comparison.NonVacuous.initial CPUWitnesses.JumpBranch.Fixture.program),
      entry.row = (⟨.jumpBranchSlt, Airbender.JumpBranchSlt.Comparison.NonVacuous.assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) :=
  ⟨CPUWitnesses.JumpBranch.Fixture.rowCertificate, CPUWitnesses.JumpBranch.Fixture.rowCertificate_row⟩

/-- The mul div CPU family has a full active native certificate with public lookup matching. -/
theorem cached_mul_div_certificate_satisfiable :
    ∃ entry : ProgramLogicalRowCertificate (NativePublicSetup.rows Airbender.NonVacuous.MulDivTrace.initial CPUWitnesses.MulDiv.Fixture.program),
      entry.row = (⟨.mulDiv, Airbender.NonVacuous.MulDivTrace.assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) :=
  ⟨CPUWitnesses.MulDiv.Fixture.rowCertificate, CPUWitnesses.MulDiv.Fixture.rowCertificate_row⟩

/-- The shift binop CPU family has a full active native certificate with public lookup matching. -/
theorem cached_shift_binop_certificate_satisfiable :
    ∃ entry : ProgramLogicalRowCertificate (NativePublicSetup.rows Airbender.NonVacuous.ShiftBinopTrace.initial CPUWitnesses.ShiftBinop.Fixture.program),
      entry.row = (⟨.shiftBinop, Airbender.NonVacuous.ShiftBinopTrace.assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) :=
  ⟨CPUWitnesses.ShiftBinop.Fixture.rowCertificate, CPUWitnesses.ShiftBinop.Fixture.rowCertificate_row⟩

/-- The word memory CPU family has a full active native certificate with public lookup matching. -/
theorem cached_word_memory_certificate_satisfiable :
    ∃ entry : ProgramLogicalRowCertificate (NativePublicSetup.rows Airbender.WordMemory.NonVacuous.initial CPUWitnesses.WordMemory.Fixture.program),
      entry.row = (⟨.wordMemory, Airbender.WordMemory.NonVacuous.assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) :=
  ⟨CPUWitnesses.WordMemory.Fixture.rowCertificate, CPUWitnesses.WordMemory.Fixture.rowCertificate_row⟩

/-- The subword memory CPU family has a full active native certificate with public lookup matching. -/
theorem cached_subword_memory_certificate_satisfiable :
    ∃ entry : ProgramLogicalRowCertificate (NativePublicSetup.rows Airbender.NonVacuous.SubwordMemoryTrace.initial CPUWitnesses.SubwordMemory.Fixture.program),
      entry.row = (⟨.subwordMemory, Airbender.NonVacuous.SubwordMemoryTrace.assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) :=
  ⟨CPUWitnesses.SubwordMemory.Fixture.rowCertificate, CPUWitnesses.SubwordMemory.Fixture.rowCertificate_row⟩

/-- The unified CPU family has a full active native certificate with public lookup matching. -/
theorem cached_unified_certificate_satisfiable :
    ∃ entry : UnifiedLogicalRowCertificate (NativePublicSetup.rows Airbender.NonVacuous.UnifiedBoot.initial CPUWitnesses.Unified.Fixture.program),
      entry.row = (⟨.machine, Airbender.NonVacuous.UnifiedBoot.assignment⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) :=
  ⟨CPUWitnesses.Unified.Fixture.rowCertificate, CPUWitnesses.Unified.Fixture.rowCertificate_row⟩

end Airbender.Compiler
