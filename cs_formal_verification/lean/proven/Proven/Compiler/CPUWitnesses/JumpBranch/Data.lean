module
public import Proven.Compiler.CPUWitnesses.JumpBranch.Queries000
public import Proven.Compiler.CPUWitnesses.JumpBranch.Queries001
public import Proven.Compiler.CPUWitnesses.JumpBranch.Queries002

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.JumpBranch
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The resolved operands retain the exact native selector order. -/
noncomputable def operands (group : Fin 3) : List NativeLookups.Operand :=
  ([[operand10, operand11, operand12, operand13, operand14], [operand0, operand1, operand2, operand15], [operand3, operand4, operand5, operand6, operand7, operand8, operand9, operand16]] : List (List NativeLookups.Operand)).get group

/-- The complete logical tuples retain each native occurrence. -/
noncomputable def tuples (logical : Nat → F) (group : Fin 3) : List (List F) :=
  ([[sourceFields10 logical, sourceFields11 logical, sourceFields12 logical, sourceFields13 logical, sourceFields14 logical], [sourceFields0 logical, sourceFields1 logical, sourceFields2 logical, sourceFields15 logical], [sourceFields3 logical, sourceFields4 logical, sourceFields5 logical, sourceFields6 logical, sourceFields7 logical, sourceFields8 logical, sourceFields9 logical, sourceFields16 logical]] : List (List (List F))).get group

/-- The canonical check compares each logical tuple with its actual public native row. -/
noncomputable def canonicalCheck (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (logical : Nat → F) : Bool := CPUWitnesses.canonicalCheck (.pooled .jumpBranchSlt) initial program (tuples logical)

end Airbender.Compiler.CPUWitnesses.JumpBranch
