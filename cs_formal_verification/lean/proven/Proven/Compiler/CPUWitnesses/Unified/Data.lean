module
public import Proven.Compiler.CPUWitnesses.Unified.Queries000
public import Proven.Compiler.CPUWitnesses.Unified.Queries001
public import Proven.Compiler.CPUWitnesses.Unified.Queries002
public import Proven.Compiler.CPUWitnesses.Unified.Queries003

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.Unified
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The resolved operands retain the exact native selector order. -/
noncomputable def operands (group : Fin 3) : List NativeLookups.Operand :=
  ([[operand18, operand22, operand23, operand24, operand25, operand26], [operand0, operand1, operand2, operand3, operand4, operand5, operand6, operand7, operand8, operand9, operand10, operand19, operand20], [operand11, operand12, operand13, operand14, operand15, operand16, operand17, operand21]] : List (List NativeLookups.Operand)).get group

/-- The complete logical tuples retain each native occurrence. -/
noncomputable def tuples (logical : Nat → F) (group : Fin 3) : List (List F) :=
  ([[sourceFields18 logical, sourceFields22 logical, sourceFields23 logical, sourceFields24 logical, sourceFields25 logical, sourceFields26 logical], [sourceFields0 logical, sourceFields1 logical, sourceFields2 logical, sourceFields3 logical, sourceFields4 logical, sourceFields5 logical, sourceFields6 logical, sourceFields7 logical, sourceFields8 logical, sourceFields9 logical, sourceFields10 logical, sourceFields19 logical, sourceFields20 logical], [sourceFields11 logical, sourceFields12 logical, sourceFields13 logical, sourceFields14 logical, sourceFields15 logical, sourceFields16 logical, sourceFields17 logical, sourceFields21 logical]] : List (List (List F))).get group

/-- The canonical check compares each logical tuple with its actual public native row. -/
noncomputable def canonicalCheck (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (logical : Nat → F) : Bool := CPUWitnesses.canonicalCheck (.unified) initial program (tuples logical)

end Airbender.Compiler.CPUWitnesses.Unified
