module
public import Proven.Compiler.CPUWitnesses.WordMemory.Queries000
public import Proven.Compiler.CPUWitnesses.WordMemory.Queries001

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.WordMemory
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The resolved operands retain the exact native selector order. -/
noncomputable def operands (group : Fin 3) : List NativeLookups.Operand :=
  ([[operand8, operand12], [operand0, operand9, operand11], [operand1, operand2, operand3, operand4, operand5, operand6, operand7, operand10]] : List (List NativeLookups.Operand)).get group

/-- The complete logical tuples retain each native occurrence. -/
noncomputable def tuples (logical : Nat → F) (group : Fin 3) : List (List F) :=
  ([[sourceFields8 logical, sourceFields12 logical], [sourceFields0 logical, sourceFields9 logical, sourceFields11 logical], [sourceFields1 logical, sourceFields2 logical, sourceFields3 logical, sourceFields4 logical, sourceFields5 logical, sourceFields6 logical, sourceFields7 logical, sourceFields10 logical]] : List (List (List F))).get group

/-- The canonical check compares each logical tuple with its actual public native row. -/
noncomputable def canonicalCheck (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (logical : Nat → F) : Bool := CPUWitnesses.canonicalCheck (.pooled .wordMemory) initial program (tuples logical)

end Airbender.Compiler.CPUWitnesses.WordMemory
