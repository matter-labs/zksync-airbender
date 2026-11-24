module
public import Proven.Compiler.CPUWitnesses.Common
public import Proven.KernelRfl

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.MulDiv
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The actual resolved native primitive operand. -/
noncomputable def operand0 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 15)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields0 (logical : Nat → F) : List F := [(Import.expression (.Var 28)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand1 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 16)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields1 (logical : Nat → F) : List F := [(Import.expression (.Var 29)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand2 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 11)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields2 (logical : Nat → F) : List F := [(Import.expression (.Var 37)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand3 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 12)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields3 (logical : Nat → F) : List F := [(Import.expression (.Var 38)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand4 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 13)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields4 (logical : Nat → F) : List F := [(Import.expression (.Var 39)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand5 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 14)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields5 (logical : Nat → F) : List F := [(Import.expression (.Var 40)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand6 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 22)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields6 (logical : Nat → F) : List F := [(Import.expression (.Var 14)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand7 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 24)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields7 (logical : Nat → F) : List F := [(Import.expression (.Var 16)).eval (Verification.environment logical)]

end Airbender.Compiler.CPUWitnesses.MulDiv
