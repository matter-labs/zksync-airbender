module
public import Proven.Compiler.CPUWitnesses.Common
public import Proven.KernelRfl

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.Unified
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The actual resolved native primitive operand. -/
noncomputable def operand0 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 44)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields0 (logical : Nat → F) : List F := [(Import.expression (.Var 74)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand1 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 45)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields1 (logical : Nat → F) : List F := [(Import.expression (.Var 75)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand2 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 19)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields2 (logical : Nat → F) : List F := [(Import.expression (.Var 50)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand3 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 20)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields3 (logical : Nat → F) : List F := [(Import.expression (.Var 51)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand4 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 23)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields4 (logical : Nat → F) : List F := [(Import.expression (.Var 1)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand5 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 34)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields5 (logical : Nat → F) : List F := [(Import.expression (.Var 64)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand6 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 10)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields6 (logical : Nat → F) : List F := [(Import.expression (.Var 38)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand7 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 11)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields7 (logical : Nat → F) : List F := [(Import.expression (.Var 39)).eval (Verification.environment logical)]

end Airbender.Compiler.CPUWitnesses.Unified
