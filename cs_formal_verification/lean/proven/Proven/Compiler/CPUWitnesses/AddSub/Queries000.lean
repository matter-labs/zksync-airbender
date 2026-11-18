module
public import Proven.Compiler.CPUWitnesses.Common
public import Proven.KernelRfl

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.AddSub
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The actual resolved native primitive operand. -/
noncomputable def operand0 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 11)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields0 (logical : Nat → F) : List F := [(Import.expression (.Var 37)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand1 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 12)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields1 (logical : Nat → F) : List F := [(Import.expression (.Var 38)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand2 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 15)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields2 (logical : Nat → F) : List F := [(Import.expression (.Var 33)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand3 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 16)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields3 (logical : Nat → F) : List F := [(Import.expression (.Var 34)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand4 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 22)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields4 (logical : Nat → F) : List F := [(Import.expression (.Var 19)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand5 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 24)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields5 (logical : Nat → F) : List F := [(Import.expression (.Var 21)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand6 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 25)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields6 (logical : Nat → F) : List F := [(Import.expression (.Var 22)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand7 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 20)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 0)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 16))], ⟨⟨0, by decide⟩⟩⟩, 2⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields7 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 23]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 42])])).eval (Verification.environment logical)]

end Airbender.Compiler.CPUWitnesses.AddSub
