module
public import Proven.Compiler.CPUWitnesses.Common
public import Proven.KernelRfl

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.SubwordMemory
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The actual resolved native primitive operand. -/
noncomputable def operand0 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 8)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields0 (logical : Nat → F) : List F := [(Import.expression (.Var 40)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand1 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 25)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields1 (logical : Nat → F) : List F := [(Import.expression (.Var 13)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand2 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 26)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields2 (logical : Nat → F) : List F := [(Import.expression (.Var 14)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand3 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 27)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields3 (logical : Nat → F) : List F := [(Import.expression (.Var 15)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand4 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 28)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields4 (logical : Nat → F) : List F := [(Import.expression (.Var 16)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand5 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 23)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 0)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 11))], ⟨⟨0, by decide⟩⟩⟩, 2⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields5 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 17]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 62])])).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand6 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 24)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 1)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 11))], ⟨⟨133099247, by decide⟩⟩⟩, 3⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields6 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 3]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 18]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 62])])).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand7 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 23)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 5)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 12))], ⟨⟨1744830467, by decide⟩⟩⟩, 4⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields7 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1744830467, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 23]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 63])])).eval (Verification.environment logical)]

end Airbender.Compiler.CPUWitnesses.SubwordMemory
