module
public import Proven.Compiler.CPUWitnesses.Common
public import Proven.KernelRfl

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.Unified
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The actual resolved native primitive operand. -/
noncomputable def operand8 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 17)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields8 (logical : Nat → F) : List F := [(Import.expression (.Var 44)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand9 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 18)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields9 (logical : Nat → F) : List F := [(Import.expression (.Var 45)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand10 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 26)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields10 (logical : Nat → F) : List F := [(Import.expression (.Var 30)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand11 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 28)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields11 (logical : Nat → F) : List F := [(Import.expression (.Var 32)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand12 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 29)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields12 (logical : Nat → F) : List F := [(Import.expression (.Var 33)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand13 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 24)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 0)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 52))], ⟨⟨0, by decide⟩⟩⟩, 2⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields13 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 34]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 123])])).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand14 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 25)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 1)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 52))], ⟨⟨133099247, by decide⟩⟩⟩, 3⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields14 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 3]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 35]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 123])])).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand15 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 24)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 5)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 53))], ⟨⟨1744830467, by decide⟩⟩⟩, 4⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields15 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1744830467, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 40]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 124])])).eval (Verification.environment logical)]

end Airbender.Compiler.CPUWitnesses.Unified
