module
public import Proven.Compiler.CPUWitnesses.Common
public import Proven.KernelRfl

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.WordMemory
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The actual resolved native primitive operand. -/
noncomputable def operand8 : NativeLookups.Operand := ⟨.column (.BaseLayerMemory 20), .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 21))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 22))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 4))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 0))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 1))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 2))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 3))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 9))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨268435358, by decide⟩⟩⟩], 18446744073709551615⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields8 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 0])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 1])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 5])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 6])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 7])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 8])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 9])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 10])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨268435358, by decide⟩⟩)])).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand9 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 26)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields9 (logical : Nat → F) : List F := [(Import.expression (.Var 12)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand10 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 24)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 13)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 7))], ⟨⟨133099247, by decide⟩⟩⟩, 7⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields10 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 3]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 28]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 48])])).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand11 : NativeLookups.Operand := ⟨.one, .address (.InnerLayer 1 7)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields11 (logical : Nat → F) : List F := [(Import.expression (.Var 36)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand12 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.InnerLayer 2 0))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.InnerLayer 2 1))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.InnerLayer 2 2))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.InnerLayer 2 3))], ⟨⟨0, by decide⟩⟩⟩], 0⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields12 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 39])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 41])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 43])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 45])])).eval (Verification.environment logical)]

end Airbender.Compiler.CPUWitnesses.WordMemory
