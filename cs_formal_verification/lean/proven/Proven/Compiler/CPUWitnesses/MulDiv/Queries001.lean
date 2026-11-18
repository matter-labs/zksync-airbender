module
public import Proven.Compiler.CPUWitnesses.Common
public import Proven.KernelRfl

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.MulDiv
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The actual resolved native primitive operand. -/
noncomputable def operand8 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 25)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields8 (logical : Nat → F) : List F := [(Import.expression (.Var 17)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand9 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 20)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 0)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 18))], ⟨⟨0, by decide⟩⟩⟩, 2⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields9 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 18]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 65])])).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand10 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 21)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 1)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 18))], ⟨⟨133099247, by decide⟩⟩⟩, 3⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields10 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 3]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 19]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 65])])).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand11 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 20)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 5)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 19))], ⟨⟨1744830467, by decide⟩⟩⟩, 4⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields11 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1744830467, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 22]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 66])])).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand12 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 21)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 6)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 19))], ⟨⟨133099247, by decide⟩⟩⟩, 5⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields12 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 3]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 23]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 66])])).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand13 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 20)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 10)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 20))], ⟨⟨1476395013, by decide⟩⟩⟩, 6⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields13 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 30]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 67])])).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand14 : NativeLookups.Operand := ⟨.column (.BaseLayerMemory 17), .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 18))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 19))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 4))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 9))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 14))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 0))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 1))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 2)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 3)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 4)), (⟨⟨134217711, by decide⟩⟩, (.BaseLayerWitness 5))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨268435358, by decide⟩⟩⟩], 18446744073709551615⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields14 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 0])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 1])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 5])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 6])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 7])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 8])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 9])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 10]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 11]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 12]), (.Product #[.Constant ⟨⟨134217711, by decide⟩⟩, .Var 13])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨268435358, by decide⟩⟩)])).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand15 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 7)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 8))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 6))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨268435454, by decide⟩⟩⟩], 0⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields15 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 24]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 25])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 32])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨268435454, by decide⟩⟩)])).eval (Verification.environment logical)]

end Airbender.Compiler.CPUWitnesses.MulDiv
