module
public import Proven.Compiler.CPUWitnesses.Common
public import Proven.KernelRfl

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.AddSub
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The actual resolved native primitive operand. -/
noncomputable def operand8 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 21)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 1)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 16))], ⟨⟨133099247, by decide⟩⟩⟩, 3⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields8 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 3]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 24]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 42])])).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand9 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 20)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 5)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 17))], ⟨⟨1744830467, by decide⟩⟩⟩, 4⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields9 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1744830467, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 27]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 43])])).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand10 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 21)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 6)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 17))], ⟨⟨133099247, by decide⟩⟩⟩, 5⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields10 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 3]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 28]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 43])])).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand11 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 20)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 10)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 18))], ⟨⟨1476395013, by decide⟩⟩⟩, 6⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields11 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 35]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 44])])).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand12 : NativeLookups.Operand := ⟨.column (.BaseLayerMemory 17), .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 18))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 19))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 4))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 9))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 14))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 0))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 1))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 2)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 3)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 4)), (⟨⟨134217711, by decide⟩⟩, (.BaseLayerWitness 5)), (⟨⟨268435422, by decide⟩⟩, (.BaseLayerWitness 6)), (⟨⟨536870844, by decide⟩⟩, (.BaseLayerWitness 7)), (⟨⟨1073741688, by decide⟩⟩, (.BaseLayerWitness 8)), (⟨⟨134217455, by decide⟩⟩, (.BaseLayerWitness 9)), (⟨⟨268434910, by decide⟩⟩, (.BaseLayerWitness 10))], ⟨⟨0, by decide⟩⟩⟩], 18446744073709551615⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields12 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 0])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 1])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 5])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 6])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 7])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 8])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 9])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 10]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 11]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 12]), (.Product #[.Constant ⟨⟨134217711, by decide⟩⟩, .Var 13]), (.Product #[.Constant ⟨⟨268435422, by decide⟩⟩, .Var 14]), (.Product #[.Constant ⟨⟨536870844, by decide⟩⟩, .Var 15]), (.Product #[.Constant ⟨⟨1073741688, by decide⟩⟩, .Var 16]), (.Product #[.Constant ⟨⟨134217455, by decide⟩⟩, .Var 17]), (.Product #[.Constant ⟨⟨268434910, by decide⟩⟩, .Var 18])])).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand13 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerMemory 23)⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields13 (logical : Nat → F) : List F := [(Import.expression (.Var 20)).eval (Verification.environment logical)]

/-- The actual resolved native primitive operand. -/
noncomputable def operand14 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 21)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 11)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 18))], ⟨⟨133099247, by decide⟩⟩⟩, 7⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields14 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 3]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 36]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 44])])).eval (Verification.environment logical)]

end Airbender.Compiler.CPUWitnesses.AddSub
