module
public import Proven.Compiler.CPUWitnesses.Common
public import Proven.KernelRfl

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.JumpBranch
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- The actual resolved native primitive operand. -/
noncomputable def operand16 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 21)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 11)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 25))], ⟨⟨133099247, by decide⟩⟩⟩, 7⟩⟩

/-- Its affine fields use the captured logical columns. -/
noncomputable def sourceFields16 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 3]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 33]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 51])])).eval (Verification.environment logical)]

end Airbender.Compiler.CPUWitnesses.JumpBranch
