module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.JumpBranch
public import Proven.GKRProtocol.CleanArithmeticNative.JumpBranchCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.JumpBranch
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 32. -/
theorem gate32 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.JumpBranch.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate32.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate32.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gatesChecked _ (List.get_mem _ ⟨32, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate32 (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[39]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨39, by decide⟩))

/-- The actual native sparse relation supplies gate 33. -/
theorem gate33 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.JumpBranch.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate33.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate33.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gatesChecked _ (List.get_mem _ ⟨33, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate33 (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[40]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨40, by decide⟩))

/-- The actual native sparse relation supplies gate 34. -/
theorem gate34 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.JumpBranch.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate34.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate34.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gatesChecked _ (List.get_mem _ ⟨34, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate34 (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[41]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨41, by decide⟩))

/-- The actual native sparse relation supplies gate 35. -/
theorem gate35 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.JumpBranch.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate35.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate35.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gatesChecked _ (List.get_mem _ ⟨35, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate35 (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨0, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates002 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.JumpBranch.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate32, Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate33, Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate34, Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate35], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0 :=
  (cons_holds (gate32 physical accepted) (cons_holds (gate33 physical accepted) (cons_holds (gate34 physical accepted) (cons_holds (gate35 physical accepted) (by intro gate member; cases member)))))
end Airbender.Compiler.NativeBindings.JumpBranch
