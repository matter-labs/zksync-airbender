module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.AddSub
public import Proven.GKRProtocol.CleanArithmeticNative.AddSubCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.AddSub
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 32. -/
theorem gate32 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.AddSub.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate32.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate32.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨32, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate32 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[38]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨38, by decide⟩))

/-- The actual native sparse relation supplies gate 33. -/
theorem gate33 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.AddSub.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate33.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate33.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨33, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate33 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[39]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨39, by decide⟩))

/-- The actual native sparse relation supplies gate 34. -/
theorem gate34 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.AddSub.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate34.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate34.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨34, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate34 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[40]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨40, by decide⟩))

/-- The actual native sparse relation supplies gate 35. -/
theorem gate35 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.AddSub.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate35.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate35.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨35, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate35 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[41]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨41, by decide⟩))

/-- The actual native sparse relation supplies gate 36. -/
theorem gate36 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.AddSub.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate36.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate36.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨36, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate36 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[42]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨42, by decide⟩))

/-- The actual native sparse relation supplies gate 37. -/
theorem gate37 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.AddSub.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate37.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate37.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨37, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate37 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[43]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨43, by decide⟩))

/-- The actual native sparse relation supplies gate 38. -/
theorem gate38 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.AddSub.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate38.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate38.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨38, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate38 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[44]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨44, by decide⟩))

/-- The actual native sparse relation supplies gate 39. -/
theorem gate39 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.AddSub.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate39.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate39.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨39, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate39 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨0, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates002 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.AddSub.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate32, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate33, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate34, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate35, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate36, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate37, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate38, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate39], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0 :=
  (cons_holds (gate32 physical accepted) (cons_holds (gate33 physical accepted) (cons_holds (gate34 physical accepted) (cons_holds (gate35 physical accepted) (cons_holds (gate36 physical accepted) (cons_holds (gate37 physical accepted) (cons_holds (gate38 physical accepted) (cons_holds (gate39 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.AddSub
