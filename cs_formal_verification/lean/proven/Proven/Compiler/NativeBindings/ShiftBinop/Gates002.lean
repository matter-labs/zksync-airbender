module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.ShiftBinop
public import Proven.GKRProtocol.CleanArithmeticNative.ShiftBinopCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.ShiftBinop
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 32. -/
theorem gate32 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate32.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate32.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨32, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate32 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[30]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨30, by decide⟩))

/-- The actual native sparse relation supplies gate 33. -/
theorem gate33 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate33.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate33.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨33, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate33 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[31]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨31, by decide⟩))

/-- The actual native sparse relation supplies gate 34. -/
theorem gate34 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate34.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate34.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨34, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate34 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[32]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨32, by decide⟩))

/-- The actual native sparse relation supplies gate 35. -/
theorem gate35 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate35.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate35.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨35, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate35 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[33]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨33, by decide⟩))

/-- The actual native sparse relation supplies gate 36. -/
theorem gate36 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate36.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate36.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨36, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate36 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[34]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨34, by decide⟩))

/-- The actual native sparse relation supplies gate 37. -/
theorem gate37 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate37.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate37.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨37, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate37 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[35]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨35, by decide⟩))

/-- The actual native sparse relation supplies gate 38. -/
theorem gate38 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate38.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate38.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨38, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate38 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[36]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨36, by decide⟩))

/-- The actual native sparse relation supplies gate 39. -/
theorem gate39 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate39.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate39.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨39, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate39 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[37]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨37, by decide⟩))

/-- The actual native sparse relation supplies gate 40. -/
theorem gate40 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate40.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate40.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨40, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate40 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[38]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨38, by decide⟩))

/-- The actual native sparse relation supplies gate 41. -/
theorem gate41 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate41.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate41.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨41, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate41 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[39]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨39, by decide⟩))

/-- The actual native sparse relation supplies gate 42. -/
theorem gate42 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate42.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate42.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨42, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate42 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[40]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨40, by decide⟩))

/-- The actual native sparse relation supplies gate 43. -/
theorem gate43 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate43.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate43.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨43, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate43 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[41]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨41, by decide⟩))

/-- The actual native sparse relation supplies gate 44. -/
theorem gate44 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate44.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate44.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨44, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate44 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[42]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨42, by decide⟩))

/-- The actual native sparse relation supplies gate 45. -/
theorem gate45 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate45.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate45.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨45, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate45 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[43]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨43, by decide⟩))

/-- The actual native sparse relation supplies gate 46. -/
theorem gate46 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate46.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate46.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨46, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate46 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[44]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨44, by decide⟩))

/-- The actual native sparse relation supplies gate 47. -/
theorem gate47 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate47.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate47.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨47, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate47 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[46]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨46, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates002 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate32, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate33, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate34, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate35, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate36, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate37, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate38, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate39, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate40, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate41, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate42, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate43, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate44, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate45, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate46, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate47], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 :=
  (cons_holds (gate32 physical accepted) (cons_holds (gate33 physical accepted) (cons_holds (gate34 physical accepted) (cons_holds (gate35 physical accepted) (cons_holds (gate36 physical accepted) (cons_holds (gate37 physical accepted) (cons_holds (gate38 physical accepted) (cons_holds (gate39 physical accepted) (cons_holds (gate40 physical accepted) (cons_holds (gate41 physical accepted) (cons_holds (gate42 physical accepted) (cons_holds (gate43 physical accepted) (cons_holds (gate44 physical accepted) (cons_holds (gate45 physical accepted) (cons_holds (gate46 physical accepted) (cons_holds (gate47 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.ShiftBinop
