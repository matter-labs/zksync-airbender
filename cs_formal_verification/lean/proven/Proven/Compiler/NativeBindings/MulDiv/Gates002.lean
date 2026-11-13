module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.MulDiv
public import Proven.GKRProtocol.CleanArithmeticNative.MulDivCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.MulDiv
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 32. -/
theorem gate32 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate32.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate32.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨32, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate32 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[42]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨42, by decide⟩))

/-- The actual native sparse relation supplies gate 33. -/
theorem gate33 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate33.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate33.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨33, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate33 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[43]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨43, by decide⟩))

/-- The actual native sparse relation supplies gate 34. -/
theorem gate34 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate34.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate34.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨34, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate34 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[44]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨44, by decide⟩))

/-- The actual native sparse relation supplies gate 35. -/
theorem gate35 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate35.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate35.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨35, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate35 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[45]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨45, by decide⟩))

/-- The actual native sparse relation supplies gate 36. -/
theorem gate36 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate36.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate36.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨36, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate36 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[46]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨46, by decide⟩))

/-- The actual native sparse relation supplies gate 37. -/
theorem gate37 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate37.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate37.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨37, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate37 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[47]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨47, by decide⟩))

/-- The actual native sparse relation supplies gate 38. -/
theorem gate38 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate38.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate38.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨38, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate38 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[48]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨48, by decide⟩))

/-- The actual native sparse relation supplies gate 39. -/
theorem gate39 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate39.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate39.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨39, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate39 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[49]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨49, by decide⟩))

/-- The actual native sparse relation supplies gate 40. -/
theorem gate40 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate40.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate40.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨40, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate40 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[50]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨50, by decide⟩))

/-- The actual native sparse relation supplies gate 41. -/
theorem gate41 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate41.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate41.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨41, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate41 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[51]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨51, by decide⟩))

/-- The actual native sparse relation supplies gate 42. -/
theorem gate42 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate42.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate42.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨42, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate42 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨0, by decide⟩))

/-- The actual native sparse relation supplies gate 43. -/
theorem gate43 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate43.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate43.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨43, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate43 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[14]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨14, by decide⟩))

/-- The actual native sparse relation supplies gate 44. -/
theorem gate44 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate44.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate44.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨44, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate44 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[15]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨15, by decide⟩))

/-- The actual native sparse relation supplies gate 45. -/
theorem gate45 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate45.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate45.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨45, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate45 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[16]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨16, by decide⟩))

/-- The actual native sparse relation supplies gate 46. -/
theorem gate46 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate46.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate46.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨46, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate46 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[17]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨17, by decide⟩))

/-- The actual native sparse relation supplies gate 47. -/
theorem gate47 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate47.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate47.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨47, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate47 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[18]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨18, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates002 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate32, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate33, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate34, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate35, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate36, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate37, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate38, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate39, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate40, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate41, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate42, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate43, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate44, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate45, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate46, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate47], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 :=
  (cons_holds (gate32 physical accepted) (cons_holds (gate33 physical accepted) (cons_holds (gate34 physical accepted) (cons_holds (gate35 physical accepted) (cons_holds (gate36 physical accepted) (cons_holds (gate37 physical accepted) (cons_holds (gate38 physical accepted) (cons_holds (gate39 physical accepted) (cons_holds (gate40 physical accepted) (cons_holds (gate41 physical accepted) (cons_holds (gate42 physical accepted) (cons_holds (gate43 physical accepted) (cons_holds (gate44 physical accepted) (cons_holds (gate45 physical accepted) (cons_holds (gate46 physical accepted) (cons_holds (gate47 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.MulDiv
