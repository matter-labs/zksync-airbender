module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.Bigint
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.Bigint
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 80. -/
theorem gate80 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate80.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate80.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨80, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate80 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[119]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨119, by decide⟩))

/-- The actual native sparse relation supplies gate 81. -/
theorem gate81 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate81.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate81.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨81, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate81 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[120]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨120, by decide⟩))

/-- The actual native sparse relation supplies gate 82. -/
theorem gate82 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate82.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate82.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨82, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate82 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[121]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨121, by decide⟩))

/-- The actual native sparse relation supplies gate 83. -/
theorem gate83 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate83.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate83.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨83, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate83 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[122]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨122, by decide⟩))

/-- The actual native sparse relation supplies gate 84. -/
theorem gate84 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate84.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate84.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨84, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate84 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[123]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨123, by decide⟩))

/-- The actual native sparse relation supplies gate 85. -/
theorem gate85 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate85.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate85.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨85, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate85 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[124]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨124, by decide⟩))

/-- The actual native sparse relation supplies gate 86. -/
theorem gate86 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate86.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate86.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨86, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate86 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[125]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨125, by decide⟩))

/-- The actual native sparse relation supplies gate 87. -/
theorem gate87 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate87.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate87.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨87, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate87 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[126]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨126, by decide⟩))

/-- The actual native sparse relation supplies gate 88. -/
theorem gate88 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate88.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate88.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨88, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate88 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[127]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨127, by decide⟩))

/-- The actual native sparse relation supplies gate 89. -/
theorem gate89 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate89.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate89.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨89, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate89 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[128]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨128, by decide⟩))

/-- The actual native sparse relation supplies gate 90. -/
theorem gate90 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate90.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate90.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨90, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate90 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[129]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨129, by decide⟩))

/-- The actual native sparse relation supplies gate 91. -/
theorem gate91 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate91.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate91.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨91, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate91 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[130]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨130, by decide⟩))

/-- The actual native sparse relation supplies gate 92. -/
theorem gate92 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate92.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate92.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨92, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate92 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[131]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨131, by decide⟩))

/-- The actual native sparse relation supplies gate 93. -/
theorem gate93 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate93.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate93.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨93, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate93 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[132]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨132, by decide⟩))

/-- The actual native sparse relation supplies gate 94. -/
theorem gate94 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate94.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate94.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨94, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate94 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[133]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨133, by decide⟩))

/-- The actual native sparse relation supplies gate 95. -/
theorem gate95 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate95.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate95.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨95, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate95 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[134]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨134, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates005 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate80, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate81, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate82, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate83, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate84, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate85, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate86, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate87, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate88, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate89, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate90, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate91, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate92, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate93, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate94, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate95], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 :=
  (cons_holds (gate80 physical accepted) (cons_holds (gate81 physical accepted) (cons_holds (gate82 physical accepted) (cons_holds (gate83 physical accepted) (cons_holds (gate84 physical accepted) (cons_holds (gate85 physical accepted) (cons_holds (gate86 physical accepted) (cons_holds (gate87 physical accepted) (cons_holds (gate88 physical accepted) (cons_holds (gate89 physical accepted) (cons_holds (gate90 physical accepted) (cons_holds (gate91 physical accepted) (cons_holds (gate92 physical accepted) (cons_holds (gate93 physical accepted) (cons_holds (gate94 physical accepted) (cons_holds (gate95 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.Bigint
