module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.Unified
public import Proven.GKRProtocol.CleanArithmeticNative.UnifiedCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.Unified
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 96. -/
theorem gate96 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate96.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate96.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨96, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate96 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[107]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨107, by decide⟩))

/-- The actual native sparse relation supplies gate 97. -/
theorem gate97 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate97.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate97.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨97, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate97 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[108]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨108, by decide⟩))

/-- The actual native sparse relation supplies gate 98. -/
theorem gate98 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate98.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate98.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨98, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate98 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[109]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨109, by decide⟩))

/-- The actual native sparse relation supplies gate 99. -/
theorem gate99 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate99.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate99.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨99, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate99 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[110]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨110, by decide⟩))

/-- The actual native sparse relation supplies gate 100. -/
theorem gate100 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate100.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate100.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨100, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate100 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[111]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨111, by decide⟩))

/-- The actual native sparse relation supplies gate 101. -/
theorem gate101 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate101.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate101.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨101, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate101 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[112]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨112, by decide⟩))

/-- The actual native sparse relation supplies gate 102. -/
theorem gate102 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate102.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate102.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨102, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate102 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[113]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨113, by decide⟩))

/-- The actual native sparse relation supplies gate 103. -/
theorem gate103 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate103.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate103.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨103, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate103 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[114]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨114, by decide⟩))

/-- The actual native sparse relation supplies gate 104. -/
theorem gate104 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate104.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate104.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨104, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate104 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[115]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨115, by decide⟩))

/-- The actual native sparse relation supplies gate 105. -/
theorem gate105 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate105.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate105.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨105, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate105 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[116]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨116, by decide⟩))

/-- The actual native sparse relation supplies gate 106. -/
theorem gate106 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate106.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate106.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨106, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate106 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[117]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨117, by decide⟩))

/-- The actual native sparse relation supplies gate 107. -/
theorem gate107 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate107.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate107.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨107, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate107 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[118]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨118, by decide⟩))

/-- The actual native sparse relation supplies gate 108. -/
theorem gate108 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate108.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate108.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨108, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate108 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[119]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨119, by decide⟩))

/-- The actual native sparse relation supplies gate 109. -/
theorem gate109 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate109.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate109.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨109, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate109 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[120]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨120, by decide⟩))

/-- The actual native sparse relation supplies gate 110. -/
theorem gate110 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate110.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate110.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨110, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate110 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[121]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨121, by decide⟩))

/-- The actual native sparse relation supplies gate 111. -/
theorem gate111 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate111.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate111.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨111, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate111 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[122]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨122, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates006 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate96, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate97, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate98, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate99, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate100, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate101, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate102, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate103, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate104, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate105, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate106, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate107, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate108, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate109, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate110, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate111], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 :=
  (cons_holds (gate96 physical accepted) (cons_holds (gate97 physical accepted) (cons_holds (gate98 physical accepted) (cons_holds (gate99 physical accepted) (cons_holds (gate100 physical accepted) (cons_holds (gate101 physical accepted) (cons_holds (gate102 physical accepted) (cons_holds (gate103 physical accepted) (cons_holds (gate104 physical accepted) (cons_holds (gate105 physical accepted) (cons_holds (gate106 physical accepted) (cons_holds (gate107 physical accepted) (cons_holds (gate108 physical accepted) (cons_holds (gate109 physical accepted) (cons_holds (gate110 physical accepted) (cons_holds (gate111 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.Unified
