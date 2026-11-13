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

/-- The actual native sparse relation supplies gate 64. -/
theorem gate64 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate64.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate64.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨64, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate64 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[103]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨103, by decide⟩))

/-- The actual native sparse relation supplies gate 65. -/
theorem gate65 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate65.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate65.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨65, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate65 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[104]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨104, by decide⟩))

/-- The actual native sparse relation supplies gate 66. -/
theorem gate66 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate66.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate66.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨66, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate66 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[105]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨105, by decide⟩))

/-- The actual native sparse relation supplies gate 67. -/
theorem gate67 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate67.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate67.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨67, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate67 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[106]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨106, by decide⟩))

/-- The actual native sparse relation supplies gate 68. -/
theorem gate68 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate68.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate68.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨68, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate68 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[107]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨107, by decide⟩))

/-- The actual native sparse relation supplies gate 69. -/
theorem gate69 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate69.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate69.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨69, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate69 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[108]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨108, by decide⟩))

/-- The actual native sparse relation supplies gate 70. -/
theorem gate70 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate70.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate70.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨70, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate70 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[109]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨109, by decide⟩))

/-- The actual native sparse relation supplies gate 71. -/
theorem gate71 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate71.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate71.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨71, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate71 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[110]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨110, by decide⟩))

/-- The actual native sparse relation supplies gate 72. -/
theorem gate72 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate72.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate72.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨72, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate72 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[111]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨111, by decide⟩))

/-- The actual native sparse relation supplies gate 73. -/
theorem gate73 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate73.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate73.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨73, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate73 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[112]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨112, by decide⟩))

/-- The actual native sparse relation supplies gate 74. -/
theorem gate74 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate74.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate74.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨74, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate74 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[113]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨113, by decide⟩))

/-- The actual native sparse relation supplies gate 75. -/
theorem gate75 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate75.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate75.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨75, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate75 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[114]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨114, by decide⟩))

/-- The actual native sparse relation supplies gate 76. -/
theorem gate76 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate76.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate76.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨76, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate76 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[115]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨115, by decide⟩))

/-- The actual native sparse relation supplies gate 77. -/
theorem gate77 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate77.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate77.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨77, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate77 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[116]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨116, by decide⟩))

/-- The actual native sparse relation supplies gate 78. -/
theorem gate78 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate78.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate78.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨78, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate78 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[117]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨117, by decide⟩))

/-- The actual native sparse relation supplies gate 79. -/
theorem gate79 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate79.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate79.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨79, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate79 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[118]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨118, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates004 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate64, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate65, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate66, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate67, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate68, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate69, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate70, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate71, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate72, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate73, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate74, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate75, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate76, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate77, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate78, Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate79], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0 :=
  (cons_holds (gate64 physical accepted) (cons_holds (gate65 physical accepted) (cons_holds (gate66 physical accepted) (cons_holds (gate67 physical accepted) (cons_holds (gate68 physical accepted) (cons_holds (gate69 physical accepted) (cons_holds (gate70 physical accepted) (cons_holds (gate71 physical accepted) (cons_holds (gate72 physical accepted) (cons_holds (gate73 physical accepted) (cons_holds (gate74 physical accepted) (cons_holds (gate75 physical accepted) (cons_holds (gate76 physical accepted) (cons_holds (gate77 physical accepted) (cons_holds (gate78 physical accepted) (cons_holds (gate79 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.Bigint
