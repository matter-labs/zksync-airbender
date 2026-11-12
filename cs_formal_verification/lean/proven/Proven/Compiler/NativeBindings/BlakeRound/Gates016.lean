module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.BlakeRound
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.BlakeRound
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 256. -/
theorem gate256 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate256.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate256.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨256, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate256 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[353]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨353, by decide⟩))

/-- The actual native sparse relation supplies gate 257. -/
theorem gate257 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate257.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate257.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨257, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate257 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[354]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨354, by decide⟩))

/-- The actual native sparse relation supplies gate 258. -/
theorem gate258 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate258.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate258.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨258, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate258 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[355]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨355, by decide⟩))

/-- The actual native sparse relation supplies gate 259. -/
theorem gate259 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate259.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate259.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨259, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate259 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[356]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨356, by decide⟩))

/-- The actual native sparse relation supplies gate 260. -/
theorem gate260 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate260.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate260.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨260, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate260 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[357]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨357, by decide⟩))

/-- The actual native sparse relation supplies gate 261. -/
theorem gate261 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate261.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate261.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨261, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate261 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[358]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨358, by decide⟩))

/-- The actual native sparse relation supplies gate 262. -/
theorem gate262 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate262.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate262.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨262, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate262 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[359]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨359, by decide⟩))

/-- The actual native sparse relation supplies gate 263. -/
theorem gate263 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate263.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate263.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨263, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate263 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[360]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨360, by decide⟩))

/-- The actual native sparse relation supplies gate 264. -/
theorem gate264 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate264.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate264.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨264, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate264 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[361]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨361, by decide⟩))

/-- The actual native sparse relation supplies gate 265. -/
theorem gate265 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate265.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate265.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨265, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate265 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[362]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨362, by decide⟩))

/-- The actual native sparse relation supplies gate 266. -/
theorem gate266 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate266.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate266.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨266, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate266 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[363]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨363, by decide⟩))

/-- The actual native sparse relation supplies gate 267. -/
theorem gate267 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate267.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate267.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨267, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate267 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[364]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨364, by decide⟩))

/-- The actual native sparse relation supplies gate 268. -/
theorem gate268 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate268.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate268.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨268, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate268 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[365]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨365, by decide⟩))

/-- The actual native sparse relation supplies gate 269. -/
theorem gate269 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate269.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate269.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨269, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate269 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[366]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨366, by decide⟩))

/-- The actual native sparse relation supplies gate 270. -/
theorem gate270 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate270.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate270.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨270, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate270 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[367]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨367, by decide⟩))

/-- The actual native sparse relation supplies gate 271. -/
theorem gate271 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate271.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate271.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨271, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate271 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[368]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨368, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates016 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate256, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate257, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate258, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate259, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate260, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate261, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate262, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate263, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate264, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate265, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate266, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate267, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate268, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate269, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate270, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate271], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate256 physical accepted) (cons_holds (gate257 physical accepted) (cons_holds (gate258 physical accepted) (cons_holds (gate259 physical accepted) (cons_holds (gate260 physical accepted) (cons_holds (gate261 physical accepted) (cons_holds (gate262 physical accepted) (cons_holds (gate263 physical accepted) (cons_holds (gate264 physical accepted) (cons_holds (gate265 physical accepted) (cons_holds (gate266 physical accepted) (cons_holds (gate267 physical accepted) (cons_holds (gate268 physical accepted) (cons_holds (gate269 physical accepted) (cons_holds (gate270 physical accepted) (cons_holds (gate271 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
